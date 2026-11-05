import Base
import ../model/kernel.bend as K
import ./catchup_gate.bend as C
import ./quorum_gates.bend as Q
import ./reachable_safety.bend as S
import ./reachable_execution.bend as E

# Python's Validator is the state-bearing consensus object. The existing
# agreement core stores only its safety-relevant Votes and finality witnesses.
def ValidatorState() -> Data:
  E.ProtocolState

def genesis() -> ValidatorState():
  E.genesis()

# A maintained Bend Vote starts from one concrete scanned Block target.
# block_frontier, quorums, and historical_q3 are computed by the Bend kernel;
# callers cannot supply independent Q2 or Q3 paths.
type Vote is Data:
  Vote{time: Nat, signer: Nat, ranked: K.ScannedTarget,
    q3_below_q2:
      C.Prefix(K.scanned_path(K.historical_q3(ranked)),
        K.scanned_path(K.Quorums.q2(ranked,K.quorums(ranked))))}

def Vote.time(+vote: Vote) -> Nat:
  match vote:
    case Vote{time,_,_,_}: time

def Vote.signer(+vote: Vote) -> Nat:
  match vote:
    case Vote{_,signer,_,_}: signer

def Vote.ranked(+vote: Vote) -> K.ScannedTarget:
  match vote:
    case Vote{_,_,ranked,_}: ranked

def Vote.block(+vote: Vote) -> Nat:
  K.target(Vote.ranked(vote))

def Vote.block_frontier(+vote: Vote) -> K.ScannedTarget:
  K.block_frontier(Vote.ranked(vote))

def Vote.quorums(+vote: Vote) -> K.Quorums<Vote.ranked(vote)>:
  K.quorums(Vote.ranked(vote))

def Vote.historical_q3(+vote: Vote) -> K.ScannedTarget:
  K.historical_q3(Vote.ranked(vote))

def Vote.q3_below_q2(+vote: Vote) ->
    C.Prefix(K.scanned_path(Vote.historical_q3(vote)),
      K.scanned_path(K.Quorums.q2(Vote.ranked(vote),Vote.quorums(vote)))):
  match vote:
    case Vote{_,_,_,proof}: proof

def Vote.event(+vote: Vote) -> S.VoteEvent:
  S.VoteEvent{Vote.time(vote),Vote.signer(vote),Vote.block(vote),
    K.scanned_path(Vote.ranked(vote)),
    K.scanned_path(K.Quorums.q2(Vote.ranked(vote),Vote.quorums(vote))),
    K.scanned_path(Vote.historical_q3(vote)),Vote.q3_below_q2(vote)}

def FreshTime(+events: List<&2,S.VoteEvent>, +time: Nat) -> Data:
  match events:
    case Nil{}: Unit
    case Con{event,rest}:
      Sigma<&2,&2,Q.Le(1n+S.VoteEvent.time(event),time),_ =>
        FreshTime(rest,time)>

def DifferentVote(+event: S.VoteEvent, +signer: Nat, +block: Nat) -> Data:
  Either<&2,&2,
    {K.nat_eq(S.VoteEvent.signer(event),signer) == False{} : Bool},
    {K.nat_eq(S.VoteEvent.block(event),block) == False{} : Bool}>

def FreshBlock(+events: List<&2,S.VoteEvent>, +signer: Nat,
    +block: Nat) -> Data:
  match events:
    case Nil{}: Unit
    case Con{event,rest}:
      Sigma<&2,&2,DifferentVote(event,signer,block),_ =>
        FreshBlock(rest,signer,block)>

# These indexed steps use Python model terms but refine the established safety
# core. FreshTime and FreshBlock are protocol admission checks; they are not
# needed by the mathematical agreement lemma after admission.
type NetworkStep<-root_authority: K.Authority, -honest: List<&2,Nat>,
    -before: ValidatorState(), -after: ValidatorState()> is Data:
  Stutter{same: {after == before : ValidatorState()}}
  EmitVote{vote: Vote,
    same: {after == E.emit_state(Vote.event(vote),before) : ValidatorState()},
    fresh_time: FreshTime(E.ProtocolState.events(before),Vote.time(vote)),
    fresh_block: FreshBlock(E.ProtocolState.events(before),Vote.signer(vote),
      Vote.block(vote)),
    new_row: S.HistoryColumns(honest,Vote.event(vote),
      Vote.event(vote) <> E.ProtocolState.events(before)),
    new_column: S.HistoryTable(honest,E.ProtocolState.events(before),
      [Vote.event(vote)]),
    q3_ready: S.Q3Ready(E.ProtocolState.locks(before),Vote.event(vote))}
  AdmitFinality{lock: S.FinalityLock,
    same: {after == E.admit_state(lock,before) : ValidatorState()},
    valid: S.ValidLock<root_authority,honest,
      E.ProtocolState.events(before),lock>}
  ApplyAuthority{same: {after == before : ValidatorState()}}

def NetworkStep.to_core(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: ValidatorState(),
    +after: ValidatorState(),
    step: NetworkStep<root_authority,honest,before,after>) ->
    E.ProtocolStep<root_authority,honest,before,after>:
  match step:
    case Stutter{same}: E.Stutter{same}
    case EmitVote{vote,same,_,_,new_row,new_column,q3_ready}:
      E.EmitVote{Vote.event(vote),same,new_row,new_column,q3_ready}
    case AdmitFinality{lock,same,valid}:
      E.AdmitCertificate{lock,same,valid}
    case ApplyAuthority{same}: E.ApplyAuthority{same}

def NetworkStep.emitted_votes(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: ValidatorState(),
    +after: ValidatorState(),
    step: NetworkStep<root_authority,honest,before,after>) -> Nat:
  match step:
    case Stutter{_}: 0n
    case EmitVote{_,_,_,_,_,_,_}: 1n
    case AdmitFinality{_,_,_}: 0n
    case ApplyAuthority{_}: 0n

def NetworkStep.emitted_votes_to_core(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: ValidatorState(),
    +after: ValidatorState(),
    +step: NetworkStep<root_authority,honest,before,after>) ->
    {E.ProtocolStep.emitted_votes(root_authority,honest,before,after,
      NetworkStep.to_core(root_authority,honest,before,after,step)) ==
      NetworkStep.emitted_votes(root_authority,honest,before,after,step) : Nat}:
  match step:
    case Stutter{_}: {==}
    case EmitVote{_,_,_,_,_,_,_}: {==}
    case AdmitFinality{_,_,_}: {==}
    case ApplyAuthority{_}: {==}

def NetworkEffects(+steps: Nat, +root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: ValidatorState(),
    +after: ValidatorState()) -> Data:
  match steps:
    case 0n: {after == before : ValidatorState()}
    case 1n+steps:
      Sigma<&2,&2,ValidatorState(),middle =>
        Sigma<&2,&2,NetworkStep<root_authority,honest,before,middle>,_ =>
          NetworkEffects(steps,root_authority,honest,middle,after)>>

def NetworkEffects.emitted_votes(+steps: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +before: ValidatorState(), +after: ValidatorState(),
    effects: NetworkEffects(steps,root_authority,honest,before,after)) -> Nat:
  match steps:
    case 0n: 0n
    case 1n+steps:
      (+middle,(first,rest)) = effects
      Nat.add(NetworkStep.emitted_votes(root_authority,honest,before,middle,first),
        NetworkEffects.emitted_votes(steps,root_authority,honest,middle,after,rest))

def NetworkEffects.to_core(+steps: Nat, +root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: ValidatorState(),
    +after: ValidatorState(),
    effects: NetworkEffects(steps,root_authority,honest,before,after)) ->
    E.ActionEffects(steps,root_authority,honest,before,after):
  match steps:
    case 0n: effects
    case 1n+steps:
      (+middle,(first,rest)) = effects
      (middle,(NetworkStep.to_core(root_authority,honest,before,middle,first),
        NetworkEffects.to_core(steps,root_authority,honest,middle,after,rest)))

def NetworkEffects.emitted_votes_to_core(+steps: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +before: ValidatorState(), +after: ValidatorState(),
    +effects: NetworkEffects(steps,root_authority,honest,before,after)) ->
    {E.ActionEffects.emitted_votes(steps,root_authority,honest,before,after,
      NetworkEffects.to_core(steps,root_authority,honest,before,after,effects)) ==
      NetworkEffects.emitted_votes(steps,root_authority,honest,before,after,
        effects) : Nat}:
  match steps:
    case 0n: {==}
    case 1n+steps:
      (+middle,(+first,+rest)) = effects
      +first_same = NetworkStep.emitted_votes_to_core(root_authority,honest,
        before,middle,first)
      +same = NetworkEffects.emitted_votes_to_core(steps,root_authority,
        honest,middle,after,rest)
      +core_rest = E.ActionEffects.emitted_votes(steps,root_authority,honest,
        middle,after,NetworkEffects.to_core(steps,root_authority,honest,middle,
          after,rest))
      +network_rest = NetworkEffects.emitted_votes(steps,root_authority,honest,
        middle,after,rest)
      +first_cong = Equal.cong(Nat,Nat,
        head => Nat.add(head,core_rest),
        E.ProtocolStep.emitted_votes(root_authority,honest,before,middle,
          NetworkStep.to_core(root_authority,honest,before,middle,first)),
        NetworkStep.emitted_votes(root_authority,honest,before,middle,first),
        first_same)
      +rest_cong = Equal.cong(Nat,Nat,
        tail => Nat.add(NetworkStep.emitted_votes(root_authority,honest,
          before,middle,first),tail),
        core_rest,network_rest,same)
      C.equality_trans(Nat,
        Nat.add(E.ProtocolStep.emitted_votes(root_authority,honest,before,
          middle,NetworkStep.to_core(root_authority,honest,before,middle,first)),
          core_rest),
        Nat.add(NetworkStep.emitted_votes(root_authority,honest,before,middle,
          first),core_rest),
        Nat.add(NetworkStep.emitted_votes(root_authority,honest,before,middle,
          first),network_rest),first_cong,rest_cong)

def NetworkEffects.bound_to_core(+steps: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +before: ValidatorState(), +after: ValidatorState(),
    +effects: NetworkEffects(steps,root_authority,honest,before,after),
    +limit: Nat,
    bound: Q.Le(NetworkEffects.emitted_votes(steps,root_authority,honest,
      before,after,effects),limit)) ->
    Q.Le(E.ActionEffects.emitted_votes(steps,root_authority,honest,before,after,
      NetworkEffects.to_core(steps,root_authority,honest,before,after,effects)),
      limit):
  +same = NetworkEffects.emitted_votes_to_core(steps,root_authority,honest,
    before,after,effects)
  %Equal.sym(Nat,
    E.ActionEffects.emitted_votes(steps,root_authority,honest,before,after,
      NetworkEffects.to_core(steps,root_authority,honest,before,after,effects)),
    NetworkEffects.emitted_votes(steps,root_authority,honest,before,after,
      effects),same) : Q.Le(_,limit)
  bound

type NetworkAction<-root_authority: K.Authority, -honest: List<&2,Nat>,
    -before: ValidatorState(), -after: ValidatorState()> is Data:
  SignVote{steps: Nat,
    effects: NetworkEffects(steps,root_authority,honest,before,after),
    emission_bound: Q.Le(NetworkEffects.emitted_votes(steps,root_authority,
      honest,before,after,effects),K.emission_limit(K.SignVote{}))}
  Propose{steps: Nat,
    effects: NetworkEffects(steps,root_authority,honest,before,after),
    emission_bound: Q.Le(NetworkEffects.emitted_votes(steps,root_authority,
      honest,before,after,effects),K.emission_limit(K.Propose{}))}
  PublishVote{same: {after == before : ValidatorState()}}
  PublishProposal{same: {after == before : ValidatorState()}}
  DeliverVote{steps: Nat,
    effects: NetworkEffects(steps,root_authority,honest,before,after),
    emission_bound: Q.Le(NetworkEffects.emitted_votes(steps,root_authority,
      honest,before,after,effects),K.emission_limit(K.DeliverVote{}))}
  DeliverProposal{steps: Nat,
    effects: NetworkEffects(steps,root_authority,honest,before,after),
    emission_bound: Q.Le(NetworkEffects.emitted_votes(steps,root_authority,
      honest,before,after,effects),K.emission_limit(K.DeliverProposal{}))}
  Idle{same: {after == before : ValidatorState()}}

def NetworkAction.to_core(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: ValidatorState(),
    +after: ValidatorState(),
    action: NetworkAction<root_authority,honest,before,after>) ->
    E.PythonAction<root_authority,honest,before,after>:
  match action:
    case SignVote{+steps,+effects,bound}:
      E.SignVote{steps,NetworkEffects.to_core(steps,root_authority,honest,
        before,after,effects),NetworkEffects.bound_to_core(steps,
          root_authority,honest,before,after,effects,
          K.emission_limit(K.SignVote{}),bound)}
    case Propose{+steps,+effects,bound}:
      E.Propose{steps,NetworkEffects.to_core(steps,root_authority,honest,
        before,after,effects),NetworkEffects.bound_to_core(steps,
          root_authority,honest,before,after,effects,
          K.emission_limit(K.Propose{}),bound)}
    case PublishVote{same}: E.PublishVote{same}
    case PublishProposal{same}: E.PublishProposal{same}
    case DeliverVote{+steps,+effects,bound}:
      E.DeliverVote{steps,NetworkEffects.to_core(steps,root_authority,honest,
        before,after,effects),NetworkEffects.bound_to_core(steps,
          root_authority,honest,before,after,effects,
          K.emission_limit(K.DeliverVote{}),bound)}
    case DeliverProposal{+steps,+effects,bound}:
      E.DeliverProposal{steps,NetworkEffects.to_core(steps,root_authority,
        honest,before,after,effects),NetworkEffects.bound_to_core(steps,
          root_authority,honest,before,after,effects,
          K.emission_limit(K.DeliverProposal{}),bound)}
    case Idle{same}: E.Idle{same}

def NetworkAction.preserve_reachable(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: ValidatorState(),
    +after: ValidatorState(),
    action: NetworkAction<root_authority,honest,before,after>,
    reachable: E.SomeReachable(root_authority,honest,before)) ->
    E.SomeReachable(root_authority,honest,after):
  E.PythonAction.preserve_reachable(root_authority,honest,before,after,
    NetworkAction.to_core(root_authority,honest,before,after,action),reachable)

def NetworkExecution(+actions: Nat, +root_authority: K.Authority,
    +honest: List<&2,Nat>, +state: ValidatorState()) -> Data:
  match actions:
    case 0n: {state == genesis() : ValidatorState()}
    case 1n+actions:
      Sigma<&2,&2,ValidatorState(),before =>
        Sigma<&2,&2,NetworkExecution(actions,root_authority,honest,before),_ =>
          NetworkAction<root_authority,honest,before,state>>>

def NetworkExecution.to_core(+actions: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +state: ValidatorState(),
    execution: NetworkExecution(actions,root_authority,honest,state)) ->
    E.PythonExecution(actions,root_authority,honest,state):
  match actions:
    case 0n: execution
    case 1n+actions:
      (+before,(earlier,action)) = execution
      (before,(NetworkExecution.to_core(actions,root_authority,honest,before,
        earlier),NetworkAction.to_core(root_authority,honest,before,state,
        action)))

def NetworkExecution.finalized_safety(+actions: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +state: ValidatorState(),
    execution: NetworkExecution(actions,root_authority,honest,state),
    +left: C.Path, +right: C.Path,
    left_finalized: E.Finalized<state,left>,
    right_finalized: E.Finalized<state,right>,
    honest_quorum:
      {K.has_quorum(root_authority,honest) == True{} : Bool}) ->
    C.Compatible(left,right):
  E.PythonExecution.finalized_safety(actions,root_authority,honest,state,
    NetworkExecution.to_core(actions,root_authority,honest,state,execution),
    left,right,left_finalized,right_finalized,honest_quorum)
