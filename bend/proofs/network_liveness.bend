import Base
import ../model/kernel.bend as K
import ./catchup_gate.bend as C
import ./quorum_gates.bend as Q
import ./reduced_quorum_gate.bend as R
import ./reachable_safety.bend as S
import ./reachable_execution.bend as E
import ./network_execution.bend as N

# One accepted Python-model Vote and the local checks used by Network.step.
# It contains no finality witness, completed NetworkAction, or execution.
type AcceptedVote<-root_authority: K.Authority, -honest: List<&2,Nat>,
    -before: N.ValidatorState(), -after: N.ValidatorState()> is Data:
  AcceptedVote{vote: N.Vote,
    same: {after == E.emit_state(N.Vote.event(vote),before) : N.ValidatorState()},
    fresh_time:
      N.FreshTime(E.ProtocolState.events(before),N.Vote.time(vote)),
    fresh_block:
      N.FreshBlock(E.ProtocolState.events(before),N.Vote.signer(vote),
        N.Vote.block(vote)),
    new_row: S.HistoryColumns(honest,N.Vote.event(vote),
      N.Vote.event(vote) <> E.ProtocolState.events(before)),
    new_column: S.HistoryTable(honest,E.ProtocolState.events(before),
      [N.Vote.event(vote)]),
    q3_ready: S.Q3Ready(E.ProtocolState.locks(before),N.Vote.event(vote))}

def AcceptedVote.vote(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(),
    +after: N.ValidatorState(),
    accepted: AcceptedVote<root_authority,honest,before,after>) -> N.Vote:
  match accepted:
    case AcceptedVote{vote,_,_,_,_,_,_}: vote

def AcceptedVote.event(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(),
    +after: N.ValidatorState(),
    +accepted: AcceptedVote<root_authority,honest,before,after>) -> S.VoteEvent:
  N.Vote.event(AcceptedVote.vote(root_authority,honest,before,after,accepted))

def AcceptedVote.step(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(),
    +after: N.ValidatorState(),
    accepted: AcceptedVote<root_authority,honest,before,after>) ->
    N.NetworkStep<root_authority,honest,before,after>:
  match accepted:
    case AcceptedVote{vote,same,fresh_time,fresh_block,new_row,new_column,
        q3_ready}:
      N.EmitVote{vote,same,fresh_time,fresh_block,new_row,new_column,q3_ready}

def AcceptedVote.action(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(),
    +after: N.ValidatorState(),
    +accepted: AcceptedVote<root_authority,honest,before,after>) ->
    N.NetworkAction<root_authority,honest,before,after>:
  match accepted:
    case AcceptedVote{vote,same,fresh_time,fresh_block,new_row,new_column,
        q3_ready}:
      +step : N.NetworkStep<root_authority,honest,before,after> =
        N.EmitVote{vote,same,fresh_time,fresh_block,new_row,new_column,q3_ready}
      +effects : N.NetworkEffects(1n,root_authority,honest,before,after) =
        (after,(step,{==}))
      N.SignVote{1n,effects,Unit{}}

# A finite delivered Vote schedule. Each row is checked against the exact
# ValidatorState produced by the previous row.
def VoteSchedule(+count: Nat, +root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(),
    +after: N.ValidatorState()) -> Data:
  match count:
    case 0n: {after == before : N.ValidatorState()}
    case 1n+count:
      Sigma<&2,&2,N.ValidatorState(),middle =>
        Sigma<&2,&2,AcceptedVote<root_authority,honest,before,middle>,_ =>
          VoteSchedule(count,root_authority,honest,middle,after)>>

def VoteSchedule.delivered_events(+count: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +before: N.ValidatorState(), +after: N.ValidatorState(),
    +schedule: VoteSchedule(count,root_authority,honest,before,after)) ->
    List<&2,S.VoteEvent>:
  match count:
    case 0n: []
    case 1n+count:
      (+middle,(+accepted,+rest)) = schedule
      AcceptedVote.event(root_authority,honest,before,middle,accepted) <>
        VoteSchedule.delivered_events(count,root_authority,honest,middle,after,
          rest)

def VoteSchedule.delivered_signers(+count: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +before: N.ValidatorState(), +after: N.ValidatorState(),
    +schedule: VoteSchedule(count,root_authority,honest,before,after)) ->
    List<&2,Nat>:
  S.signer_list(VoteSchedule.delivered_events(count,root_authority,honest,
    before,after,schedule))

def state_cast(+before: N.ValidatorState(), +after: N.ValidatorState(),
    same: {after == before : N.ValidatorState()},
    +event: S.VoteEvent,
    member: S.Member(S.VoteEvent,event,E.ProtocolState.events(before))) ->
    S.Member(S.VoteEvent,event,E.ProtocolState.events(after)):
  %Equal.sym(N.ValidatorState(),after,before,same) :
    S.Member(S.VoteEvent,event,E.ProtocolState.events(_))
  member

def AcceptedVote.new_member(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(),
    +after: N.ValidatorState(),
    +accepted: AcceptedVote<root_authority,honest,before,after>) ->
    S.Member(S.VoteEvent,
      AcceptedVote.event(root_authority,honest,before,after,accepted),
      E.ProtocolState.events(after)):
  match accepted:
    case AcceptedVote{vote,same,_,_,_,_,_}:
      +event = N.Vote.event(vote)
      +member = S.member_head(S.VoteEvent,event,E.ProtocolState.events(before))
      state_cast(E.emit_state(event,before),after,same,event,member)

def AcceptedVote.preserve_member(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(),
    +after: N.ValidatorState(),
    accepted: AcceptedVote<root_authority,honest,before,after>,
    +event: S.VoteEvent,
    member: S.Member(S.VoteEvent,event,E.ProtocolState.events(before))) ->
    S.Member(S.VoteEvent,event,E.ProtocolState.events(after)):
  match accepted:
    case AcceptedVote{vote,same,_,_,_,_,_}:
      +new_event = N.Vote.event(vote)
      +weakened = S.member_tail(S.VoteEvent,event,new_event,
        E.ProtocolState.events(before),member)
      state_cast(E.emit_state(new_event,before),after,same,event,weakened)

def VoteSchedule.preserve_member(+count: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +before: N.ValidatorState(), +after: N.ValidatorState(),
    schedule: VoteSchedule(count,root_authority,honest,before,after),
    +event: S.VoteEvent,
    member: S.Member(S.VoteEvent,event,E.ProtocolState.events(before))) ->
    S.Member(S.VoteEvent,event,E.ProtocolState.events(after)):
  match count:
    case 0n: state_cast(before,after,schedule,event,member)
    case 1n+count:
      (+middle,(accepted,rest)) = schedule
      VoteSchedule.preserve_member(count,root_authority,honest,middle,after,
        rest,event,AcceptedVote.preserve_member(root_authority,honest,before,
          middle,accepted,event,member))

def VoteSchedule.delivered_stored(+count: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +before: N.ValidatorState(), +after: N.ValidatorState(),
    +schedule: VoteSchedule(count,root_authority,honest,before,after)) ->
    S.Stored(E.ProtocolState.events(after),
      VoteSchedule.delivered_events(count,root_authority,honest,before,after,
        schedule)):
  match count:
    case 0n: Unit{}
    case 1n+count:
      (+middle,(+accepted,+rest)) = schedule
      +event = AcceptedVote.event(root_authority,honest,before,middle,accepted)
      (VoteSchedule.preserve_member(count,root_authority,honest,middle,after,
          rest,event,AcceptedVote.new_member(root_authority,honest,before,
            middle,accepted)),
        VoteSchedule.delivered_stored(count,root_authority,honest,middle,after,
          rest))

def execution_cast(+actions: Nat, +root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(),
    +after: N.ValidatorState(), same: {after == before : N.ValidatorState()},
    execution: N.NetworkExecution(actions,root_authority,honest,before)) ->
    N.NetworkExecution(actions,root_authority,honest,after):
  %Equal.sym(N.ValidatorState(),after,before,same) :
    N.NetworkExecution(actions,root_authority,honest,_)
  execution

def SomeNetworkExecution(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +state: N.ValidatorState()) -> Data:
  Sigma<&2,&2,Nat,actions =>
    N.NetworkExecution(actions,root_authority,honest,state)>

def AcceptedVote.extend_execution(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(),
    +after: N.ValidatorState(),
    +accepted: AcceptedVote<root_authority,honest,before,after>,
    execution: SomeNetworkExecution(root_authority,honest,before)) ->
    SomeNetworkExecution(root_authority,honest,after):
  match execution:
    case (+actions,proof):
      (1n+actions,(before,(proof,
        AcceptedVote.action(root_authority,honest,before,after,accepted))))

def NetworkAction.extend_execution(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(),
    +after: N.ValidatorState(),
    +action: N.NetworkAction<root_authority,honest,before,after>,
    execution: SomeNetworkExecution(root_authority,honest,before)) ->
    SomeNetworkExecution(root_authority,honest,after):
  match execution:
    case (+actions,proof): (1n+actions,(before,(proof,action)))

def VoteSchedule.extend_execution(+count: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +before: N.ValidatorState(), +after: N.ValidatorState(),
    schedule: VoteSchedule(count,root_authority,honest,before,after),
    execution: SomeNetworkExecution(root_authority,honest,before)) ->
    SomeNetworkExecution(root_authority,honest,after):
  match count:
    case 0n:
      match execution:
        case (+actions,proof):
          (actions,execution_cast(actions,root_authority,honest,before,after,
            schedule,proof))
    case 1n+count:
      (+middle,(accepted,rest)) = schedule
      VoteSchedule.extend_execution(count,root_authority,honest,middle,after,
        rest,AcceptedVote.extend_execution(root_authority,honest,before,middle,
          accepted,execution))

def lock_member_cast(+before: N.ValidatorState(), +after: N.ValidatorState(),
    same: {after == before : N.ValidatorState()}, +lock: S.FinalityLock,
    member: S.Member(S.FinalityLock,lock,E.ProtocolState.locks(before))) ->
    S.Member(S.FinalityLock,lock,E.ProtocolState.locks(after)):
  %Equal.sym(N.ValidatorState(),after,before,same) :
    S.Member(S.FinalityLock,lock,E.ProtocolState.locks(_))
  member

def AcceptedVote.preserve_lock(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(),
    +after: N.ValidatorState(),
    accepted: AcceptedVote<root_authority,honest,before,after>,
    +lock: S.FinalityLock,
    member: S.Member(S.FinalityLock,lock,E.ProtocolState.locks(before))) ->
    S.Member(S.FinalityLock,lock,E.ProtocolState.locks(after)):
  match accepted:
    case AcceptedVote{vote,same,_,_,_,_,_}:
      lock_member_cast(E.emit_state(N.Vote.event(vote),before),after,same,lock,
        member)

def VoteSchedule.preserve_lock(+count: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +before: N.ValidatorState(), +after: N.ValidatorState(),
    schedule: VoteSchedule(count,root_authority,honest,before,after),
    +lock: S.FinalityLock,
    member: S.Member(S.FinalityLock,lock,E.ProtocolState.locks(before))) ->
    S.Member(S.FinalityLock,lock,E.ProtocolState.locks(after)):
  match count:
    case 0n: lock_member_cast(before,after,schedule,lock,member)
    case 1n+count:
      (+middle,(accepted,rest)) = schedule
      VoteSchedule.preserve_lock(count,root_authority,honest,middle,after,rest,
        lock,AcceptedVote.preserve_lock(root_authority,honest,before,middle,
          accepted,lock,member))

type FinalityDelivery<-root_authority: K.Authority,
    -honest: List<&2,Nat>, -before: N.ValidatorState(),
    -locked: C.Path> is Data:
  FinalityDelivery{count: Nat, ready: N.ValidatorState(), root: C.Path,
    offenders: List<&2,Nat>,
    schedule: VoteSchedule(count,root_authority,honest,before,ready),
    all_honest_votes:
      {VoteSchedule.delivered_signers(count,root_authority,honest,before,ready,
        schedule) == honest : List<&2,Nat>},
    covers: S.Covers(locked,
      VoteSchedule.delivered_events(count,root_authority,honest,before,ready,
        schedule)),
    below_root: S.BelowRoot(root,
      VoteSchedule.delivered_events(count,root_authority,honest,before,ready,
        schedule)),
    clean: R.Clean(K.Authority.members(root_authority),offenders,honest),
    honest_quorum:
      {K.has_quorum(K.after_evidence(root_authority,offenders),honest) ==
        True{} : Bool}}

def FinalityDelivery.lock(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(), +locked: C.Path,
    +delivery: FinalityDelivery<root_authority,honest,before,locked>) ->
    S.FinalityLock:
  match delivery:
    case FinalityDelivery{count,ready,root,offenders,schedule,_,_,_,_,_}:
      S.FinalityLock{locked,root,
        VoteSchedule.delivered_events(count,root_authority,honest,before,ready,
          schedule),offenders}

def FinalityDelivery.ready(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(), +locked: C.Path,
    delivery: FinalityDelivery<root_authority,honest,before,locked>) ->
    N.ValidatorState():
  match delivery:
    case FinalityDelivery{_,ready,_,_,_,_,_,_,_,_}: ready

def FinalityDelivery.locked(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(), +locked: C.Path,
    +delivery: FinalityDelivery<root_authority,honest,before,locked>) ->
    {S.FinalityLock.locked(FinalityDelivery.lock(root_authority,honest,before,
      locked,delivery)) == locked : C.Path}:
  match delivery:
    case FinalityDelivery{_,_,_,_,_,_,_,_,_,_}: {==}

def FinalityDelivery.after(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(), +locked: C.Path,
    +delivery: FinalityDelivery<root_authority,honest,before,locked>) ->
    N.ValidatorState():
  E.admit_state(FinalityDelivery.lock(root_authority,honest,before,locked,
    delivery),FinalityDelivery.ready(root_authority,honest,before,locked,
      delivery))

def FinalityDelivery.valid(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(), +locked: C.Path,
    +delivery: FinalityDelivery<root_authority,honest,before,locked>) ->
    S.ValidLock<root_authority,honest,
      E.ProtocolState.events(FinalityDelivery.ready(root_authority,honest,
        before,locked,delivery)),
      FinalityDelivery.lock(root_authority,honest,before,locked,delivery)>:
  match delivery:
    case FinalityDelivery{+count,+ready,+root,+offenders,+schedule,
        all_honest_votes,covers,below_root,clean,honest_quorum}:
      +contributors = VoteSchedule.delivered_events(count,root_authority,
        honest,before,ready,schedule)
      +signers = VoteSchedule.delivered_signers(count,root_authority,honest,
        before,ready,schedule)
      +same_quorum = Equal.cong(List<&2,Nat>,Bool,
        values => K.has_quorum(K.after_evidence(root_authority,offenders),
          values),signers,honest,all_honest_votes)
      +quorum = C.equality_trans(Bool,
        K.has_quorum(K.after_evidence(root_authority,offenders),signers),
        K.has_quorum(K.after_evidence(root_authority,offenders),honest),True{},
        same_quorum,honest_quorum)
      S.ValidLock{
        VoteSchedule.delivered_stored(count,root_authority,honest,before,
          ready,schedule),covers,below_root,clean,quorum}

def FinalityDelivery.action(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(), +locked: C.Path,
    +delivery: FinalityDelivery<root_authority,honest,before,locked>) ->
    N.NetworkAction<root_authority,honest,
      FinalityDelivery.ready(root_authority,honest,before,locked,delivery),
      FinalityDelivery.after(root_authority,honest,before,locked,delivery)>:
  +ready = FinalityDelivery.ready(root_authority,honest,before,locked,delivery)
  +after = FinalityDelivery.after(root_authority,honest,before,locked,delivery)
  +lock = FinalityDelivery.lock(root_authority,honest,before,locked,delivery)
  +step : N.NetworkStep<root_authority,honest,ready,after> =
    N.AdmitFinality{lock,{==},
      FinalityDelivery.valid(root_authority,honest,before,locked,delivery)}
  +effects : N.NetworkEffects(1n,root_authority,honest,ready,after) =
    (after,(step,{==}))
  N.DeliverProposal{1n,effects,Unit{}}

def FinalityDelivery.extend_execution(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(), +locked: C.Path,
    +delivery: FinalityDelivery<root_authority,honest,before,locked>,
    execution: SomeNetworkExecution(root_authority,honest,before)) ->
    SomeNetworkExecution(root_authority,honest,
      FinalityDelivery.after(root_authority,honest,before,locked,delivery)):
  match delivery:
    case FinalityDelivery{count,ready,root,offenders,schedule,all,covers,below,
        clean,quorum}:
      +whole : FinalityDelivery<root_authority,honest,before,locked> =
        FinalityDelivery{count,ready,root,offenders,schedule,all,covers,below,
          clean,quorum}
      NetworkAction.extend_execution(root_authority,honest,ready,
        FinalityDelivery.after(root_authority,honest,before,locked,whole),
        FinalityDelivery.action(root_authority,honest,before,locked,whole),
        VoteSchedule.extend_execution(count,root_authority,honest,before,
          ready,schedule,execution))

def FinalityDelivery.finalized(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(), +locked: C.Path,
    +delivery: FinalityDelivery<root_authority,honest,before,locked>) ->
    E.Finalized<
      FinalityDelivery.after(root_authority,honest,before,locked,delivery),
      locked>:
  +ready = FinalityDelivery.ready(root_authority,honest,before,locked,delivery)
  +lock = FinalityDelivery.lock(root_authority,honest,before,locked,delivery)
  E.FinalizedLock{lock,S.member_head(S.FinalityLock,lock,
    E.ProtocolState.locks(ready)),FinalityDelivery.locked(root_authority,
      honest,before,locked,delivery)}

type FutureActivity<-root_authority: K.Authority,
    -honest: List<&2,Nat>, -before: N.ValidatorState(),
    -selected_chain: K.Chain()> is Data:
  FutureActivity{parent: K.ScannedTarget, block: K.Block,
    offenders: List<&2,Nat>,
    admissible:
      K.AdmissibleChild<honest,parent,selected_chain,block,offenders>,
    selected_votes:
      FinalityDelivery<root_authority,honest,before,
        K.chain_path(selected_chain)>,
    descendant_votes:
      FinalityDelivery<root_authority,honest,
        FinalityDelivery.after(root_authority,honest,before,
          K.chain_path(selected_chain),selected_votes),
        K.chain_path(List.append(&2,K.Block,selected_chain,[block]))>}

def prefix_append_one(+path: C.Path, +tip: Nat) ->
    C.Prefix(path,List.append(&2,Nat,path,[tip])):
  match path:
    case Nil{}: Unit{}
    case Con{head,rest}: ({==},prefix_append_one(rest,tip))

def append_one_strict(+path: C.Path, +tip: Nat) ->
    Q.Le(1n+List.length(&2,Nat,path),
      List.length(&2,Nat,List.append(&2,Nat,path,[tip]))):
  match path:
    case Nil{}: Unit{}
    case Con{head,rest}: append_one_strict(rest,tip)

def extension_prefix(+chain: K.Chain(), +block: K.Block) ->
    C.Prefix(K.chain_path(chain),
      K.chain_path(List.append(&2,K.Block,chain,[block]))):
  +path = prefix_append_one(K.chain_path(chain),K.Block.id(block))
  %Equal.sym(List<&2,Nat>,
    K.chain_path(List.append(&2,K.Block,chain,[block])),
    List.append(&2,Nat,K.chain_path(chain),[K.Block.id(block)]),
    K.chain_path_append_block(chain,block)) : C.Prefix(K.chain_path(chain),_)
  path

def extension_strict(+chain: K.Chain(), +block: K.Block) ->
    Q.Le(1n+List.length(&2,Nat,K.chain_path(chain)),
      List.length(&2,Nat,
        K.chain_path(List.append(&2,K.Block,chain,[block])))):
  +strict = append_one_strict(K.chain_path(chain),K.Block.id(block))
  +same = Equal.cong(List<&2,Nat>,Nat,
    path => List.length(&2,Nat,path),
    K.chain_path(List.append(&2,K.Block,chain,[block])),
    List.append(&2,Nat,K.chain_path(chain),[K.Block.id(block)]),
    K.chain_path_append_block(chain,block))
  %Equal.sym(Nat,
    List.length(&2,Nat,K.chain_path(List.append(&2,K.Block,chain,[block]))),
    List.length(&2,Nat,
      List.append(&2,Nat,K.chain_path(chain),[K.Block.id(block)])),same) :
    Q.Le(1n+List.length(&2,Nat,K.chain_path(chain)),_)
  strict

type NetworkLivenessResult<-root_authority: K.Authority,
    -honest: List<&2,Nat>, -before: N.ValidatorState(),
    -selected_chain: K.Chain()> is Data:
  NetworkLivenessResult{parent: K.ScannedTarget, block: K.Block,
    offenders: List<&2,Nat>, descendant_chain: K.Chain(),
    after: N.ValidatorState(), actions: Nat,
    execution: N.NetworkExecution(actions,root_authority,honest,after),
    selected_finalized: E.Finalized<after,K.chain_path(selected_chain)>,
    descendant_finalized: E.Finalized<after,K.chain_path(descendant_chain)>,
    descendant_admissible:
      K.AdmissibleChild<honest,parent,selected_chain,block,offenders>,
    descendant_extension:
      {descendant_chain ==
        List.append(&2,K.Block,selected_chain,[block]) : K.Chain()},
    descendant_path:
      C.Prefix(K.chain_path(selected_chain),K.chain_path(descendant_chain)),
    strict_progress:
      Q.Le(1n+List.length(&2,Nat,K.chain_path(selected_chain)),
        List.length(&2,Nat,K.chain_path(descendant_chain)))}

def finish_liveness(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(),
    +selected_chain: K.Chain(), +parent: K.ScannedTarget,
    +block: K.Block, +offenders: List<&2,Nat>,
    +after: N.ValidatorState(),
    final_execution: SomeNetworkExecution(root_authority,honest,after),
    selected_finalized: E.Finalized<after,K.chain_path(selected_chain)>,
    descendant_finalized: E.Finalized<after,
      K.chain_path(List.append(&2,K.Block,selected_chain,[block]))>,
    admissible:
      K.AdmissibleChild<honest,parent,selected_chain,block,offenders>) ->
    NetworkLivenessResult<root_authority,honest,before,selected_chain>:
  match final_execution:
    case (+actions,proof):
      +descendant_chain = List.append(&2,K.Block,selected_chain,[block])
      NetworkLivenessResult{parent,block,offenders,descendant_chain,after,
        actions,proof,selected_finalized,descendant_finalized,admissible,{==},
        extension_prefix(selected_chain,block),
        extension_strict(selected_chain,block)}

def extend_with_finality(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(),
    +selected_chain: K.Chain(),
    execution: SomeNetworkExecution(root_authority,honest,before),
    future: FutureActivity<root_authority,honest,before,selected_chain>) ->
    NetworkLivenessResult<root_authority,honest,before,selected_chain>:
  match future:
    case FutureActivity{+parent,+block,+offenders,admissible,+selected_votes,
        +descendant_votes}:
      match descendant_votes:
        case FinalityDelivery{+count,+ready,+root,+lock_offenders,+schedule,+all,
            +covers,+below,+clean,+quorum}:
          +selected_path = K.chain_path(selected_chain)
          +selected_after = FinalityDelivery.after(root_authority,honest,before,
            selected_path,selected_votes)
          +descendant_chain = List.append(&2,K.Block,selected_chain,[block])
          +descendant_path = K.chain_path(descendant_chain)
          +descendant_delivery : FinalityDelivery<root_authority,honest,
              selected_after,descendant_path> =
            FinalityDelivery{count,ready,root,lock_offenders,schedule,all,covers,
              below,clean,quorum}
          +after = FinalityDelivery.after(root_authority,honest,selected_after,
            descendant_path,descendant_delivery)
          +selected_execution = FinalityDelivery.extend_execution(
            root_authority,honest,before,selected_path,selected_votes,execution)
          +final_execution = FinalityDelivery.extend_execution(root_authority,
            honest,selected_after,descendant_path,descendant_delivery,
            selected_execution)
          +selected_lock = FinalityDelivery.lock(root_authority,honest,before,
            selected_path,selected_votes)
          +selected_ready = FinalityDelivery.ready(root_authority,honest,
            before,selected_path,selected_votes)
          +descendant_lock = FinalityDelivery.lock(root_authority,honest,
            selected_after,descendant_path,descendant_delivery)
          +selected_at_selected_after = S.member_head(S.FinalityLock,
            selected_lock,E.ProtocolState.locks(selected_ready))
          +selected_at_ready = VoteSchedule.preserve_lock(count,
            root_authority,honest,selected_after,ready,schedule,selected_lock,
            selected_at_selected_after)
          +selected_at_after = S.member_tail(S.FinalityLock,selected_lock,
            descendant_lock,E.ProtocolState.locks(ready),selected_at_ready)
          +selected_finalized : E.Finalized<after,selected_path> =
            E.FinalizedLock{selected_lock,selected_at_after,
              FinalityDelivery.locked(root_authority,honest,before,
                selected_path,selected_votes)}
          +descendant_finalized = FinalityDelivery.finalized(root_authority,
            honest,selected_after,descendant_path,descendant_delivery)
          finish_liveness(root_authority,honest,before,selected_chain,parent,
            block,offenders,after,final_execution,selected_finalized,
            descendant_finalized,admissible)

# Safety and liveness meet on the same execution object. This is a theorem
# application, not an ancestry shortcut: both native Finalized witnesses are
# passed to NetworkExecution.finalized_safety.
def NetworkLivenessResult.finalized_safety(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: N.ValidatorState(),
    +selected_chain: K.Chain(),
    result: NetworkLivenessResult<root_authority,honest,before,selected_chain>,
    honest_quorum:
      {K.has_quorum(root_authority,honest) == True{} : Bool}) ->
    Sigma<&2,&2,K.Chain(),descendant_chain =>
      C.Compatible(K.chain_path(selected_chain),
        K.chain_path(descendant_chain))>:
  match result:
    case NetworkLivenessResult{_,block,_,+descendant_chain,+after,+actions,
        execution,selected_finalized,descendant_finalized,_,_,_,_}:
      (descendant_chain,N.NetworkExecution.finalized_safety(actions,
        root_authority,honest,after,execution,K.chain_path(selected_chain),
        K.chain_path(descendant_chain),selected_finalized,
        descendant_finalized,honest_quorum))
