import Base
import ../model/kernel.bend as K
import ./catchup_gate.bend as C
import ./quorum_gates.bend as Q
import ./reachable_safety.bend as S

# The projected execution contains only durable Vote events and accepted
# finality certificates. Receipts that change neither list are stuttering.
type ProtocolState is Data:
  ProtocolState{events: List<&2,S.VoteEvent>, locks: List<&2,S.FinalityLock>}

def ProtocolState.events(state: ProtocolState) -> List<&2,S.VoteEvent>:
  match state:
    case ProtocolState{events,_}: events

def ProtocolState.locks(state: ProtocolState) -> List<&2,S.FinalityLock>:
  match state:
    case ProtocolState{_,locks}: locks

def genesis() -> ProtocolState:
  ProtocolState{[],[]}

# These are the three finite invariants required by the safety proof. They do
# not contain a pairwise agreement claim.
type Consistent<-root_authority: K.Authority, -honest: List<&2,Nat>,
    -state: ProtocolState> is Data:
  Consistent{
    validity: S.ValidTable(root_authority,honest,ProtocolState.events(state),ProtocolState.locks(state)),
    history: S.HistoryTable(honest,ProtocolState.events(state),ProtocolState.events(state)),
    readiness: S.ReadyTable(ProtocolState.events(state),ProtocolState.locks(state))}

def genesis_consistent(+root_authority: K.Authority, +honest: List<&2,Nat>) ->
    Consistent<root_authority,honest,genesis()>:
  Consistent{Unit{},Unit{},Unit{}}

def consistent_cast(+root_authority: K.Authority, +honest: List<&2,Nat>,
    +before: ProtocolState, +after: ProtocolState,
    same: {after == before : ProtocolState},
    consistent: Consistent<root_authority,honest,before>) ->
    Consistent<root_authority,honest,after>:
  %Equal.sym(ProtocolState,after,before,same) : Consistent<root_authority,honest,_>
  consistent

def emit_state(+event: S.VoteEvent, +before: ProtocolState) -> ProtocolState:
  ProtocolState{event <> ProtocolState.events(before),ProtocolState.locks(before)}

def admit_state(+lock: S.FinalityLock, +before: ProtocolState) -> ProtocolState:
  ProtocolState{ProtocolState.events(before),lock <> ProtocolState.locks(before)}

# Adding a Vote preserves every stored contributor reference.
def stored_event_weaken(+event: S.VoteEvent,
    +events: List<&2,S.VoteEvent>, +contributors: List<&2,S.VoteEvent>,
    stored: S.Stored(events,contributors)) ->
    S.Stored(event <> events,contributors):
  match contributors:
    case Nil{}: Unit{}
    case Con{contributor,rest}:
      (member,tail) = stored
      (S.member_tail(S.VoteEvent,contributor,event,events,member),
        stored_event_weaken(event,events,rest,tail))

def valid_lock_event_weaken(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +event: S.VoteEvent,
    +events: List<&2,S.VoteEvent>, +lock: S.FinalityLock,
    valid: S.ValidLock<root_authority,honest,events,lock>) ->
    S.ValidLock<root_authority,honest,event <> events,lock>:
  match valid:
    case S.ValidLock{stored,covers,below_root,clean,quorum}:
      S.ValidLock{stored_event_weaken(event,events,
        S.FinalityLock.contributors(lock),stored),covers,below_root,clean,quorum}

def valid_table_event_weaken(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +event: S.VoteEvent,
    +events: List<&2,S.VoteEvent>, +locks: List<&2,S.FinalityLock>,
    table: S.ValidTable(root_authority,honest,events,locks)) ->
    S.ValidTable(root_authority,honest,event <> events,locks):
  match locks:
    case Nil{}: Unit{}
    case Con{lock,rest}:
      (valid,tail) = table
      (valid_lock_event_weaken(root_authority,honest,event,events,lock,valid),
        valid_table_event_weaken(root_authority,honest,event,events,rest,tail))

# One new column is prepended to each existing history row.
def history_columns_prepend(+honest: List<&2,Nat>, +older: S.VoteEvent,
    +newer: S.VoteEvent, +old_newers: List<&2,S.VoteEvent>,
    single: S.HistoryColumns(honest,older,[newer]),
    old: S.HistoryColumns(honest,older,old_newers)) ->
    S.HistoryColumns(honest,older,newer <> old_newers):
  match single:
    case (classified,unit): (classified,old)

def history_table_prepend_column(+honest: List<&2,Nat>,
    +olders: List<&2,S.VoteEvent>, +newer: S.VoteEvent,
    +old_newers: List<&2,S.VoteEvent>,
    column: S.HistoryTable(honest,olders,[newer]),
    old: S.HistoryTable(honest,olders,old_newers)) ->
    S.HistoryTable(honest,olders,newer <> old_newers):
  match olders:
    case Nil{}: Unit{}
    case Con{older,rest}:
      (single,columns) = column
      (old_columns,old_rows) = old
      (history_columns_prepend(honest,older,newer,old_newers,
        single,old_columns),history_table_prepend_column(honest,rest,newer,
        old_newers,columns,old_rows))

# Adding a certificate only enlarges the set available to Q3-ready witnesses.
def q3_ready_lock_weaken(+lock: S.FinalityLock,
    +locks: List<&2,S.FinalityLock>, +event: S.VoteEvent,
    ready: S.Q3Ready(locks,event)) -> S.Q3Ready(lock <> locks,event):
  match ready:
    case Inl{genesis}: Inl{genesis}
    case Inr{(+pivot,(member,(same,bound)))}:
      Inr{(pivot,(S.member_tail(S.FinalityLock,pivot,lock,locks,member),
        (same,bound)))}

def ready_table_lock_weaken(+lock: S.FinalityLock,
    +events: List<&2,S.VoteEvent>, +locks: List<&2,S.FinalityLock>,
    table: S.ReadyTable(events,locks)) ->
    S.ReadyTable(events,lock <> locks):
  match events:
    case Nil{}: Unit{}
    case Con{event,rest}:
      (ready,tail) = table
      (q3_ready_lock_weaken(lock,locks,event,ready),
        ready_table_lock_weaken(lock,rest,locks,tail))

# Each non-stuttering step carries only its new local checks. Preservation
# below constructs the complete resulting tables from those checks.
type ProtocolStep<-root_authority: K.Authority, -honest: List<&2,Nat>,
    -before: ProtocolState, -after: ProtocolState> is Data:
  Stutter{same: {after == before : ProtocolState}}
  EmitVote{event: S.VoteEvent,
    same: {after == emit_state(event,before) : ProtocolState},
    new_row: S.HistoryColumns(honest,event,event <> ProtocolState.events(before)),
    new_column: S.HistoryTable(honest,ProtocolState.events(before),[event]),
    q3_ready: S.Q3Ready(ProtocolState.locks(before),event)}
  AdmitCertificate{lock: S.FinalityLock,
    same: {after == admit_state(lock,before) : ProtocolState},
    valid: S.ValidLock<root_authority,honest,ProtocolState.events(before),lock>}
  ApplyAuthority{same: {after == before : ProtocolState}}

def ProtocolStep.preserve(+root_authority: K.Authority, +honest: List<&2,Nat>,
    +before: ProtocolState, +after: ProtocolState,
    step: ProtocolStep<root_authority,honest,before,after>,
    consistent: Consistent<root_authority,honest,before>) ->
    Consistent<root_authority,honest,after>:
  match step:
    case Stutter{same}:
      consistent_cast(root_authority,honest,before,after,same,consistent)
    case EmitVote{+event,same,new_row,new_column,q3_ready}:
      Consistent{validity,history,readiness} = consistent
      built : Consistent<root_authority,honest,emit_state(event,before)> =
        Consistent{
          valid_table_event_weaken(root_authority,honest,event,
            ProtocolState.events(before),ProtocolState.locks(before),validity),
          (new_row,history_table_prepend_column(honest,
            ProtocolState.events(before),event,ProtocolState.events(before),
            new_column,history)),
          (q3_ready,readiness)}
      consistent_cast(root_authority,honest,emit_state(event,before),after,
        same,built)
    case AdmitCertificate{+lock,same,valid}:
      Consistent{validity,history,readiness} = consistent
      built : Consistent<root_authority,honest,admit_state(lock,before)> =
        Consistent{(valid,validity),history,
          ready_table_lock_weaken(lock,ProtocolState.events(before),
            ProtocolState.locks(before),readiness)}
      consistent_cast(root_authority,honest,admit_state(lock,before),after,
        same,built)
    case ApplyAuthority{same}:
      consistent_cast(root_authority,honest,before,after,same,consistent)

def Reachable(+steps: Nat, +root_authority: K.Authority,
    +honest: List<&2,Nat>, +state: ProtocolState) -> Data:
  match steps:
    case 0n: {state == genesis() : ProtocolState}
    case 1n+steps:
      Sigma<&2,&2,ProtocolState,before =>
        Sigma<&2,&2,Reachable(steps,root_authority,honest,before),_ =>
          ProtocolStep<root_authority,honest,before,state>>>

def reachable_consistent(+steps: Nat, +root_authority: K.Authority,
    +honest: List<&2,Nat>, +state: ProtocolState,
    reachable: Reachable(steps,root_authority,honest,state)) ->
    Consistent<root_authority,honest,state>:
  match steps:
    case 0n:
      same = reachable
      consistent_cast(root_authority,honest,genesis(),state,
        same,genesis_consistent(root_authority,honest))
    case 1n+steps:
      (+before,(earlier,step)) = reachable
      ProtocolStep.preserve(root_authority,honest,before,state,step,
        reachable_consistent(steps,root_authority,honest,before,earlier))

# One Python action may contain a finite sequence of safety-relevant effects.
def ActionEffects(+steps: Nat, +root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: ProtocolState,
    +after: ProtocolState) -> Data:
  match steps:
    case 0n: {after == before : ProtocolState}
    case 1n+steps:
      Sigma<&2,&2,ProtocolState,middle =>
        Sigma<&2,&2,ProtocolStep<root_authority,honest,before,middle>,_ =>
          ActionEffects(steps,root_authority,honest,middle,after)>>

def ProtocolStep.emitted_votes(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: ProtocolState, +after: ProtocolState,
    step: ProtocolStep<root_authority,honest,before,after>) -> Nat:
  match step:
    case Stutter{_}: 0n
    case EmitVote{_,_,_,_,_}: 1n
    case AdmitCertificate{_,_,_}: 0n
    case ApplyAuthority{_}: 0n

def ActionEffects.emitted_votes(+steps: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +before: ProtocolState, +after: ProtocolState,
    effects: ActionEffects(steps,root_authority,honest,before,after)) -> Nat:
  match steps:
    case 0n: 0n
    case 1n+steps:
      (+middle,(first,rest)) = effects
      Nat.add(ProtocolStep.emitted_votes(root_authority,honest,before,middle,first),
        ActionEffects.emitted_votes(steps,root_authority,honest,middle,after,rest))

# These seven constructors are the safety projection of the seven Python
# action kinds. Publication and idle actions stutter exactly as in Lean.
type PythonAction<-root_authority: K.Authority, -honest: List<&2,Nat>,
    -before: ProtocolState, -after: ProtocolState> is Data:
  SignVote{steps: Nat,
    effects: ActionEffects(steps,root_authority,honest,before,after),
    emission_bound: Q.Le(ActionEffects.emitted_votes(steps,root_authority,
      honest,before,after,effects),K.emission_limit(K.SignVote{}))}
  Propose{steps: Nat,
    effects: ActionEffects(steps,root_authority,honest,before,after),
    emission_bound: Q.Le(ActionEffects.emitted_votes(steps,root_authority,
      honest,before,after,effects),K.emission_limit(K.Propose{}))}
  PublishVote{same: {after == before : ProtocolState}}
  PublishProposal{same: {after == before : ProtocolState}}
  DeliverVote{steps: Nat,
    effects: ActionEffects(steps,root_authority,honest,before,after),
    emission_bound: Q.Le(ActionEffects.emitted_votes(steps,root_authority,
      honest,before,after,effects),K.emission_limit(K.DeliverVote{}))}
  DeliverProposal{steps: Nat,
    effects: ActionEffects(steps,root_authority,honest,before,after),
    emission_bound: Q.Le(ActionEffects.emitted_votes(steps,root_authority,
      honest,before,after,effects),K.emission_limit(K.DeliverProposal{}))}
  Idle{same: {after == before : ProtocolState}}

def reachable_cast(+steps: Nat, +root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: ProtocolState, +after: ProtocolState,
    same: {after == before : ProtocolState},
    reachable: Reachable(steps,root_authority,honest,before)) ->
    Reachable(steps,root_authority,honest,after):
  %Equal.sym(ProtocolState,after,before,same) : Reachable(steps,root_authority,honest,_)
  reachable

def SomeReachable(+root_authority: K.Authority, +honest: List<&2,Nat>,
    +state: ProtocolState) -> Data:
  Sigma<&2,&2,Nat,steps => Reachable(steps,root_authority,honest,state)>

def ActionEffects.preserve_reachable(+effect_steps: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +before: ProtocolState, +after: ProtocolState,
    effects: ActionEffects(effect_steps,root_authority,honest,before,after),
    reachable: SomeReachable(root_authority,honest,before)) ->
    SomeReachable(root_authority,honest,after):
  match effect_steps:
    case 0n:
      match effects:
        case same:
          match reachable:
            case (+steps,proof):
              (steps,reachable_cast(steps,root_authority,honest,before,after,
                same,proof))
    case 1n+effect_steps:
      match effects:
        case (+middle,(first,rest)):
          match reachable:
            case (+steps,proof):
              ActionEffects.preserve_reachable(effect_steps,root_authority,
                honest,middle,after,rest,
                (1n+steps,(before,(proof,first))))

def PythonAction.preserve_reachable(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +before: ProtocolState, +after: ProtocolState,
    action: PythonAction<root_authority,honest,before,after>,
    reachable: SomeReachable(root_authority,honest,before)) ->
    SomeReachable(root_authority,honest,after):
  match action:
    case SignVote{steps,effects,bound}:
      ActionEffects.preserve_reachable(steps,root_authority,honest,before,after,
        effects,reachable)
    case Propose{steps,effects,bound}:
      ActionEffects.preserve_reachable(steps,root_authority,honest,before,after,
        effects,reachable)
    case PublishVote{same}:
      ActionEffects.preserve_reachable(0n,root_authority,honest,before,after,
        same,reachable)
    case PublishProposal{same}:
      ActionEffects.preserve_reachable(0n,root_authority,honest,before,after,
        same,reachable)
    case DeliverVote{steps,effects,bound}:
      ActionEffects.preserve_reachable(steps,root_authority,honest,before,after,
        effects,reachable)
    case DeliverProposal{steps,effects,bound}:
      ActionEffects.preserve_reachable(steps,root_authority,honest,before,after,
        effects,reachable)
    case Idle{same}:
      ActionEffects.preserve_reachable(0n,root_authority,honest,before,after,
        same,reachable)

# A projected Python execution begins at Genesis and applies whole actions.
def PythonExecution(+actions: Nat, +root_authority: K.Authority,
    +honest: List<&2,Nat>, +state: ProtocolState) -> Data:
  match actions:
    case 0n: {state == genesis() : ProtocolState}
    case 1n+actions:
      Sigma<&2,&2,ProtocolState,before =>
        Sigma<&2,&2,PythonExecution(actions,root_authority,honest,before),_ =>
          PythonAction<root_authority,honest,before,state>>>

def PythonExecution.reachable(+actions: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +state: ProtocolState,
    execution: PythonExecution(actions,root_authority,honest,state)) ->
    SomeReachable(root_authority,honest,state):
  match actions:
    case 0n:
      (0n,reachable_cast(0n,root_authority,honest,genesis(),state,execution,{==}))
    case 1n+actions:
      (+before,(earlier,action)) = execution
      PythonAction.preserve_reachable(root_authority,honest,before,state,action,
        PythonExecution.reachable(actions,root_authority,honest,before,earlier))

type Finalized<-state: ProtocolState, -block: C.Path> is Data:
  FinalizedGenesis{same: {block == [] : C.Path}}
  FinalizedLock{lock: S.FinalityLock,
    member: S.Member(S.FinalityLock,lock,ProtocolState.locks(state)),
    same: {S.FinalityLock.locked(lock) == block : C.Path}}

def finalized_with_consistency(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +state: ProtocolState,
    consistent: Consistent<root_authority,honest,state>,
    +left: C.Path, +right: C.Path,
    left_finalized: Finalized<state,left>,
    right_finalized: Finalized<state,right>,
    honest_quorum: {K.has_quorum(root_authority,honest) == True{} : Bool}) ->
    C.Compatible(left,right):
  Consistent{+validity,+history,+readiness} = consistent
  match left_finalized right_finalized:
    case FinalizedGenesis{left_empty} right_finalized:
      Inl{S.prefix_from_empty(left,right,left_empty)}
    case FinalizedLock{left_lock,+left_member,left_same} FinalizedGenesis{right_empty}:
      Inr{S.prefix_from_empty(right,left,right_empty)}
    case FinalizedLock{left_lock,+left_member,left_same} FinalizedLock{right_lock,+right_member,right_same}:
      locked = S.accepted_locks_agree(root_authority,honest,ProtocolState.events(state),
        ProtocolState.locks(state),validity,history,readiness,left_lock,right_lock,
        left_member,right_member,honest_quorum)
      %left_same : C.Compatible(_,right)
      %right_same : C.Compatible(S.FinalityLock.locked(left_lock),_)
      locked

# End-to-end reachable safety: finalized Blocks never conflict.
def reachable_finalized_safety(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +steps: Nat, +state: ProtocolState,
    reachable: Reachable(steps,root_authority,honest,state),
    +left: C.Path, +right: C.Path,
    left_finalized: Finalized<state,left>,
    right_finalized: Finalized<state,right>,
    honest_quorum: {K.has_quorum(root_authority,honest) == True{} : Bool}) ->
    C.Compatible(left,right):
  finalized_with_consistency(root_authority,honest,state,
    reachable_consistent(steps,root_authority,honest,state,reachable),left,right,
    left_finalized,right_finalized,honest_quorum)

def some_reachable_finalized_safety(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +state: ProtocolState,
    reachable: SomeReachable(root_authority,honest,state),
    +left: C.Path, +right: C.Path,
    left_finalized: Finalized<state,left>,
    right_finalized: Finalized<state,right>,
    honest_quorum: {K.has_quorum(root_authority,honest) == True{} : Bool}) ->
    C.Compatible(left,right):
  match reachable:
    case (steps,proof):
      reachable_finalized_safety(root_authority,honest,steps,state,proof,
        left,right,left_finalized,right_finalized,honest_quorum)

# End-to-end agreement for every projected Python execution.
def PythonExecution.finalized_safety(+actions: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +state: ProtocolState,
    execution: PythonExecution(actions,root_authority,honest,state),
    +left: C.Path, +right: C.Path,
    left_finalized: Finalized<state,left>,
    right_finalized: Finalized<state,right>,
    honest_quorum: {K.has_quorum(root_authority,honest) == True{} : Bool}) ->
    C.Compatible(left,right):
  some_reachable_finalized_safety(root_authority,honest,state,
    PythonExecution.reachable(actions,root_authority,honest,state,execution),
    left,right,left_finalized,right_finalized,honest_quorum)
