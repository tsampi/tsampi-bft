import Base
import ../model/kernel.bend as K
import ./quorum_gates.bend as Q
import ./reduced_quorum_gate.bend as R
import ./catchup_gate.bend as C

# Safety-relevant projection of a durable Vote.
type VoteEvent is Data:
  VoteEvent{time: Nat, signer: Nat, block: Nat, target: C.Path,
    q2: C.Path, q3: C.Path,
    q3_below_q2: C.Prefix(q3,q2)}

# One accepted outer-Q1 certificate. Its parent authority is the root authority
# after the listed verified offenders have been removed.
type FinalityLock is Data:
  FinalityLock{locked: C.Path, root: C.Path,
    contributors: List<&2,VoteEvent>, offenders: List<&2,Nat>}

def VoteEvent.time(event: VoteEvent) -> Nat:
  match event:
    case VoteEvent{time,_,_,_,_,_,_}: time

def VoteEvent.signer(event: VoteEvent) -> Nat:
  match event:
    case VoteEvent{_,signer,_,_,_,_,_}: signer

def VoteEvent.block(event: VoteEvent) -> Nat:
  match event:
    case VoteEvent{_,_,block,_,_,_,_}: block

def VoteEvent.target(event: VoteEvent) -> C.Path:
  match event:
    case VoteEvent{_,_,_,target,_,_,_}: target

def VoteEvent.q2(event: VoteEvent) -> C.Path:
  match event:
    case VoteEvent{_,_,_,_,q2,_,_}: q2

def VoteEvent.q3(event: VoteEvent) -> C.Path:
  match event:
    case VoteEvent{_,_,_,_,_,q3,_}: q3

def VoteEvent.q3_below_q2(event: VoteEvent) -> C.Prefix(VoteEvent.q3(event),VoteEvent.q2(event)):
  match event:
    case VoteEvent{_,_,_,_,_,_,proof}: proof

def FinalityLock.locked(lock: FinalityLock) -> C.Path:
  match lock:
    case FinalityLock{locked,_,_,_}: locked

def FinalityLock.root(lock: FinalityLock) -> C.Path:
  match lock:
    case FinalityLock{_,root,_,_}: root

def FinalityLock.contributors(lock: FinalityLock) -> List<&2,VoteEvent>:
  match lock:
    case FinalityLock{_,_,contributors,_}: contributors

def FinalityLock.offenders(lock: FinalityLock) -> List<&2,Nat>:
  match lock:
    case FinalityLock{_,_,_,offenders}: offenders

def signer_list(events: List<&2,VoteEvent>) -> List<&2,Nat>:
  match events:
    case Nil{}: []
    case Con{event,rest}: VoteEvent.signer(event) <> signer_list(rest)

def FinalityLock.signers(lock: FinalityLock) -> List<&2,Nat>:
  signer_list(FinalityLock.contributors(lock))

# Structural membership. No decidable equality or object hash is needed.
def Member(-A: Data, +wanted: A, +items: List<&2,A>) -> Data:
  match items:
    case Nil{}: Empty
    case Con{item,rest}:
      Either<&2,&2,{wanted == item : A},Member(A,wanted,rest)>

def member_head(-A: Data, +item: A, +rest: List<&2,A>) -> Member(A,item,item <> rest):
  Inl{{==}}

def member_tail(-A: Data, +wanted: A, +item: A, +rest: List<&2,A>, member: Member(A,wanted,rest)) -> Member(A,wanted,item <> rest):
  Inr{member}

# Certificate facts are aligned with the contributor list.
def Stored(+events: List<&2,VoteEvent>, +contributors: List<&2,VoteEvent>) -> Data:
  match contributors:
    case Nil{}: Unit
    case Con{event,rest}:
      Sigma<&2,&2,Member(VoteEvent,event,events),_ => Stored(events,rest)>

def Covers(+locked: C.Path, +contributors: List<&2,VoteEvent>) -> Data:
  match contributors:
    case Nil{}: Unit
    case Con{event,rest}:
      Sigma<&2,&2,C.Prefix(locked,VoteEvent.q2(event)),_ => Covers(locked,rest)>

def BelowRoot(+root: C.Path, +contributors: List<&2,VoteEvent>) -> Data:
  match contributors:
    case Nil{}: Unit
    case Con{event,rest}:
      Sigma<&2,&2,Q.Le(1n+List.length(&2,Nat,VoteEvent.target(event)),List.length(&2,Nat,root)),_ => BelowRoot(root,rest)>

type ValidLock<-root_authority: K.Authority, -honest: List<&2,Nat>,
    -events: List<&2,VoteEvent>, -lock: FinalityLock> is Data:
  ValidLock{
    stored: Stored(events,FinalityLock.contributors(lock)),
    covers: Covers(FinalityLock.locked(lock),FinalityLock.contributors(lock)),
    below_root: BelowRoot(FinalityLock.root(lock),FinalityLock.contributors(lock)),
    clean: R.Clean(K.Authority.members(root_authority),FinalityLock.offenders(lock),honest),
    quorum: {K.has_quorum(K.after_evidence(root_authority,FinalityLock.offenders(lock)),FinalityLock.signers(lock)) == True{} : Bool}}

def RankLE(+older: VoteEvent, +newer: VoteEvent) -> Data:
  Either<&2,&2,
    C.Prefix(VoteEvent.q2(older),VoteEvent.q2(newer)),
    Sigma<&2,&2,C.Prefix(VoteEvent.q3(older),VoteEvent.q3(newer)),_ =>
      Q.Le(List.length(&2,Nat,VoteEvent.q2(older)),List.length(&2,Nat,VoteEvent.q3(newer)))>>

# Every non-Genesis Q3 used by an emitted Vote names an already accepted
# certificate whose root is no later than that Vote target.
def Q3Ready(+locks: List<&2,FinalityLock>, +event: VoteEvent) -> Data:
  Either<&2,&2,
    {VoteEvent.q3(event) == [] : C.Path},
    Sigma<&2,&2,FinalityLock,pivot =>
      Sigma<&2,&2,Member(FinalityLock,pivot,locks),_ =>
        Sigma<&2,&2,{FinalityLock.locked(pivot) == VoteEvent.q3(event) : C.Path},_ =>
          Q.Le(List.length(&2,Nat,FinalityLock.root(pivot)),List.length(&2,Nat,VoteEvent.target(event)))>>>>

type Located<-events: List<&2,VoteEvent>, -locked: C.Path, -root: C.Path,
    -signer: Nat> is Data:
  Located{event: VoteEvent,
    stored: Member(VoteEvent,event,events),
    same_signer: {VoteEvent.signer(event) == signer : Nat},
    covers: C.Prefix(locked,VoteEvent.q2(event)),
    below_root: Q.Le(1n+List.length(&2,Nat,VoteEvent.target(event)),List.length(&2,Nat,root))}

def nat_eq_true(+left: Nat, +right: Nat, proof: {K.nat_eq(left,right) == True{} : Bool}) -> {left == right : Nat}:
  match left right:
    case 0n 0n: {==}
    case 0n 1n+right: Empty.absurd({0n == 1n+right : Nat},Q.false_empty(proof))
    case 1n+left 0n: Empty.absurd({1n+left == 0n : Nat},Q.false_empty(proof))
    case 1n+left 1n+right:
      Equal.cong(Nat,Nat,x => 1n+x,left,right,nat_eq_true(left,right,proof))

def false_or(+value: Bool) -> {False{} || value == value : Bool}:
  match value:
    case False{}: {==}
    case True{}: {==}

def locate_case(+events: List<&2,VoteEvent>, +locked: C.Path, +root: C.Path,
    +signer: Nat, +event: VoteEvent, +rest: List<&2,VoteEvent>,
    stored_here: Member(VoteEvent,event,events), +stored_rest: Stored(events,rest),
    covers_here: C.Prefix(locked,VoteEvent.q2(event)), +covers_rest: Covers(locked,rest),
    below_here: Q.Le(1n+List.length(&2,Nat,VoteEvent.target(event)),List.length(&2,Nat,root)),
    +below_rest: BelowRoot(root,rest), +same: Bool,
    same_value: {K.nat_eq(VoteEvent.signer(event),signer) == same : Bool},
    found: {K.contains(signer_list(event <> rest),signer) == True{} : Bool},
    recurse: {K.contains(signer_list(rest),signer) == True{} : Bool} -> Located<events,locked,root,signer>) -> Located<events,locked,root,signer>:
  match same:
    case True{}:
      Located{event,stored_here,nat_eq_true(VoteEvent.signer(event),signer,same_value),covers_here,below_here}
    case False{}:
      +tail = K.contains(signer_list(rest),signer)
      first = Equal.cong(Bool,Bool,x => x || tail,K.nat_eq(VoteEvent.signer(event),signer),False{},same_value)
      whole_tail = C.equality_trans(Bool,K.nat_eq(VoteEvent.signer(event),signer) || tail,False{} || tail,tail,first,false_or(tail))
      tail_found = C.equality_trans(Bool,tail,K.nat_eq(VoteEvent.signer(event),signer) || tail,True{},Equal.sym(Bool,K.nat_eq(VoteEvent.signer(event),signer) || tail,tail,whole_tail),found)
      recurse(tail_found)

def locate(+events: List<&2,VoteEvent>, +locked: C.Path, +root: C.Path,
    +contributors: List<&2,VoteEvent>, +signer: Nat,
    stored: Stored(events,contributors), covers: Covers(locked,contributors),
    below: BelowRoot(root,contributors),
    found: {K.contains(signer_list(contributors),signer) == True{} : Bool}) -> Located<events,locked,root,signer>:
  match contributors:
    case Nil{}: Empty.absurd(Located<events,locked,root,signer>,Q.false_empty(found))
    case Con{event,rest}:
      (stored_here,+stored_rest) = stored
      (covers_here,+covers_rest) = covers
      (below_here,+below_rest) = below
      locate_case(events,locked,root,signer,event,rest,stored_here,stored_rest,
        covers_here,covers_rest,below_here,below_rest,
        K.nat_eq(VoteEvent.signer(event),signer),Q.refl(Bool,K.nat_eq(VoteEvent.signer(event),signer)),found,
        next => locate(events,locked,root,rest,signer,stored_rest,covers_rest,below_rest,next))

def le_total(+left: Nat, +right: Nat) -> Either<&2,&2,Q.Le(left,right),Q.Le(right,left)>:
  match left right:
    case 0n right: Inl{Unit{}}
    case 1n+left 0n: Inr{Unit{}}
    case 1n+left 1n+right: le_total(left,right)

def compatible_sym(+left: C.Path, +right: C.Path, compatible: C.Compatible(left,right)) -> C.Compatible(right,left):
  match compatible:
    case Inl{forward}: Inr{forward}
    case Inr{backward}: Inl{backward}

def path_empty(+path: C.Path, length_zero: Q.Le(List.length(&2,Nat,path),0n)) -> {path == [] : C.Path}:
  match path:
    case Nil{}: {==}
    case Con{head,tail}: Empty.absurd({path == [] : C.Path},length_zero)

def prefix_from_empty(+ancestor: C.Path, +descendant: C.Path,
    empty: {ancestor == [] : C.Path}) -> C.Prefix(ancestor,descendant):
  match ancestor:
    case Nil{}: Unit{}
    case Con{head,tail}:
      length_equal = Equal.cong(C.Path,Nat,x => List.length(&2,Nat,x),ancestor,[],empty)
      impossible = C.zero_successor_empty(List.length(&2,Nat,tail),Equal.sym(Nat,1n+List.length(&2,Nat,tail),0n,length_equal))
      Empty.absurd(C.Prefix(ancestor,descendant),impossible)

def smaller_sum(+older_root: C.Path, +pivot_root: C.Path, +newer_root: C.Path,
    +newer_target: C.Path, +fuel: Nat,
    pivot_bound: Q.Le(List.length(&2,Nat,pivot_root),List.length(&2,Nat,newer_target)),
    target_below_root: Q.Le(1n+List.length(&2,Nat,newer_target),List.length(&2,Nat,newer_root)),
    pair_bound: Q.Le(Nat.add(List.length(&2,Nat,older_root),List.length(&2,Nat,newer_root)),1n+fuel)) ->
    Q.Le(Nat.add(List.length(&2,Nat,older_root),List.length(&2,Nat,pivot_root)),fuel):
  +older = List.length(&2,Nat,older_root)
  +pivot = List.length(&2,Nat,pivot_root)
  +target = List.length(&2,Nat,newer_target)
  +newer = List.length(&2,Nat,newer_root)
  pivot_strict : Q.Le(1n+pivot,newer) = Q.le_trans(1n+pivot,1n+target,newer,pivot_bound,target_below_root)
  with_older = Q.le_add(older,older,1n+pivot,newer,Q.le_refl(older),pivot_strict)
  normalized : Q.Le(1n+Nat.add(older,pivot),Nat.add(older,newer)) = %Q.add_successor(older,pivot) : Q.Le(_,Nat.add(older,newer)); with_older
  Q.le_trans(1n+Nat.add(older,pivot),Nat.add(older,newer),1n+fuel,normalized,pair_bound)

def swap_sum_bound(+left: Nat, +right: Nat, +bound: Nat,
    proof: Q.Le(Nat.add(left,right),bound)) -> Q.Le(Nat.add(right,left),bound):
  %Q.add_comm(left,right) : Q.Le(_,bound)
  proof

def ValidTable(+root_authority: K.Authority, +honest: List<&2,Nat>,
    +events: List<&2,VoteEvent>, +locks: List<&2,FinalityLock>) -> Data:
  match locks:
    case Nil{}: Unit
    case Con{lock,rest}:
      Sigma<&2,&2,ValidLock<root_authority,honest,events,lock>,_ =>
        ValidTable(root_authority,honest,events,rest)>

def valid_at(+root_authority: K.Authority, +honest: List<&2,Nat>,
    +events: List<&2,VoteEvent>, +lock: FinalityLock,
    +locks: List<&2,FinalityLock>, table: ValidTable(root_authority,honest,events,locks),
    member: Member(FinalityLock,lock,locks)) ->
    ValidLock<root_authority,honest,events,lock>:
  match locks:
    case Nil{}: Empty.absurd(ValidLock<root_authority,honest,events,lock>,member)
    case Con{head,rest}:
      (head_valid,rest_valid) = table
      match member:
        case Inl{same}:
          %Equal.sym(FinalityLock,lock,head,same) : ValidLock<root_authority,honest,events,_>
          head_valid
        case Inr{tail}:
          valid_at(root_authority,honest,events,lock,rest,rest_valid,tail)

def ReadyTable(+events: List<&2,VoteEvent>, +locks: List<&2,FinalityLock>) -> Data:
  match events:
    case Nil{}: Unit
    case Con{event,rest}:
      Sigma<&2,&2,Q3Ready(locks,event),_ => ReadyTable(rest,locks)>

def ready_at(+events: List<&2,VoteEvent>, +locks: List<&2,FinalityLock>,
    +event: VoteEvent, table: ReadyTable(events,locks),
    member: Member(VoteEvent,event,events)) -> Q3Ready(locks,event):
  match events:
    case Nil{}: Empty.absurd(Q3Ready(locks,event),member)
    case Con{head,rest}:
      (head_ready,rest_ready) = table
      match member:
        case Inl{same}:
          %Equal.sym(VoteEvent,event,head,same) : Q3Ready(locks,_)
          head_ready
        case Inr{tail}:
          ready_at(rest,locks,event,rest_ready,tail)

# A finite table records either the certified rank relation or the concrete
# reason why that pair is outside the honest same-signer chronological case.
type ClassifiedPair<-honest: List<&2,Nat>, -older: VoteEvent,
    -newer: VoteEvent> is Data:
  Ranked{rank: RankLE(older,newer)}
  OlderDishonest{absent: {K.contains(honest,VoteEvent.signer(older)) == False{} : Bool}}
  OtherSigner{different: {K.nat_eq(VoteEvent.signer(older),VoteEvent.signer(newer)) == False{} : Bool}}
  ReverseTime{later: Q.Le(1n+VoteEvent.time(newer),VoteEvent.time(older))}

def HistoryColumns(+honest: List<&2,Nat>, +older: VoteEvent,
    +newers: List<&2,VoteEvent>) -> Data:
  match newers:
    case Nil{}: Unit
    case Con{newer,rest}:
      Sigma<&2,&2,ClassifiedPair<honest,older,newer>,_ =>
        HistoryColumns(honest,older,rest)>

def HistoryTable(+honest: List<&2,Nat>, +olders: List<&2,VoteEvent>,
    +newers: List<&2,VoteEvent>) -> Data:
  match olders:
    case Nil{}: Unit
    case Con{older,rest}:
      Sigma<&2,&2,HistoryColumns(honest,older,newers),_ =>
        HistoryTable(honest,rest,newers)>

def classified_column_at(+honest: List<&2,Nat>, +older: VoteEvent,
    +newer: VoteEvent, +newers: List<&2,VoteEvent>,
    columns: HistoryColumns(honest,older,newers),
    member: Member(VoteEvent,newer,newers)) -> ClassifiedPair<honest,older,newer>:
  match newers:
    case Nil{}: Empty.absurd(ClassifiedPair<honest,older,newer>,member)
    case Con{head,rest}:
      (head_classified,rest_columns) = columns
      match member:
        case Inl{same}:
          %Equal.sym(VoteEvent,newer,head,same) : ClassifiedPair<honest,older,_>
          head_classified
        case Inr{tail}:
          classified_column_at(honest,older,newer,rest,rest_columns,tail)

def classified_at(+honest: List<&2,Nat>, +older: VoteEvent,
    +newer: VoteEvent, +olders: List<&2,VoteEvent>, +newers: List<&2,VoteEvent>,
    table: HistoryTable(honest,olders,newers),
    older_member: Member(VoteEvent,older,olders),
    newer_member: Member(VoteEvent,newer,newers)) -> ClassifiedPair<honest,older,newer>:
  match olders:
    case Nil{}: Empty.absurd(ClassifiedPair<honest,older,newer>,older_member)
    case Con{head,rest}:
      (head_columns,rest_table) = table
      match older_member:
        case Inl{same}:
          result = classified_column_at(honest,head,newer,newers,head_columns,newer_member)
          %Equal.sym(VoteEvent,older,head,same) : ClassifiedPair<honest,_,newer>
          result
        case Inr{tail}:
          classified_at(honest,older,newer,rest,newers,rest_table,tail,newer_member)

def classified_rank(+honest: List<&2,Nat>, +older: VoteEvent,
    +newer: VoteEvent, +signer: Nat,
    honest_member: {K.contains(honest,signer) == True{} : Bool},
    older_same: {VoteEvent.signer(older) == signer : Nat},
    newer_same: {VoteEvent.signer(newer) == signer : Nat},
    time_order: Q.Le(VoteEvent.time(older),VoteEvent.time(newer)),
    classified: ClassifiedPair<honest,older,newer>) -> RankLE(older,newer):
  match classified:
    case Ranked{rank}: rank
    case OlderDishonest{absent}:
      mapped = Equal.cong(Nat,Bool,x => K.contains(honest,x),VoteEvent.signer(older),signer,older_same)
      present = C.equality_trans(Bool,K.contains(honest,VoteEvent.signer(older)),K.contains(honest,signer),True{},mapped,honest_member)
      false_true = C.equality_trans(Bool,False{},K.contains(honest,VoteEvent.signer(older)),True{},Equal.sym(Bool,K.contains(honest,VoteEvent.signer(older)),False{},absent),present)
      Empty.absurd(RankLE(older,newer),Q.false_empty(false_true))
    case OtherSigner{different}:
      same_signer = C.equality_trans(Nat,VoteEvent.signer(older),signer,VoteEvent.signer(newer),older_same,Equal.sym(Nat,VoteEvent.signer(newer),signer,newer_same))
      mapped = Equal.cong(Nat,Bool,x => K.nat_eq(VoteEvent.signer(older),x),VoteEvent.signer(older),VoteEvent.signer(newer),same_signer)
      equal_true = C.equality_trans(Bool,K.nat_eq(VoteEvent.signer(older),VoteEvent.signer(newer)),K.nat_eq(VoteEvent.signer(older),VoteEvent.signer(older)),True{},Equal.sym(Bool,K.nat_eq(VoteEvent.signer(older),VoteEvent.signer(older)),K.nat_eq(VoteEvent.signer(older),VoteEvent.signer(newer)),mapped),Q.nat_eq_refl(VoteEvent.signer(older)))
      false_true = C.equality_trans(Bool,False{},K.nat_eq(VoteEvent.signer(older),VoteEvent.signer(newer)),True{},Equal.sym(Bool,K.nat_eq(VoteEvent.signer(older),VoteEvent.signer(newer)),False{},different),equal_true)
      Empty.absurd(RankLE(older,newer),Q.false_empty(false_true))
    case ReverseTime{later}:
      Empty.absurd(RankLE(older,newer),Q.le_not_gt(VoteEvent.time(older),VoteEvent.time(newer),time_order,later))

def history_rank(+honest: List<&2,Nat>, +events: List<&2,VoteEvent>,
    +table: HistoryTable(honest,events,events),
    +older: VoteEvent, +newer: VoteEvent,
    older_stored: Member(VoteEvent,older,events),
    newer_stored: Member(VoteEvent,newer,events), +signer: Nat,
    honest_member: {K.contains(honest,signer) == True{} : Bool},
    older_same: {VoteEvent.signer(older) == signer : Nat},
    newer_same: {VoteEvent.signer(newer) == signer : Nat},
    time_order: Q.Le(VoteEvent.time(older),VoteEvent.time(newer))) -> RankLE(older,newer):
  classified_rank(honest,older,newer,signer,honest_member,older_same,newer_same,
    time_order,classified_at(honest,older,newer,events,events,table,older_stored,newer_stored))

# The main proof follows below. Its recursive call is on a strictly smaller
# sum of certificate-root heights.

def catchup_ready_case(+fuel: Nat, +events: List<&2,VoteEvent>,
    +locks: List<&2,FinalityLock>,
    +older_lock: FinalityLock, +newer_lock: FinalityLock,
    recurse: @+pivot: FinalityLock ->
      @+pivot_member: Member(FinalityLock,pivot,locks) ->
      @+smaller: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(older_lock)),
        List.length(&2,Nat,FinalityLock.root(pivot))),fuel) ->
      C.Compatible(FinalityLock.locked(older_lock),FinalityLock.locked(pivot)),
    +older_event: VoteEvent, +newer_event: VoteEvent,
    +older_covers: C.Prefix(FinalityLock.locked(older_lock),VoteEvent.q2(older_event)),
    newer_covers: C.Prefix(FinalityLock.locked(newer_lock),VoteEvent.q2(newer_event)),
    newer_below_root: Q.Le(1n+List.length(&2,Nat,VoteEvent.target(newer_event)),List.length(&2,Nat,FinalityLock.root(newer_lock))),
    +height: Q.Le(List.length(&2,Nat,VoteEvent.q2(older_event)),List.length(&2,Nat,VoteEvent.q3(newer_event))),
    pair_bound: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(older_lock)),List.length(&2,Nat,FinalityLock.root(newer_lock))),1n+fuel),
    readiness: Q3Ready(locks,newer_event)) ->
    C.Compatible(FinalityLock.locked(older_lock),FinalityLock.locked(newer_lock)):
  match readiness:
    case Inl{at_genesis}:
      locked_height = Q.le_trans(List.length(&2,Nat,FinalityLock.locked(older_lock)),
        List.length(&2,Nat,VoteEvent.q2(older_event)),
        List.length(&2,Nat,VoteEvent.q3(newer_event)),
        C.prefix_length(FinalityLock.locked(older_lock),VoteEvent.q2(older_event),older_covers),height)
      q3_zero = Equal.cong(C.Path,Nat,x => List.length(&2,Nat,x),VoteEvent.q3(newer_event),[],at_genesis)
      locked_zero : Q.Le(List.length(&2,Nat,FinalityLock.locked(older_lock)),0n) = %q3_zero : Q.Le(List.length(&2,Nat,FinalityLock.locked(older_lock)),_); locked_height
      locked_empty = path_empty(FinalityLock.locked(older_lock),locked_zero)
      old_below_q3 = prefix_from_empty(FinalityLock.locked(older_lock),VoteEvent.q3(newer_event),locked_empty)
      prior : C.Compatible(FinalityLock.locked(older_lock),VoteEvent.q3(newer_event)) = Inl{old_below_q3}
      C.catchup_case(FinalityLock.locked(older_lock),FinalityLock.locked(newer_lock),
        VoteEvent.q2(older_event),VoteEvent.q2(newer_event),VoteEvent.q3(newer_event),
        older_covers,newer_covers,VoteEvent.q3_below_q2(newer_event),height,prior)
    case Inr{accepted}:
      (+pivot,(+pivot_member,(pivot_locked,pivot_bound))) = accepted
      smaller = smaller_sum(FinalityLock.root(older_lock),FinalityLock.root(pivot),
        FinalityLock.root(newer_lock),VoteEvent.target(newer_event),fuel,
        pivot_bound,newer_below_root,pair_bound)
      compared = recurse(pivot,pivot_member,smaller)
      prior : C.Compatible(FinalityLock.locked(older_lock),VoteEvent.q3(newer_event)) = %pivot_locked : C.Compatible(FinalityLock.locked(older_lock),_); compared
      C.catchup_case(FinalityLock.locked(older_lock),FinalityLock.locked(newer_lock),
        VoteEvent.q2(older_event),VoteEvent.q2(newer_event),VoteEvent.q3(newer_event),
        older_covers,newer_covers,VoteEvent.q3_below_q2(newer_event),height,prior)

def ordered_agreement(+fuel: Nat, +events: List<&2,VoteEvent>,
    +locks: List<&2,FinalityLock>,
    +readiness: ReadyTable(events,locks),
    +older_lock: FinalityLock, +newer_lock: FinalityLock,
    recurse: @+pivot: FinalityLock ->
      @+pivot_member: Member(FinalityLock,pivot,locks) ->
      @+smaller: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(older_lock)),
        List.length(&2,Nat,FinalityLock.root(pivot))),fuel) ->
      C.Compatible(FinalityLock.locked(older_lock),FinalityLock.locked(pivot)),
    +older_event: VoteEvent, +newer_event: VoteEvent,
    newer_stored: Member(VoteEvent,newer_event,events),
    older_covers: C.Prefix(FinalityLock.locked(older_lock),VoteEvent.q2(older_event)),
    newer_covers: C.Prefix(FinalityLock.locked(newer_lock),VoteEvent.q2(newer_event)),
    newer_below_root: Q.Le(1n+List.length(&2,Nat,VoteEvent.target(newer_event)),List.length(&2,Nat,FinalityLock.root(newer_lock))),
    pair_bound: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(older_lock)),List.length(&2,Nat,FinalityLock.root(newer_lock))),1n+fuel),
    rank: RankLE(older_event,newer_event)) ->
    C.Compatible(FinalityLock.locked(older_lock),FinalityLock.locked(newer_lock)):
  match rank:
    case Inl{q2_retained}:
      older_below_new = C.prefix_trans(FinalityLock.locked(older_lock),
        VoteEvent.q2(older_event),VoteEvent.q2(newer_event),older_covers,q2_retained)
      C.compare_under_tip(FinalityLock.locked(older_lock),FinalityLock.locked(newer_lock),
        VoteEvent.q2(newer_event),older_below_new,newer_covers)
    case Inr{catchup}:
      (q3_advanced,height) = catchup
      catchup_ready_case(fuel,events,locks,older_lock,newer_lock,recurse,
        older_event,newer_event,older_covers,newer_covers,newer_below_root,height,
        pair_bound,ready_at(events,locks,newer_event,readiness,newer_stored))

def agreement_time_case(+fuel: Nat, +honest: List<&2,Nat>,
    +events: List<&2,VoteEvent>, +locks: List<&2,FinalityLock>,
    +history: HistoryTable(honest,events,events),
    +readiness: ReadyTable(events,locks),
    +left_lock: FinalityLock, +right_lock: FinalityLock,
    +left_member: Member(FinalityLock,left_lock,locks),
    +right_member: Member(FinalityLock,right_lock,locks),
    recurse: @+older: FinalityLock -> @+pivot: FinalityLock ->
      @+older_member: Member(FinalityLock,older,locks) ->
      @+pivot_member: Member(FinalityLock,pivot,locks) ->
      @+smaller: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(older)),
        List.length(&2,Nat,FinalityLock.root(pivot))),fuel) ->
      C.Compatible(FinalityLock.locked(older),FinalityLock.locked(pivot)),
    +signer: Nat, honest_member: {K.contains(honest,signer) == True{} : Bool},
    +left_event: VoteEvent, +right_event: VoteEvent,
    +left_stored: Member(VoteEvent,left_event,events),
    +right_stored: Member(VoteEvent,right_event,events),
    left_same: {VoteEvent.signer(left_event) == signer : Nat},
    right_same: {VoteEvent.signer(right_event) == signer : Nat},
    left_covers: C.Prefix(FinalityLock.locked(left_lock),VoteEvent.q2(left_event)),
    right_covers: C.Prefix(FinalityLock.locked(right_lock),VoteEvent.q2(right_event)),
    left_below: Q.Le(1n+List.length(&2,Nat,VoteEvent.target(left_event)),List.length(&2,Nat,FinalityLock.root(left_lock))),
    right_below: Q.Le(1n+List.length(&2,Nat,VoteEvent.target(right_event)),List.length(&2,Nat,FinalityLock.root(right_lock))),
    pair_bound: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(left_lock)),List.length(&2,Nat,FinalityLock.root(right_lock))),1n+fuel),
    order: Either<&2,&2,Q.Le(VoteEvent.time(left_event),VoteEvent.time(right_event)),Q.Le(VoteEvent.time(right_event),VoteEvent.time(left_event))>) ->
    C.Compatible(FinalityLock.locked(left_lock),FinalityLock.locked(right_lock)):
  match order:
    case Inl{left_first}:
      ordered_agreement(fuel,events,locks,readiness,left_lock,right_lock,
        pivot => pivot_member => smaller => recurse(left_lock,pivot,left_member,pivot_member,smaller),
        left_event,right_event,right_stored,left_covers,right_covers,right_below,pair_bound,
        history_rank(honest,events,history,left_event,right_event,left_stored,right_stored,signer,
          honest_member,left_same,right_same,left_first))
    case Inr{right_first}:
      reversed_bound = swap_sum_bound(List.length(&2,Nat,FinalityLock.root(left_lock)),
        List.length(&2,Nat,FinalityLock.root(right_lock)),1n+fuel,pair_bound)
      reversed = ordered_agreement(fuel,events,locks,readiness,right_lock,left_lock,
        pivot => pivot_member => smaller => recurse(right_lock,pivot,right_member,pivot_member,smaller),
        right_event,left_event,left_stored,right_covers,left_covers,left_below,reversed_bound,
        history_rank(honest,events,history,right_event,left_event,right_stored,left_stored,signer,
          honest_member,right_same,left_same,right_first))
      compatible_sym(FinalityLock.locked(right_lock),FinalityLock.locked(left_lock),reversed)

def agreement_locations(+fuel: Nat, +honest: List<&2,Nat>,
    +events: List<&2,VoteEvent>, +locks: List<&2,FinalityLock>,
    +history: HistoryTable(honest,events,events),
    +readiness: ReadyTable(events,locks),
    +left_lock: FinalityLock, +right_lock: FinalityLock,
    left_member: Member(FinalityLock,left_lock,locks),
    right_member: Member(FinalityLock,right_lock,locks),
    recurse: @+older: FinalityLock -> @+pivot: FinalityLock ->
      @+older_member: Member(FinalityLock,older,locks) ->
      @+pivot_member: Member(FinalityLock,pivot,locks) ->
      @+smaller: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(older)),
        List.length(&2,Nat,FinalityLock.root(pivot))),fuel) ->
      C.Compatible(FinalityLock.locked(older),FinalityLock.locked(pivot)),
    +signer: Nat, honest_member: {K.contains(honest,signer) == True{} : Bool},
    left_location: Located<events,FinalityLock.locked(left_lock),FinalityLock.root(left_lock),signer>,
    right_location: Located<events,FinalityLock.locked(right_lock),FinalityLock.root(right_lock),signer>,
    pair_bound: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(left_lock)),List.length(&2,Nat,FinalityLock.root(right_lock))),1n+fuel)) ->
    C.Compatible(FinalityLock.locked(left_lock),FinalityLock.locked(right_lock)):
  Located{+left_event,+left_stored,+left_same,+left_covers,+left_below} = left_location
  Located{+right_event,+right_stored,+right_same,+right_covers,+right_below} = right_location
  agreement_time_case(fuel,honest,events,locks,history,readiness,left_lock,right_lock,
    left_member,right_member,recurse,signer,honest_member,left_event,right_event,
    left_stored,right_stored,left_same,right_same,left_covers,right_covers,
    left_below,right_below,pair_bound,le_total(VoteEvent.time(left_event),VoteEvent.time(right_event)))

def agreement_common(+fuel: Nat, +root_authority: K.Authority,
    +honest: List<&2,Nat>, +events: List<&2,VoteEvent>,
    +locks: List<&2,FinalityLock>,
    +history: HistoryTable(honest,events,events),
    +readiness: ReadyTable(events,locks),
    +left_lock: FinalityLock, +right_lock: FinalityLock,
    left_member: Member(FinalityLock,left_lock,locks),
    right_member: Member(FinalityLock,right_lock,locks),
    recurse: @+older: FinalityLock -> @+pivot: FinalityLock ->
      @+older_member: Member(FinalityLock,older,locks) ->
      @+pivot_member: Member(FinalityLock,pivot,locks) ->
      @+smaller: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(older)),
        List.length(&2,Nat,FinalityLock.root(pivot))),fuel) ->
      C.Compatible(FinalityLock.locked(older),FinalityLock.locked(pivot)),
    left_stored: Stored(events,FinalityLock.contributors(left_lock)),
    left_covers: Covers(FinalityLock.locked(left_lock),FinalityLock.contributors(left_lock)),
    left_below: BelowRoot(FinalityLock.root(left_lock),FinalityLock.contributors(left_lock)),
    right_stored: Stored(events,FinalityLock.contributors(right_lock)),
    right_covers: Covers(FinalityLock.locked(right_lock),FinalityLock.contributors(right_lock)),
    right_below: BelowRoot(FinalityLock.root(right_lock),FinalityLock.contributors(right_lock)),
    pair_bound: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(left_lock)),List.length(&2,Nat,FinalityLock.root(right_lock))),1n+fuel),
    common: Q.Common(K.Authority.members(root_authority),FinalityLock.signers(left_lock),FinalityLock.signers(right_lock),honest)) ->
    C.Compatible(FinalityLock.locked(left_lock),FinalityLock.locked(right_lock)):
  (+signer,(authority_member,(left_found,(right_found,honest_member)))) = common
  agreement_locations(fuel,honest,events,locks,history,readiness,left_lock,right_lock,
    left_member,right_member,recurse,signer,honest_member,
    locate(events,FinalityLock.locked(left_lock),FinalityLock.root(left_lock),
      FinalityLock.contributors(left_lock),signer,left_stored,left_covers,left_below,left_found),
    locate(events,FinalityLock.locked(right_lock),FinalityLock.root(right_lock),
      FinalityLock.contributors(right_lock),signer,right_stored,right_covers,right_below,right_found),
    pair_bound)

def agreement_valid_step(+fuel: Nat, +root_authority: K.Authority,
    +honest: List<&2,Nat>, +events: List<&2,VoteEvent>,
    +locks: List<&2,FinalityLock>,
    +history: HistoryTable(honest,events,events),
    +readiness: ReadyTable(events,locks),
    +left_lock: FinalityLock, +right_lock: FinalityLock,
    left_member: Member(FinalityLock,left_lock,locks),
    right_member: Member(FinalityLock,right_lock,locks),
    recurse: @+older: FinalityLock -> @+pivot: FinalityLock ->
      @+older_member: Member(FinalityLock,older,locks) ->
      @+pivot_member: Member(FinalityLock,pivot,locks) ->
      @+smaller: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(older)),
        List.length(&2,Nat,FinalityLock.root(pivot))),fuel) ->
      C.Compatible(FinalityLock.locked(older),FinalityLock.locked(pivot)),
    honest_quorum: {K.has_quorum(root_authority,honest) == True{} : Bool},
    pair_bound: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(left_lock)),List.length(&2,Nat,FinalityLock.root(right_lock))),1n+fuel),
    left_valid: ValidLock<root_authority,honest,events,left_lock>,
    right_valid: ValidLock<root_authority,honest,events,right_lock>) ->
    C.Compatible(FinalityLock.locked(left_lock),FinalityLock.locked(right_lock)):
  ValidLock{left_stored,left_covers,left_below,left_clean,left_quorum} = left_valid
  ValidLock{right_stored,right_covers,right_below,right_clean,right_quorum} = right_valid
  agreement_common(fuel,root_authority,honest,events,locks,history,readiness,
    left_lock,right_lock,left_member,right_member,recurse,
    left_stored,left_covers,left_below,right_stored,right_covers,right_below,
    pair_bound,
    R.reduced_authority_intersection(root_authority,FinalityLock.offenders(left_lock),
      FinalityLock.offenders(right_lock),FinalityLock.signers(left_lock),
      FinalityLock.signers(right_lock),honest,left_clean,right_clean,
      left_quorum,right_quorum,honest_quorum))

def agreement_zero_location(+left_lock: FinalityLock, +right_lock: FinalityLock,
    +events: List<&2,VoteEvent>, +signer: Nat,
    location: Located<events,FinalityLock.locked(left_lock),FinalityLock.root(left_lock),signer>,
    pair_bound: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(left_lock)),List.length(&2,Nat,FinalityLock.root(right_lock))),0n)) ->
    C.Compatible(FinalityLock.locked(left_lock),FinalityLock.locked(right_lock)):
  Located{event,stored,same,covers,below} = location
  +left_height = List.length(&2,Nat,FinalityLock.root(left_lock))
  +right_height = List.length(&2,Nat,FinalityLock.root(right_lock))
  left_zero = Q.le_trans(left_height,Nat.add(left_height,right_height),0n,
    Q.le_left(left_height,right_height),pair_bound)
  impossible = Q.le_trans(1n+List.length(&2,Nat,VoteEvent.target(event)),left_height,0n,below,left_zero)
  Empty.absurd(C.Compatible(FinalityLock.locked(left_lock),FinalityLock.locked(right_lock)),impossible)

def agreement_zero_common(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +events: List<&2,VoteEvent>,
    +left_lock: FinalityLock, +right_lock: FinalityLock,
    left_stored: Stored(events,FinalityLock.contributors(left_lock)),
    left_covers: Covers(FinalityLock.locked(left_lock),FinalityLock.contributors(left_lock)),
    left_below: BelowRoot(FinalityLock.root(left_lock),FinalityLock.contributors(left_lock)),
    pair_bound: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(left_lock)),List.length(&2,Nat,FinalityLock.root(right_lock))),0n),
    common: Q.Common(K.Authority.members(root_authority),FinalityLock.signers(left_lock),FinalityLock.signers(right_lock),honest)) ->
    C.Compatible(FinalityLock.locked(left_lock),FinalityLock.locked(right_lock)):
  (+signer,(authority_member,(left_found,(right_found,honest_member)))) = common
  agreement_zero_location(left_lock,right_lock,events,signer,
    locate(events,FinalityLock.locked(left_lock),FinalityLock.root(left_lock),
      FinalityLock.contributors(left_lock),signer,left_stored,left_covers,left_below,left_found),
    pair_bound)

def agreement_zero_valid(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +events: List<&2,VoteEvent>,
    +left_lock: FinalityLock, +right_lock: FinalityLock,
    honest_quorum: {K.has_quorum(root_authority,honest) == True{} : Bool},
    pair_bound: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(left_lock)),List.length(&2,Nat,FinalityLock.root(right_lock))),0n),
    left_valid: ValidLock<root_authority,honest,events,left_lock>,
    right_valid: ValidLock<root_authority,honest,events,right_lock>) ->
    C.Compatible(FinalityLock.locked(left_lock),FinalityLock.locked(right_lock)):
  ValidLock{left_stored,left_covers,left_below,left_clean,left_quorum} = left_valid
  ValidLock{right_stored,right_covers,right_below,right_clean,right_quorum} = right_valid
  agreement_zero_common(root_authority,honest,events,left_lock,right_lock,
    left_stored,left_covers,left_below,pair_bound,
    R.reduced_authority_intersection(root_authority,FinalityLock.offenders(left_lock),
      FinalityLock.offenders(right_lock),FinalityLock.signers(left_lock),
      FinalityLock.signers(right_lock),honest,left_clean,right_clean,
      left_quorum,right_quorum,honest_quorum))

def agreement_fuel(+fuel: Nat, +root_authority: K.Authority,
    +honest: List<&2,Nat>, +events: List<&2,VoteEvent>,
    +locks: List<&2,FinalityLock>,
    +validity: ValidTable(root_authority,honest,events,locks),
    +history: HistoryTable(honest,events,events),
    +readiness: ReadyTable(events,locks),
    +left_lock: FinalityLock, +right_lock: FinalityLock,
    left_member: Member(FinalityLock,left_lock,locks),
    right_member: Member(FinalityLock,right_lock,locks),
    +honest_quorum: {K.has_quorum(root_authority,honest) == True{} : Bool},
    pair_bound: Q.Le(Nat.add(List.length(&2,Nat,FinalityLock.root(left_lock)),List.length(&2,Nat,FinalityLock.root(right_lock))),fuel),
    left_valid: ValidLock<root_authority,honest,events,left_lock>,
    right_valid: ValidLock<root_authority,honest,events,right_lock>) ->
    C.Compatible(FinalityLock.locked(left_lock),FinalityLock.locked(right_lock)):
  match fuel:
    case 0n:
      agreement_zero_valid(root_authority,honest,events,left_lock,right_lock,
        honest_quorum,pair_bound,left_valid,right_valid)
    case 1n+fuel:
      agreement_valid_step(fuel,root_authority,honest,events,locks,history,readiness,
        left_lock,right_lock,left_member,right_member,
        older => pivot => older_member => pivot_member => smaller =>
          agreement_fuel(fuel,root_authority,honest,events,locks,validity,history,readiness,
            older,pivot,older_member,pivot_member,honest_quorum,smaller,
            valid_at(root_authority,honest,events,older,locks,validity,older_member),
            valid_at(root_authority,honest,events,pivot,locks,validity,pivot_member)),
        honest_quorum,pair_bound,left_valid,right_valid)

# Reachable-state safety core: any two accepted certificates are compatible.
# The three oracles are exactly the invariants preserved by the projected
# transitions: accepted-certificate validity, honest signing history, and Q3
# coverage by an earlier accepted certificate.
def accepted_locks_agree(+root_authority: K.Authority,
    +honest: List<&2,Nat>, +events: List<&2,VoteEvent>,
    +locks: List<&2,FinalityLock>,
    +validity: ValidTable(root_authority,honest,events,locks),
    +history: HistoryTable(honest,events,events),
    +readiness: ReadyTable(events,locks),
    +left_lock: FinalityLock, +right_lock: FinalityLock,
    +left_member: Member(FinalityLock,left_lock,locks),
    +right_member: Member(FinalityLock,right_lock,locks),
    honest_quorum: {K.has_quorum(root_authority,honest) == True{} : Bool}) ->
    C.Compatible(FinalityLock.locked(left_lock),FinalityLock.locked(right_lock)):
  +fuel = Nat.add(List.length(&2,Nat,FinalityLock.root(left_lock)),
    List.length(&2,Nat,FinalityLock.root(right_lock)))
  agreement_fuel(fuel,root_authority,honest,events,locks,validity,history,readiness,
    left_lock,right_lock,left_member,right_member,honest_quorum,Q.le_refl(fuel),
    valid_at(root_authority,honest,events,left_lock,locks,validity,left_member),
    valid_at(root_authority,honest,events,right_lock,locks,validity,right_member))
