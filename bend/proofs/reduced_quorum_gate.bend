import Base
import ../model/kernel.bend as K
import ./quorum_gates.bend as Q

def nat_trans(+a: Nat, +b: Nat, +c: Nat, first: {a == b : Nat}, second: {b == c : Nat}) -> {a == c : Nat}:
  %second : {a == _ : Nat}
  first

def le_transport(+a: Nat, +a2: Nat, +b: Nat, +b2: Nat, left: {a == a2 : Nat}, right: {b == b2 : Nat}, proof: Q.Le(a2,b2)) -> Q.Le(a,b):
  %Equal.sym(Nat,a,a2,left) : Q.Le(_,b)
  %Equal.sym(Nat,b,b2,right) : Q.Le(a2,_)
  proof

# No honest stake row is removed by the verified evidence set.
def Clean(authority: List<&2,Nat>, +offenders: List<&2,Nat>, +honest: List<&2,Nat>) -> Data:
  match authority:
    case Nil{}: Unit
    case Con{id,rest}:
      Sigma<&2,&2,{K.contains(offenders,id) && K.contains(honest,id) == False{} : Bool},_ =>
        Clean(rest,offenders,honest)>

def mask_partition(+removed: Bool) -> {Nat.add(Q.mask(Bool.not(removed)),Q.mask(removed)) == 1n : Nat}:
  match removed:
    case False{}: {==}
    case True{}: {==}

def partition_total(+authority: List<&2,Nat>, +offenders: List<&2,Nat>) -> {List.length(&2,Nat,authority) == Nat.add(Q.rows(authority,Q.Not{Q.In{offenders}}),Q.rows(authority,Q.In{offenders})) : Nat}:
  match authority:
    case Nil{}: {==}
    case Con{id,rest}:
      +head_retained = Q.mask(Bool.not(K.contains(offenders,id)))
      +head_removed = Q.mask(K.contains(offenders,id))
      +tail_retained = Q.rows(rest,Q.Not{Q.In{offenders}})
      +tail_removed = Q.rows(rest,Q.In{offenders})
      +tail_sum = Nat.add(tail_retained,tail_removed)
      tail = partition_total(rest,offenders)
      head = mask_partition(K.contains(offenders,id))
      first = Equal.cong(Nat,Nat,x => Nat.add(1n,x),List.length(&2,Nat,rest),tail_sum,tail)
      second = Equal.cong(Nat,Nat,x => Nat.add(x,tail_sum),1n,Nat.add(head_retained,head_removed),Equal.sym(Nat,Nat.add(head_retained,head_removed),1n,head))
      nat_trans(1n+List.length(&2,Nat,rest),1n+tail_sum,Nat.add(Nat.add(head_retained,tail_retained),Nat.add(head_removed,tail_removed)),first,nat_trans(1n+tail_sum,Nat.add(Nat.add(head_retained,head_removed),tail_sum),Nat.add(Nat.add(head_retained,tail_retained),Nat.add(head_removed,tail_removed)),second,Q.shuffle(head_retained,head_removed,tail_retained,tail_removed)))

def fill_mask(+removed: Bool, +selected: Bool) -> {Q.mask(selected || removed) == Nat.add(Q.mask(Bool.not(removed) && selected),Q.mask(removed)) : Nat}:
  match removed selected:
    case False{} False{}: {==}
    case False{} True{}: Equal.sym(Nat,Nat.add(1n,0n),1n,Q.add_zero(1n))
    case True{} False{}: {==}
    case True{} True{}: {==}

def fill_rows(+authority: List<&2,Nat>, +offenders: List<&2,Nat>, +signers: List<&2,Nat>) -> {Q.rows(authority,Q.Either{Q.In{signers},Q.In{offenders}}) == Nat.add(Q.rows(authority,Q.Both{Q.Not{Q.In{offenders}},Q.In{signers}}),Q.rows(authority,Q.In{offenders})) : Nat}:
  match authority:
    case Nil{}: {==}
    case Con{id,rest}:
      +head_union = Q.mask(K.contains(signers,id) || K.contains(offenders,id))
      +head_retained = Q.mask(Bool.not(K.contains(offenders,id)) && K.contains(signers,id))
      +head_removed = Q.mask(K.contains(offenders,id))
      +tail_union = Q.rows(rest,Q.Either{Q.In{signers},Q.In{offenders}})
      +tail_retained = Q.rows(rest,Q.Both{Q.Not{Q.In{offenders}},Q.In{signers}})
      +tail_removed = Q.rows(rest,Q.In{offenders})
      +tail_pair = Nat.add(tail_retained,tail_removed)
      tail = fill_rows(rest,offenders,signers)
      head = fill_mask(K.contains(offenders,id),K.contains(signers,id))
      first = Equal.cong(Nat,Nat,x => Nat.add(head_union,x),tail_union,tail_pair,tail)
      second = Equal.cong(Nat,Nat,x => Nat.add(x,tail_pair),head_union,Nat.add(head_retained,head_removed),head)
      nat_trans(Nat.add(head_union,tail_union),Nat.add(head_union,tail_pair),Nat.add(Nat.add(head_retained,tail_retained),Nat.add(head_removed,tail_removed)),first,nat_trans(Nat.add(head_union,tail_pair),Nat.add(Nat.add(head_retained,head_removed),tail_pair),Nat.add(Nat.add(head_retained,tail_retained),Nat.add(head_removed,tail_removed)),second,Q.shuffle(head_retained,head_removed,tail_retained,tail_removed)))

def after_total_case(+id: Nat, +filtered: List<&2,Nat>, +tail: Nat, +removed: Bool, recurse: {List.length(&2,Nat,filtered) == tail : Nat}) -> {List.length(&2,Nat,List.append(&2,Nat,Bool.pick(List<&2,Nat>,removed,[],[id]),filtered)) == Nat.add(Q.mask(Bool.not(removed)),tail) : Nat}:
  match removed:
    case False{}:
      %recurse : {1n+List.length(&2,Nat,filtered) == 1n+_ : Nat}
      {==}
    case True{}:
      recurse

def after_total(+authority: List<&2,Nat>, +offenders: List<&2,Nat>) -> {List.length(&2,Nat,K.after_evidence_go(authority,offenders)) == Q.rows(authority,Q.Not{Q.In{offenders}}) : Nat}:
  match authority:
    case Nil{}: {==}
    case Con{id,rest}:
      after_total_case(id,K.after_evidence_go(rest,offenders),Q.rows(rest,Q.Not{Q.In{offenders}}),K.contains(offenders,id),after_total(rest,offenders))

def after_selected_case(+id: Nat, +filtered: List<&2,Nat>, +tail: Nat, +signers: List<&2,Nat>, +removed: Bool, recurse: {Q.selected(filtered,signers) == tail : Nat}) -> {Q.selected(List.append(&2,Nat,Bool.pick(List<&2,Nat>,removed,[],[id]),filtered),signers) == Nat.add(Q.mask(Bool.not(removed) && K.contains(signers,id)),tail) : Nat}:
  match removed:
    case False{}:
      %recurse : {Nat.add(Q.mask(K.contains(signers,id)),Q.selected(filtered,signers)) == Nat.add(Q.mask(K.contains(signers,id)),_) : Nat}
      {==}
    case True{}:
      recurse

def after_selected(+authority: List<&2,Nat>, +offenders: List<&2,Nat>, +signers: List<&2,Nat>) -> {Q.selected(K.after_evidence_go(authority,offenders),signers) == Q.rows(authority,Q.Both{Q.Not{Q.In{offenders}},Q.In{signers}}) : Nat}:
  match authority:
    case Nil{}: {==}
    case Con{id,rest}:
      after_selected_case(id,K.after_evidence_go(rest,offenders),Q.rows(rest,Q.Both{Q.Not{Q.In{offenders}},Q.In{signers}}),signers,K.contains(offenders,id),after_selected(rest,offenders,signers))

def reduced_strict(+root: K.Authority, +offenders: List<&2,Nat>, +signers: List<&2,Nat>, quorum: {K.has_quorum(K.after_evidence(root,offenders),signers) == True{} : Bool}) -> Q.Le(1n+Nat.mul(2n,Q.rows(K.Authority.members(root),Q.Not{Q.In{offenders}})),Nat.mul(3n,Q.rows(K.Authority.members(root),Q.Both{Q.Not{Q.In{offenders}},Q.In{signers}}))):
  strict = Q.quorum_strict(K.after_evidence(root,offenders),signers,quorum)
  rewritten_total : Q.Le(1n+Nat.mul(2n,Q.rows(K.Authority.members(root),Q.Not{Q.In{offenders}})),Nat.mul(3n,Q.selected(K.after_evidence_go(K.Authority.members(root),offenders),signers))) = %after_total(K.Authority.members(root),offenders) : Q.Le(1n+Nat.mul(2n,_),Nat.mul(3n,Q.selected(K.after_evidence_go(K.Authority.members(root),offenders),signers))); strict
  %after_selected(K.Authority.members(root),offenders,signers) : Q.Le(1n+Nat.mul(2n,Q.rows(K.Authority.members(root),Q.Not{Q.In{offenders}})),Nat.mul(3n,_))
  rewritten_total

def two_three(+amount: Nat) -> Q.Le(Nat.mul(2n,amount),Nat.mul(3n,amount)):
  %Equal.sym(Nat,Nat.mul(2n,amount),Nat.add(amount,amount),Q.twice(amount)) : Q.Le(_,Nat.mul(3n,amount))
  %Equal.sym(Nat,Nat.mul(3n,amount),Nat.add(Nat.add(amount,amount),amount),Q.thrice(amount)) : Q.Le(Nat.add(amount,amount),_)
  Q.le_left(Nat.add(amount,amount),amount)

def grow_strict(+total: Nat, +selected: Nat, +removed: Nat, strict: Q.Le(1n+Nat.mul(2n,total),Nat.mul(3n,selected))) -> Q.Le(1n+Nat.mul(2n,Nat.add(total,removed)),Nat.mul(3n,Nat.add(selected,removed))):
  %Equal.sym(Nat,Nat.mul(2n,Nat.add(total,removed)),Nat.add(Nat.mul(2n,total),Nat.mul(2n,removed)),Q.mul_right_sum(2n,total,removed)) : Q.Le(1n+_,Nat.mul(3n,Nat.add(selected,removed)))
  %Equal.sym(Nat,Nat.mul(3n,Nat.add(selected,removed)),Nat.add(Nat.mul(3n,selected),Nat.mul(3n,removed)),Q.mul_right_sum(3n,selected,removed)) : Q.Le(1n+Nat.add(Nat.mul(2n,total),Nat.mul(2n,removed)),_)
  Q.le_add(1n+Nat.mul(2n,total),Nat.mul(3n,selected),Nat.mul(2n,removed),Nat.mul(3n,removed),strict,two_three(removed))

def filled_strict(+root: K.Authority, +offenders: List<&2,Nat>, +signers: List<&2,Nat>, quorum: {K.has_quorum(K.after_evidence(root,offenders),signers) == True{} : Bool}) -> Q.Le(1n+Nat.mul(2n,K.total(root)),Nat.mul(3n,Q.rows(K.Authority.members(root),Q.Either{Q.In{signers},Q.In{offenders}}))):
  +members = K.Authority.members(root)
  +retained_total = Q.rows(members,Q.Not{Q.In{offenders}})
  +removed = Q.rows(members,Q.In{offenders})
  +retained_selected = Q.rows(members,Q.Both{Q.Not{Q.In{offenders}},Q.In{signers}})
  +filled_selected = Q.rows(members,Q.Either{Q.In{signers},Q.In{offenders}})
  strict = reduced_strict(root,offenders,signers,quorum)
  grown = grow_strict(retained_total,retained_selected,removed,strict)
  left = Equal.cong(Nat,Nat,x => 1n+Nat.mul(2n,x),K.total(root),Nat.add(retained_total,removed),partition_total(members,offenders))
  right = Equal.cong(Nat,Nat,x => Nat.mul(3n,x),filled_selected,Nat.add(retained_selected,removed),fill_rows(members,offenders,signers))
  le_transport(1n+Nat.mul(2n,K.total(root)),1n+Nat.mul(2n,Nat.add(retained_total,removed)),Nat.mul(3n,filled_selected),Nat.mul(3n,Nat.add(retained_selected,removed)),left,right,grown)

def and_false(+value: Bool) -> {value && False{} == False{} : Bool}:
  match value:
    case False{}: {==}
    case True{}: {==}

def or_false(+value: Bool) -> {value || False{} == value : Bool}:
  match value:
    case False{}: {==}
    case True{}: {==}

def unfill_test(+left: Bool, +right: Bool, +honest: Bool, +left_removed: Bool, +right_removed: Bool, left_clean: {left_removed && honest == False{} : Bool}, right_clean: {right_removed && honest == False{} : Bool}) -> {((left || left_removed) && (right || right_removed)) && honest == (left && right) && honest : Bool}:
  match honest left_removed right_removed:
    case False{} left_removed right_removed:
      %Equal.sym(Bool,(left && right) && False{},False{},and_false(left && right)) : {((left || left_removed) && (right || right_removed)) && False{} == _ : Bool}
      and_false((left || left_removed) && (right || right_removed))
    case True{} True{} right_removed:
      Empty.absurd({((left || left_removed) && (right || right_removed)) && honest == (left && right) && honest : Bool},Q.false_empty(Equal.sym(Bool,True{},False{},left_clean)))
    case True{} False{} True{}:
      Empty.absurd({((left || left_removed) && (right || right_removed)) && honest == (left && right) && honest : Bool},Q.false_empty(Equal.sym(Bool,True{},False{},right_clean)))
    case True{} False{} False{}:
      %or_false(left) : {((left || False{}) && (right || False{})) && True{} == (_ && right) && True{} : Bool}
      %or_false(right) : {((left || False{}) && (right || False{})) && True{} == ((left || False{}) && _) && True{} : Bool}
      {==}

def unfill_rows(+authority: List<&2,Nat>, +left: List<&2,Nat>, +right: List<&2,Nat>, +honest: List<&2,Nat>, +left_offenders: List<&2,Nat>, +right_offenders: List<&2,Nat>, left_clean: Clean(authority,left_offenders,honest), right_clean: Clean(authority,right_offenders,honest)) -> {Q.rows(authority,Q.Both{Q.Both{Q.Either{Q.In{left},Q.In{left_offenders}},Q.Either{Q.In{right},Q.In{right_offenders}}},Q.In{honest}}) == Q.rows(authority,Q.Both{Q.Both{Q.In{left},Q.In{right}},Q.In{honest}}) : Nat}:
  match authority:
    case Nil{}: {==}
    case Con{id,rest}:
      (left_here,left_rest) = left_clean
      (right_here,right_rest) = right_clean
      %unfill_rows(rest,left,right,honest,left_offenders,right_offenders,left_rest,right_rest) : {Q.rows(authority,Q.Both{Q.Both{Q.Either{Q.In{left},Q.In{left_offenders}},Q.Either{Q.In{right},Q.In{right_offenders}}},Q.In{honest}}) == Nat.add(Q.mask((K.contains(left,id) && K.contains(right,id)) && K.contains(honest,id)),_) : Nat}
      %unfill_test(K.contains(left,id),K.contains(right,id),K.contains(honest,id),K.contains(left_offenders,id),K.contains(right_offenders,id),left_here,right_here) : {Q.rows(authority,Q.Both{Q.Both{Q.Either{Q.In{left},Q.In{left_offenders}},Q.Either{Q.In{right},Q.In{right_offenders}}},Q.In{honest}}) == Nat.add(Q.mask(_),Q.rows(rest,Q.Both{Q.Both{Q.Either{Q.In{left},Q.In{left_offenders}},Q.Either{Q.In{right},Q.In{right_offenders}}},Q.In{honest}})) : Nat}
      {==}

# Gate 2: quorums under two independently evidence-reduced descendants of one
# parent authority still share honest stake when neither reduction removes an
# honest validator.
def reduced_authority_intersection(+root: K.Authority, +left_offenders: List<&2,Nat>, +right_offenders: List<&2,Nat>, +left: List<&2,Nat>, +right: List<&2,Nat>, +honest: List<&2,Nat>, left_clean: Clean(K.Authority.members(root),left_offenders,honest), right_clean: Clean(K.Authority.members(root),right_offenders,honest), left_quorum: {K.has_quorum(K.after_evidence(root,left_offenders),left) == True{} : Bool}, right_quorum: {K.has_quorum(K.after_evidence(root,right_offenders),right) == True{} : Bool}, honest_quorum: {K.has_quorum(root,honest) == True{} : Bool}) -> Q.Common(K.Authority.members(root),left,right,honest):
  +members : List<&2,Nat> = K.Authority.members(root)
  filled = Q.positive_from_not_zero(Q.rows(members,Q.Both{Q.Both{Q.Either{Q.In{left},Q.In{left_offenders}},Q.Either{Q.In{right},Q.In{right_offenders}}},Q.In{honest}}),zero => Q.triple_zero_impossible(members,Q.Either{Q.In{left},Q.In{left_offenders}},Q.Either{Q.In{right},Q.In{right_offenders}},Q.In{honest},filled_strict(root,left_offenders,left,left_quorum),filled_strict(root,right_offenders,right,right_quorum),Q.quorum_strict(root,honest,honest_quorum),zero))
  actual : Q.Le(1n,Q.rows(members,Q.Both{Q.Both{Q.In{left},Q.In{right}},Q.In{honest}})) = %unfill_rows(members,left,right,honest,left_offenders,right_offenders,left_clean,right_clean) : Q.Le(1n,_); filled
  Q.common_from_witness(members,left,right,honest,Q.rows_witness(members,Q.Both{Q.Both{Q.In{left},Q.In{right}},Q.In{honest}},actual))
