import Base
import ./quorum_gates.bend as Q

# Concrete ancestry for the proof kernel. Paths run from Genesis to the target.
def Path() -> Data:
  List<&2,Nat>

def Prefix(ancestor: Path, descendant: Path) -> Data:
  match ancestor descendant:
    case Nil{} descendant: Unit
    case Con{head,tail} Nil{}: Empty
    case Con{head,tail} Con{other,rest}:
      Sigma<&2,&2,{head == other : Nat},_ => Prefix(tail,rest)>

def Compatible(left: Path, right: Path) -> Data:
  Either<&2,&2,Prefix(left,right),Prefix(right,left)>

def equality_trans(-A: Type, first: A, middle: A, last: A, first_middle: {first == middle : A}, middle_last: {middle == last : A}) -> {first == last : A}:
  %middle_last : {first == _ : A}
  first_middle

def prefix_refl(+path: Path) -> Prefix(path,path):
  match path:
    case Nil{}: Unit{}
    case Con{head,tail}: (Q.refl(Nat,head),prefix_refl(tail))

def prefix_trans(+first: Path, +second: Path, +third: Path, first_second: Prefix(first,second), second_third: Prefix(second,third)) -> Prefix(first,third):
  match first second third:
    case Nil{} second third: Unit{}
    case Con{head,tail} Nil{} third: Empty.absurd(Prefix(first,third),first_second)
    case Con{head,tail} Con{middle,middle_tail} Nil{}: Empty.absurd(Prefix(first,third),second_third)
    case Con{head,tail} Con{middle,middle_tail} Con{last,last_tail}:
      (head_middle,tail_middle) = first_second
      (middle_last,middle_last_tail) = second_third
      (equality_trans(Nat,head,middle,last,head_middle,middle_last),prefix_trans(tail,middle_tail,last_tail,tail_middle,middle_last_tail))

def lift_comparison(+left_head: Nat, +right_head: Nat, +left_tail: Path, +right_tail: Path, head_equal: {left_head == right_head : Nat}, comparison: Compatible(left_tail,right_tail)) -> Compatible(left_head <> left_tail,right_head <> right_tail):
  match comparison:
    case Inl{forward}: Inl{(head_equal,forward)}
    case Inr{backward}: Inr{(Equal.sym(Nat,left_head,right_head,head_equal),backward)}

def prefixes_comparable(+left: Path, +right: Path, +tip: Path, left_tip: Prefix(left,tip), right_tip: Prefix(right,tip)) -> Compatible(left,right):
  match left right tip:
    case Nil{} right tip: Inl{Unit{}}
    case Con{left_head,left_tail} Nil{} tip: Inr{Unit{}}
    case Con{left_head,left_tail} Con{right_head,right_tail} Nil{}:
      Empty.absurd(Compatible(left,right),left_tip)
    case Con{left_head,left_tail} Con{right_head,right_tail} Con{tip_head,tip_tail}:
      (left_equal,left_rest) = left_tip
      (right_equal,right_rest) = right_tip
      head_equal : {left_head == right_head : Nat} = %Equal.sym(Nat,right_head,tip_head,right_equal) : {left_head == _ : Nat}; left_equal
      lift_comparison(left_head,right_head,left_tail,right_tail,head_equal,prefixes_comparable(left_tail,right_tail,tip_tail,left_rest,right_rest))

def prefix_length(+ancestor: Path, +descendant: Path, prefix: Prefix(ancestor,descendant)) -> Q.Le(List.length(&2,Nat,ancestor),List.length(&2,Nat,descendant)):
  match ancestor descendant:
    case Nil{} descendant: Unit{}
    case Con{head,tail} Nil{}: Empty.absurd(Q.Le(List.length(&2,Nat,ancestor),0n),prefix)
    case Con{head,tail} Con{other,rest}:
      (equal,next) = prefix
      prefix_length(tail,rest,next)

def le_antisymm(+left: Nat, +right: Nat, forward: Q.Le(left,right), backward: Q.Le(right,left)) -> {left == right : Nat}:
  match left right:
    case 0n 0n: {==}
    case 0n 1n+right: Empty.absurd({0n == 1n+right : Nat},backward)
    case 1n+left 0n: Empty.absurd({1n+left == 0n : Nat},forward)
    case 1n+left 1n+right:
      Equal.cong(Nat,Nat,x => 1n+x,left,right,le_antisymm(left,right,forward,backward))

def is_zero(n: Nat) -> Bool:
  match n:
    case 0n: True{}
    case 1n+n: False{}

def zero_successor_empty(+n: Nat, equality: {0n == 1n+n : Nat}) -> Empty:
  different = Equal.cong(Nat,Bool,is_zero,0n,1n+n,equality)
  Q.false_empty(Equal.sym(Bool,True{},False{},different))

def predecessor(n: Nat) -> Nat:
  match n:
    case 0n: 0n
    case 1n+n: n

def successor_injective(+left: Nat, +right: Nat, equality: {1n+left == 1n+right : Nat}) -> {left == right : Nat}:
  Equal.cong(Nat,Nat,predecessor,1n+left,1n+right,equality)

def prefix_same_length(+ancestor: Path, +descendant: Path, prefix: Prefix(ancestor,descendant), same_length: {List.length(&2,Nat,ancestor) == List.length(&2,Nat,descendant) : Nat}) -> {ancestor == descendant : Path}:
  match ancestor descendant:
    case Nil{} Nil{}: {==}
    case Nil{} Con{head,tail}:
      Empty.absurd({ancestor == descendant : Path},zero_successor_empty(List.length(&2,Nat,tail),same_length))
    case Con{head,tail} Nil{}:
      Empty.absurd({ancestor == descendant : Path},prefix)
    case Con{head,tail} Con{other,rest}:
      (head_equal,tail_prefix) = prefix
      tail_length = successor_injective(List.length(&2,Nat,tail),List.length(&2,Nat,rest),same_length)
      tail_equal = prefix_same_length(tail,rest,tail_prefix,tail_length)
      first = Equal.cong(Path,Path,x => head <> x,tail,rest,tail_equal)
      second = Equal.cong(Nat,Path,x => x <> rest,head,other,head_equal)
      equality_trans(Path,ancestor,head <> rest,descendant,first,second)

def compare_under_tip(+left_locked: Path, +right_locked: Path, +new_q2: Path, left_new_q2: Prefix(left_locked,new_q2), right_new_q2: Prefix(right_locked,new_q2)) -> Compatible(left_locked,right_locked):
  prefixes_comparable(left_locked,right_locked,new_q2,left_new_q2,right_new_q2)

def catchup_case(+left_locked: Path, +right_locked: Path, +old_q2: Path, +new_q2: Path, +new_q3: Path, left_covers: Prefix(left_locked,old_q2), right_covers: Prefix(right_locked,new_q2), new_q3_below_q2: Prefix(new_q3,new_q2), height: Q.Le(List.length(&2,Nat,old_q2),List.length(&2,Nat,new_q3)), prior: Compatible(left_locked,new_q3)) -> Compatible(left_locked,right_locked):
  match prior:
    case Inl{left_below_q3}:
      compare_under_tip(left_locked,right_locked,new_q2,prefix_trans(left_locked,new_q3,new_q2,left_below_q3,new_q3_below_q2),right_covers)
    case Inr{+q3_below_left}:
      left_length = Q.le_trans(List.length(&2,Nat,left_locked),List.length(&2,Nat,old_q2),List.length(&2,Nat,new_q3),prefix_length(left_locked,old_q2,left_covers),height)
      q3_length = prefix_length(new_q3,left_locked,q3_below_left)
      same_length = le_antisymm(List.length(&2,Nat,new_q3),List.length(&2,Nat,left_locked),q3_length,left_length)
      same_path = prefix_same_length(new_q3,left_locked,q3_below_left,same_length)
      left_below_q2 : Prefix(left_locked,new_q2) = %same_path : Prefix(_,new_q2); new_q3_below_q2
      compare_under_tip(left_locked,right_locked,new_q2,left_below_q2,right_covers)

# A retained Q2 is the direct case: both locks are below the same new Q2.
def retained_q2_preserves_safety(+left_locked: Path, +right_locked: Path, +old_q2: Path, +new_q2: Path, left_covers: Prefix(left_locked,old_q2), right_covers: Prefix(right_locked,new_q2), retained: Prefix(old_q2,new_q2)) -> Compatible(left_locked,right_locked):
  compare_under_tip(left_locked,right_locked,new_q2,prefix_trans(left_locked,old_q2,new_q2,left_covers,retained),right_covers)

# Gate 3: an honest advancing-Q3 catch-up preserves compatibility. The `prior`
# certificate is the smaller-root induction result for the already accepted Q3
# lock; it is not a recovery permission or a ranking override.
def advancing_q3_preserves_safety(+left_locked: Path, +right_locked: Path, +old_q2: Path, +new_q2: Path, +old_q3: Path, +new_q3: Path, left_covers: Prefix(left_locked,old_q2), right_covers: Prefix(right_locked,new_q2), new_q3_below_q2: Prefix(new_q3,new_q2), advanced: Prefix(old_q3,new_q3), height: Q.Le(List.length(&2,Nat,old_q2),List.length(&2,Nat,new_q3)), prior: Compatible(left_locked,new_q3)) -> Compatible(left_locked,right_locked):
  catchup_case(left_locked,right_locked,old_q2,new_q2,new_q3,left_covers,right_covers,new_q3_below_q2,height,prior)
