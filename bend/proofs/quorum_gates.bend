import Base
import ../model/kernel.bend as K

# Universal weighted-quorum gates. Authority rows are stake units, so repeated
# identities carry weight while repeated signatures still count once.

def Truth(b: Bool) -> Data:
  match b:
    case False{}: Empty
    case True{}: Unit

def false_empty(e: {False{} == True{} : Bool}) -> Empty:
  %Equal.sym(Bool,False{},True{},e) : Truth(_)
  Unit{}

def impossible(-A: Type, e: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A,false_empty(e))

def refl(-A: Type, a: A) -> {a == a : A}:
  {==}

def mask(b: Bool) -> Nat:
  Bool.pick(Nat,b,1n,0n)

type Selection is Data:
  In{ids: List<&2,Nat>}
  Both{left: Selection, right: Selection}
  Either{left: Selection, right: Selection}
  Not{inner: Selection}
  All{}

def test(selection: Selection, +id: Nat) -> Bool:
  match selection:
    case In{ids}: K.contains(ids,id)
    case Both{left,right}: test(left,id) && test(right,id)
    case Either{left,right}: test(left,id) || test(right,id)
    case Not{inner}: Bool.not(test(inner,id))
    case All{}: True{}

def rows(authority: List<&2,Nat>, +selection: Selection) -> Nat:
  match authority:
    case Nil{}: 0n
    case Con{id,rest}: Nat.add(mask(test(selection,id)),rows(rest,selection))

def selected(authority: List<&2,Nat>, signers: List<&2,Nat>) -> Nat:
  rows(authority,In{signers})

def support_rows(+authority: List<&2,Nat>, +signers: List<&2,Nat>) -> {K.support_weight(K.Authority{authority},signers) == selected(authority,signers) : Nat}:
  match authority:
    case Nil{}: {==}
    case Con{id,rest}:
      %support_rows(rest,signers) : {K.support_weight(K.Authority{authority},signers) == Nat.add(mask(K.contains(signers,id)),_) : Nat}
      {==}

# Structural natural-number order used by the arithmetic proof.
def Le(a: Nat, b: Nat) -> Data:
  match a b:
    case 0n b: Unit
    case 1n+a 0n: Empty
    case 1n+a 1n+b: Le(a,b)

def le_refl(+a: Nat) -> Le(a,a):
  match a:
    case 0n: Unit{}
    case 1n+a: le_refl(a)

def le_step(+a: Nat, +b: Nat, proof: Le(a,b)) -> Le(a,1n+b):
  match a b:
    case 0n b: Unit{}
    case 1n+a 0n: Empty.absurd(Le(1n+a,1n),proof)
    case 1n+a 1n+b: le_step(a,b,proof)

def le_trans(+a: Nat, +b: Nat, +c: Nat, first: Le(a,b), second: Le(b,c)) -> Le(a,c):
  match a b c:
    case 0n b c: Unit{}
    case 1n+a 0n c: Empty.absurd(Le(1n+a,c),first)
    case 1n+a 1n+b 0n: Empty.absurd(Le(1n+a,0n),second)
    case 1n+a 1n+b 1n+c: le_trans(a,b,c,first,second)

def le_add(+a: Nat, +b: Nat, +c: Nat, +d: Nat, first: Le(a,b), second: Le(c,d)) -> Le(Nat.add(a,c),Nat.add(b,d)):
  match a b:
    case 0n 0n: second
    case 0n 1n+b: le_step(c,Nat.add(b,d),le_add(0n,b,c,d,Unit{},second))
    case 1n+a 0n: Empty.absurd(Le(Nat.add(1n+a,c),d),first)
    case 1n+a 1n+b: le_add(a,b,c,d,first,second)

def lt_le(+a: Nat, +b: Nat, proof: {(a < b : Nat) == True{} : Bool}) -> Le(1n+a,b):
  match a b:
    case 0n 0n: false_empty(proof)
    case 0n 1n+b: Unit{}
    case 1n+a 0n: false_empty(proof)
    case 1n+a 1n+b: lt_le(a,b,proof)

def le_not_gt(+a: Nat, +b: Nat, lower: Le(a,b), upper: Le(1n+b,a)) -> Empty:
  match a b:
    case 0n b: upper
    case 1n+a 0n: lower
    case 1n+a 1n+b: le_not_gt(a,b,lower,upper)

def le_left(+a: Nat, +b: Nat) -> Le(a,Nat.add(a,b)):
  match a:
    case 0n: Unit{}
    case 1n+a: le_left(a,b)

def le_mul(+factor: Nat, +a: Nat, +b: Nat, +proof: Le(a,b)) -> Le(Nat.mul(factor,a),Nat.mul(factor,b)):
  match factor:
    case 0n: Unit{}
    case 1n+factor: le_add(a,b,Nat.mul(factor,a),Nat.mul(factor,b),proof,le_mul(factor,a,b,proof))

def lt_add(+a: Nat, +b: Nat, +c: Nat, +d: Nat, first: Le(1n+a,b), second: Le(1n+c,d)) -> Le(1n+Nat.add(a,c),Nat.add(b,d)):
  le_add(1n+a,b,c,d,first,le_trans(c,1n+c,d,le_step(c,c,le_refl(c)),second))

def add_zero(+a: Nat) -> {Nat.add(a,0n) == a : Nat}:
  match a:
    case 0n: {==}
    case 1n+a:
      %add_zero(a) : {1n+Nat.add(a,0n) == 1n+_ : Nat}
      {==}

def add_successor(+a: Nat, +b: Nat) -> {Nat.add(a,1n+b) == 1n+Nat.add(a,b) : Nat}:
  match a:
    case 0n: {==}
    case 1n+a:
      %add_successor(a,b) : {1n+Nat.add(a,1n+b) == 1n+_ : Nat}
      {==}

def add_comm(+a: Nat, +b: Nat) -> {Nat.add(a,b) == Nat.add(b,a) : Nat}:
  match a:
    case 0n: Equal.sym(Nat,Nat.add(b,0n),b,add_zero(b))
    case 1n+a:
      %Equal.sym(Nat,Nat.add(b,1n+a),1n+Nat.add(b,a),add_successor(b,a)) : {Nat.add(1n+a,b) == _ : Nat}
      %add_comm(a,b) : {Nat.add(1n+a,b) == 1n+_ : Nat}
      {==}

def add_assoc(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a,Nat.add(b,c)) == Nat.add(Nat.add(a,b),c) : Nat}:
  match a:
    case 0n: {==}
    case 1n+a:
      %add_assoc(a,b,c) : {1n+Nat.add(a,Nat.add(b,c)) == 1n+_ : Nat}
      {==}

def shuffle(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a,b),Nat.add(c,d)) == Nat.add(Nat.add(a,c),Nat.add(b,d)) : Nat}:
  %add_assoc(a,c,Nat.add(b,d)) : {Nat.add(Nat.add(a,b),Nat.add(c,d)) == _ : Nat}
  %Equal.sym(Nat,Nat.add(c,Nat.add(b,d)),Nat.add(Nat.add(c,b),d),add_assoc(c,b,d)) : {Nat.add(Nat.add(a,b),Nat.add(c,d)) == Nat.add(a,_) : Nat}
  %add_comm(b,c) : {Nat.add(Nat.add(a,b),Nat.add(c,d)) == Nat.add(a,Nat.add(_,d)) : Nat}
  %add_assoc(b,c,d) : {Nat.add(Nat.add(a,b),Nat.add(c,d)) == Nat.add(a,_) : Nat}
  Equal.sym(Nat,Nat.add(a,Nat.add(b,Nat.add(c,d))),Nat.add(Nat.add(a,b),Nat.add(c,d)),add_assoc(a,b,Nat.add(c,d)))

def mul_right_sum(+factor: Nat, +a: Nat, +b: Nat) -> {Nat.mul(factor,Nat.add(a,b)) == Nat.add(Nat.mul(factor,a),Nat.mul(factor,b)) : Nat}:
  match factor:
    case 0n: {==}
    case 1n+factor:
      %shuffle(a,b,Nat.mul(factor,a),Nat.mul(factor,b)) : {Nat.mul(1n+factor,Nat.add(a,b)) == _ : Nat}
      %mul_right_sum(factor,a,b) : {Nat.mul(1n+factor,Nat.add(a,b)) == Nat.add(Nat.add(a,b),_) : Nat}
      {==}

def twice(+n: Nat) -> {Nat.mul(2n,n) == Nat.add(n,n) : Nat}:
  %add_zero(n) : {Nat.mul(2n,n) == Nat.add(n,_) : Nat}
  {==}

def thrice(+n: Nat) -> {Nat.mul(3n,n) == Nat.add(Nat.add(n,n),n) : Nat}:
  %add_assoc(n,n,n) : {Nat.mul(3n,n) == _ : Nat}
  %add_zero(n) : {Nat.mul(3n,n) == Nat.add(n,Nat.add(n,_)) : Nat}
  {==}

def sum3(a: Nat, b: Nat, c: Nat) -> Nat:
  Nat.add(Nat.add(a,b),c)

def shuffle3(+a: Nat, +b: Nat, +c: Nat, +x: Nat, +y: Nat, +z: Nat) -> {sum3(Nat.add(a,x),Nat.add(b,y),Nat.add(c,z)) == Nat.add(sum3(a,b,c),sum3(x,y,z)) : Nat}:
  %shuffle(Nat.add(a,b),Nat.add(x,y),c,z) : {sum3(Nat.add(a,x),Nat.add(b,y),Nat.add(c,z)) == _ : Nat}
  %shuffle(a,x,b,y) : {sum3(Nat.add(a,x),Nat.add(b,y),Nat.add(c,z)) == Nat.add(_,Nat.add(c,z)) : Nat}
  {==}

def mask_triple(+a: Bool, +b: Bool, +c: Bool) -> Le(sum3(mask(a),mask(b),mask(c)),Nat.add(2n,mask((a && b) && c))):
  match a b c:
    case False{} False{} False{}: Unit{}
    case False{} False{} True{}: Unit{}
    case False{} True{} False{}: Unit{}
    case False{} True{} True{}: Unit{}
    case True{} False{} False{}: Unit{}
    case True{} False{} True{}: Unit{}
    case True{} True{} False{}: Unit{}
    case True{} True{} True{}: Unit{}

def bound_combine(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat, first: Le(a,Nat.add(b,c)), second: Le(d,Nat.add(e,f))) -> Le(Nat.add(a,d),Nat.add(Nat.add(b,e),Nat.add(c,f))):
  %shuffle(b,c,e,f) : Le(Nat.add(a,d),_)
  le_add(a,Nat.add(b,c),d,Nat.add(e,f),first,second)

def triple_bound(+authority: List<&2,Nat>, +a: Selection, +b: Selection, +c: Selection) -> Le(sum3(rows(authority,a),rows(authority,b),rows(authority,c)),Nat.add(Nat.mul(2n,List.length(&2,Nat,authority)),rows(authority,Both{Both{a,b},c}))):
  match authority:
    case Nil{}: Unit{}
    case Con{id,rest}:
      %Equal.sym(Nat,sum3(rows(authority,a),rows(authority,b),rows(authority,c)),Nat.add(sum3(mask(test(a,id)),mask(test(b,id)),mask(test(c,id))),sum3(rows(rest,a),rows(rest,b),rows(rest,c))),shuffle3(mask(test(a,id)),mask(test(b,id)),mask(test(c,id)),rows(rest,a),rows(rest,b),rows(rest,c))) : Le(_,Nat.add(Nat.mul(2n,List.length(&2,Nat,authority)),rows(authority,Both{Both{a,b},c})))
      %Equal.sym(Nat,Nat.mul(2n,List.length(&2,Nat,authority)),Nat.add(2n,Nat.mul(2n,List.length(&2,Nat,rest))),mul_right_sum(2n,1n,List.length(&2,Nat,rest))) : Le(Nat.add(sum3(mask(test(a,id)),mask(test(b,id)),mask(test(c,id))),sum3(rows(rest,a),rows(rest,b),rows(rest,c))),Nat.add(_,rows(authority,Both{Both{a,b},c})))
      bound_combine(sum3(mask(test(a,id)),mask(test(b,id)),mask(test(c,id))),2n,mask(test(Both{Both{a,b},c},id)),sum3(rows(rest,a),rows(rest,b),rows(rest,c)),Nat.mul(2n,List.length(&2,Nat,rest)),rows(rest,Both{Both{a,b},c}),mask_triple(test(a,id),test(b,id),test(c,id)),triple_bound(rest,a,b,c))

def three_strict(+total: Nat, +a: Nat, +b: Nat, +c: Nat, first: Le(1n+Nat.mul(2n,total),Nat.mul(3n,a)), second: Le(1n+Nat.mul(2n,total),Nat.mul(3n,b)), third: Le(1n+Nat.mul(2n,total),Nat.mul(3n,c))) -> Le(1n+Nat.mul(3n,Nat.mul(2n,total)),Nat.mul(3n,sum3(a,b,c))):
  %Equal.sym(Nat,Nat.mul(3n,Nat.mul(2n,total)),sum3(Nat.mul(2n,total),Nat.mul(2n,total),Nat.mul(2n,total)),thrice(Nat.mul(2n,total))) : Le(1n+_,Nat.mul(3n,sum3(a,b,c)))
  %Equal.sym(Nat,Nat.mul(3n,sum3(a,b,c)),Nat.add(Nat.mul(3n,Nat.add(a,b)),Nat.mul(3n,c)),mul_right_sum(3n,Nat.add(a,b),c)) : Le(1n+sum3(Nat.mul(2n,total),Nat.mul(2n,total),Nat.mul(2n,total)),_)
  %Equal.sym(Nat,Nat.mul(3n,Nat.add(a,b)),Nat.add(Nat.mul(3n,a),Nat.mul(3n,b)),mul_right_sum(3n,a,b)) : Le(1n+sum3(Nat.mul(2n,total),Nat.mul(2n,total),Nat.mul(2n,total)),Nat.add(_,Nat.mul(3n,c)))
  lt_add(Nat.add(Nat.mul(2n,total),Nat.mul(2n,total)),Nat.add(Nat.mul(3n,a),Nat.mul(3n,b)),Nat.mul(2n,total),Nat.mul(3n,c),lt_add(Nat.mul(2n,total),Nat.mul(3n,a),Nat.mul(2n,total),Nat.mul(3n,b),first,second),third)

def positive_from_not_zero(+n: Nat, absent: {n == 0n : Nat} -> Empty) -> Le(1n,n):
  match n:
    case 0n: absent(refl(Nat,0n))
    case 1n+n: Unit{}

def triple_zero_impossible(+authority: List<&2,Nat>, +a: Selection, +b: Selection, +c: Selection, first: Le(1n+Nat.mul(2n,List.length(&2,Nat,authority)),Nat.mul(3n,rows(authority,a))), second: Le(1n+Nat.mul(2n,List.length(&2,Nat,authority)),Nat.mul(3n,rows(authority,b))), third: Le(1n+Nat.mul(2n,List.length(&2,Nat,authority)),Nat.mul(3n,rows(authority,c))), zero: {rows(authority,Both{Both{a,b},c}) == 0n : Nat}) -> Empty:
  upper : Le(sum3(rows(authority,a),rows(authority,b),rows(authority,c)),Nat.mul(2n,List.length(&2,Nat,authority))) = %add_zero(Nat.mul(2n,List.length(&2,Nat,authority))) : Le(sum3(rows(authority,a),rows(authority,b),rows(authority,c)),_); %zero : Le(sum3(rows(authority,a),rows(authority,b),rows(authority,c)),Nat.add(Nat.mul(2n,List.length(&2,Nat,authority)),_)); triple_bound(authority,a,b,c)
  le_not_gt(Nat.mul(3n,sum3(rows(authority,a),rows(authority,b),rows(authority,c))),Nat.mul(3n,Nat.mul(2n,List.length(&2,Nat,authority))),le_mul(3n,sum3(rows(authority,a),rows(authority,b),rows(authority,c)),Nat.mul(2n,List.length(&2,Nat,authority)),upper),three_strict(List.length(&2,Nat,authority),rows(authority,a),rows(authority,b),rows(authority,c),first,second,third))

def quorum_strict(+authority: K.Authority, +signers: List<&2,Nat>, quorum: {K.has_quorum(authority,signers) == True{} : Bool}) -> Le(1n+Nat.mul(2n,K.total(authority)),Nat.mul(3n,selected(K.Authority.members(authority),signers))):
  numeric : {(Nat.mul(2n,K.total(authority)) < Nat.mul(3n,selected(K.Authority.members(authority),signers)) : Nat) == True{} : Bool} = %support_rows(K.Authority.members(authority),signers) : {(Nat.mul(2n,K.total(authority)) < Nat.mul(3n,_) : Nat) == True{} : Bool}; quorum
  lt_le(Nat.mul(2n,K.total(authority)),Nat.mul(3n,selected(K.Authority.members(authority),signers)),numeric)

def nat_eq_refl(+id: Nat) -> {K.nat_eq(id,id) == True{} : Bool}:
  match id:
    case 0n: {==}
    case 1n+id: nat_eq_refl(id)

def or_from_left(+left: Bool, +right: Bool, proof: {left == True{} : Bool}) -> {left || right == True{} : Bool}:
  match left right:
    case False{} False{}: proof
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}: {==}

def contains_head(+id: Nat, +rest: List<&2,Nat>) -> {K.contains(id <> rest,id) == True{} : Bool}:
  or_from_left(K.nat_eq(id,id),K.contains(rest,id),nat_eq_refl(id))

def or_true(+value: Bool) -> {value || True{} == True{} : Bool}:
  match value:
    case False{}: {==}
    case True{}: {==}

def or_from_right(+left: Bool, +right: Bool, proof: {right == True{} : Bool}) -> {left || right == True{} : Bool}:
  match left right:
    case False{} False{}: proof
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}: {==}

def contains_tail(+id: Nat, +rest: List<&2,Nat>, +wanted: Nat, found: {K.contains(rest,wanted) == True{} : Bool}) -> {K.contains(id <> rest,wanted) == True{} : Bool}:
  or_from_right(K.nat_eq(id,wanted),K.contains(rest,wanted),found)

def and_left(+a: Bool, +b: Bool, both: {a && b == True{} : Bool}) -> {a == True{} : Bool}:
  match a b:
    case False{} False{}: impossible({False{} == True{} : Bool},both)
    case False{} True{}: both
    case True{} False{}: {==}
    case True{} True{}: {==}

def and_right(+a: Bool, +b: Bool, both: {a && b == True{} : Bool}) -> {b == True{} : Bool}:
  match a b:
    case False{} False{}: impossible({False{} == True{} : Bool},both)
    case False{} True{}: {==}
    case True{} False{}: both
    case True{} True{}: {==}

def Witness(+authority: List<&2,Nat>, +selection: Selection) -> Type:
  Sigma<&2,&1,Nat,id => {K.contains(authority,id) == True{} : Bool} & {test(selection,id) == True{} : Bool}>

def witness_lift(+id: Nat, +rest: List<&2,Nat>, +selection: Selection, found: Witness(rest,selection)) -> Witness(id <> rest,selection):
  (+wanted,(member,yes)) = found
  (wanted,(contains_tail(id,rest,wanted,member),yes))

def rows_witness_case(+id: Nat, +rest: List<&2,Nat>, +selection: Selection, +selected_here: Bool, equal: {test(selection,id) == selected_here : Bool}, positive: Le(1n,rows(id <> rest,selection)), recurse: Le(1n,rows(rest,selection)) -> Witness(rest,selection)) -> Witness(id <> rest,selection):
  match selected_here:
    case False{}:
      tail_positive : Le(1n,rows(rest,selection)) = %equal : Le(1n,Nat.add(mask(_),rows(rest,selection))); positive
      witness_lift(id,rest,selection,recurse(tail_positive))
    case True{}:
      (id,(contains_head(id,rest),equal))

def rows_witness(+authority: List<&2,Nat>, +selection: Selection, positive: Le(1n,rows(authority,selection))) -> Witness(authority,selection):
  match authority:
    case Nil{}: Empty.absurd(Witness(authority,selection),positive)
    case Con{id,rest}:
      rows_witness_case(id,rest,selection,test(selection,id),refl(Bool,test(selection,id)),positive,next => rows_witness(rest,selection,next))

def Common(+authority: List<&2,Nat>, +left: List<&2,Nat>, +right: List<&2,Nat>, +honest: List<&2,Nat>) -> Type:
  Sigma<&2,&1,Nat,id => {K.contains(authority,id) == True{} : Bool} & ({K.contains(left,id) == True{} : Bool} & ({K.contains(right,id) == True{} : Bool} & {K.contains(honest,id) == True{} : Bool}))>

def common_from_witness(+authority: List<&2,Nat>, +left: List<&2,Nat>, +right: List<&2,Nat>, +honest: List<&2,Nat>, witness: Witness(authority,Both{Both{In{left},In{right}},In{honest}})) -> Common(authority,left,right,honest):
  (+id,(member,+yes)) = witness
  +left_right = and_left(K.contains(left,id) && K.contains(right,id),K.contains(honest,id),yes)
  honest_yes = and_right(K.contains(left,id) && K.contains(right,id),K.contains(honest,id),yes)
  (id,(member,(and_left(K.contains(left,id),K.contains(right,id),left_right),(and_right(K.contains(left,id),K.contains(right,id),left_right),honest_yes))))

# Gate 1: two strict two-thirds certificates under one authority share honest
# stake when honest stake is itself a strict two-thirds quorum.
def same_authority_intersection(+authority: K.Authority, +left: List<&2,Nat>, +right: List<&2,Nat>, +honest: List<&2,Nat>, left_quorum: {K.has_quorum(authority,left) == True{} : Bool}, right_quorum: {K.has_quorum(authority,right) == True{} : Bool}, honest_quorum: {K.has_quorum(authority,honest) == True{} : Bool}) -> Common(K.Authority.members(authority),left,right,honest):
  +members : List<&2,Nat> = K.Authority.members(authority)
  positive = positive_from_not_zero(rows(members,Both{Both{In{left},In{right}},In{honest}}),zero => triple_zero_impossible(members,In{left},In{right},In{honest},quorum_strict(authority,left,left_quorum),quorum_strict(authority,right,right_quorum),quorum_strict(authority,honest,honest_quorum),zero))
  common_from_witness(members,left,right,honest,rows_witness(members,Both{Both{In{left},In{right}},In{honest}},positive))
