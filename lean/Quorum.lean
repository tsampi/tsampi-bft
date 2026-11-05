import Protocol

/-!
# Weighted quorum overlap

Two strict two-thirds signer sets under the same finite authority share an
honest signer when honest power itself exceeds two thirds.
-/

namespace BFT

def mass (members : List (ValidatorId × Stake)) (predicate : ValidatorId → Bool) : Stake :=
  (members.map fun entry ↦ if predicate entry.1 then entry.2 else 0).sum

@[simp] theorem mass_nil (predicate : ValidatorId → Bool) : mass [] predicate = 0 := rfl

@[simp] theorem mass_cons (entry : ValidatorId × Stake)
    (members : List (ValidatorId × Stake)) (predicate : ValidatorId → Bool) :
    mass (entry :: members) predicate =
      (if predicate entry.1 then entry.2 else 0) + mass members predicate := by
  simp [mass]

@[simp] theorem mass_true (members : List (ValidatorId × Stake)) :
    mass members (fun _ ↦ true) = (members.map Prod.snd).sum := by
  simp [mass]

theorem mass_congr {members : List (ValidatorId × Stake)}
    {left right : ValidatorId → Bool}
    (same : ∀ entry ∈ members, left entry.1 = right entry.1) :
    mass members left = mass members right := by
  unfold mass
  apply congrArg List.sum
  apply List.map_inj_left.mpr
  intro entry member
  rw [same entry member]

theorem mass_zero {members : List (ValidatorId × Stake)}
    {predicate : ValidatorId → Bool}
    (zero : ∀ entry ∈ members, predicate entry.1 = false) :
    mass members predicate = 0 := by
  induction members with
  | nil => rfl
  | cons entry rest ih =>
      have head := zero entry (by simp)
      have tail := ih (fun candidate member ↦ zero candidate (by simp [member]))
      simp [head, tail]

theorem mass_le_total (members : List (ValidatorId × Stake))
    (predicate : ValidatorId → Bool) :
    mass members predicate ≤ (members.map Prod.snd).sum := by
  induction members with
  | nil => simp
  | cons entry rest ih =>
      cases selected : predicate entry.1
      · simpa [mass_cons, selected] using Nat.le_add_left_of_le (k := entry.2) ih
      · simpa [mass_cons, selected] using Nat.add_le_add_left ih entry.2

theorem mass_filter (members : List (ValidatorId × Stake))
    (retained selected : ValidatorId → Bool) :
    mass (members.filter fun entry ↦ retained entry.1) selected =
      mass members (fun id ↦ retained id && selected id) := by
  induction members with
  | nil => rfl
  | cons entry rest ih =>
      cases keep : retained entry.1 <;> simp_all [mass_cons]

theorem mass_cover_within (members : List (ValidatorId × Stake))
    (retainedSet selected honest : ValidatorId → Bool)
    (selectedWithin : ∀ entry ∈ members,
      selected entry.1 = true → retainedSet entry.1 = true)
    (honestWithin : ∀ entry ∈ members,
      honest entry.1 = true → retainedSet entry.1 = true) :
    mass members selected + mass members honest ≤
      mass members retainedSet + mass members (fun id ↦ selected id && honest id) := by
  induction members with
  | nil => simp
  | cons entry rest ih =>
      have selectedTail : ∀ candidate ∈ rest,
          selected candidate.1 = true → retainedSet candidate.1 = true := by
        intro candidate member
        exact selectedWithin candidate (by simp [member])
      have honestTail : ∀ candidate ∈ rest,
          honest candidate.1 = true → retainedSet candidate.1 = true := by
        intro candidate member
        exact honestWithin candidate (by simp [member])
      have tail := ih selectedTail honestTail
      have selectedHead := selectedWithin entry (by simp)
      have honestHead := honestWithin entry (by simp)
      cases hu : retainedSet entry.1
      · cases hs : selected entry.1 <;> cases hh : honest entry.1 <;>
          simp_all [mass_cons]
      · cases hs : selected entry.1 <;> cases hh : honest entry.1
        case false.false =>
          simp_all [mass_cons]
          simpa [Nat.add_assoc] using Nat.le_add_left_of_le (k := entry.2) tail
        case false.true =>
          simp_all [mass_cons]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            Nat.add_le_add_left tail entry.2
        case true.false =>
          simp_all [mass_cons]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            Nat.add_le_add_left tail entry.2
        case true.true =>
          simp_all [mass_cons]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            Nat.add_le_add_left (Nat.add_le_add_left tail entry.2) entry.2

theorem mass_cover (members : List (ValidatorId × Stake))
    (selected honest : ValidatorId → Bool) :
    mass members selected + mass members honest ≤
      (members.map Prod.snd).sum + mass members (fun id ↦ selected id && honest id) := by
  induction members with
  | nil => simp
  | cons entry rest ih =>
      cases hs : selected entry.1 <;> cases hh : honest entry.1
      case false.false =>
        simp_all [mass_cons]
        simpa [Nat.add_assoc] using Nat.le_add_left_of_le (k := entry.2) ih
      case false.true =>
        simp_all [mass_cons]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Nat.add_le_add_left ih entry.2
      case true.false =>
        simp_all [mass_cons]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Nat.add_le_add_left ih entry.2
      case true.true =>
        simp_all [mass_cons]
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Nat.add_le_add_left (Nat.add_le_add_left ih entry.2) entry.2

theorem mass_disjoint (members : List (ValidatorId × Stake))
    (left right honest : ValidatorId → Bool)
    (disjoint : ∀ entry ∈ members, ¬(left entry.1 = true ∧ right entry.1 = true ∧
      honest entry.1 = true)) :
    mass members (fun id ↦ left id && honest id) +
      mass members (fun id ↦ right id && honest id) ≤ mass members honest := by
  induction members with
  | nil => simp
  | cons entry rest ih =>
      have here := disjoint entry (by simp)
      have tail := ih (fun candidate member ↦ disjoint candidate (by simp [member]))
      cases hl : left entry.1 <;> cases hr : right entry.1 <;>
        cases hh : honest entry.1 <;> simp_all [mass_cons]
      case false.false.true =>
        exact Nat.le_add_left_of_le (k := entry.2) tail
      case false.true.true =>
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Nat.add_le_add_left tail entry.2
      case true.false.true =>
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Nat.add_le_add_left tail entry.2

theorem eraseDups_nodup (ids : List ValidatorId) : ids.eraseDups.Nodup := by
  cases ids with
  | nil => simp
  | cons id rest =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp [List.mem_eraseDups, List.mem_filter]
      · exact eraseDups_nodup _
termination_by ids.length
decreasing_by
  have bound := List.length_filter_le (fun candidate : ValidatorId ↦ !(candidate == id)) rest
  simp only [List.length_cons]
  omega

private theorem sum_map_add {α : Type} (items : List α) (left right : α → Nat) :
    (items.map fun item ↦ left item + right item).sum =
      (items.map left).sum + (items.map right).sum := by
  induction items with
  | nil => simp
  | cons item rest ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private theorem sum_indicator (ids : List ValidatorId) (key amount : Nat)
    (unique : ids.Nodup) :
    (ids.map fun id ↦ if key == id then amount else 0).sum =
      if ids.contains key then amount else 0 := by
  induction ids with
  | nil => simp
  | cons id rest ih =>
      have head := List.nodup_cons.mp unique
      have tail := ih head.2
      by_cases same : key = id
      · subst key
        simp only [List.map_cons, List.sum_cons, tail]
        simp [head.1]
      · simp only [List.map_cons, List.sum_cons, tail]
        simp [same]

private theorem sum_singleton_mass (members : List (ValidatorId × Stake))
    (ids : List ValidatorId) (unique : ids.Nodup) :
    (ids.map fun id ↦ mass members (fun key ↦ key == id)).sum =
      mass members fun key ↦ ids.contains key := by
  induction members with
  | nil =>
      simp only [mass_nil]
      induction ids with
      | nil => rfl
      | cons id rest ih => simp_all
  | cons entry rest ih =>
      simp only [mass_cons]
      rw [sum_map_add, sum_indicator ids entry.1 entry.2 unique, ih]

private theorem weight_eq_mass (members : List (ValidatorId × Stake))
    (id : ValidatorId) (unique : (members.map Prod.fst).Nodup) :
    ((members.find? fun entry ↦ entry.1 == id).map Prod.snd).getD 0 =
      mass members (fun key ↦ key == id) := by
  induction members with
  | nil => simp [mass]
  | cons entry rest ih =>
      have head := List.nodup_cons.mp unique
      by_cases same : entry.1 = id
      · have zero : mass rest (fun key ↦ key == id) = 0 := by
          apply mass_zero
          intro other member
          have different : other.1 ≠ id := by
            intro equal
            apply head.1
            exact List.mem_map.mpr ⟨other, member, equal.trans same.symm⟩
          simp [different]
        simp [same, zero]
      · simpa [same] using ih head.2

theorem supportWeight_eq_mass (authority : Authority) (signers : List ValidatorId)
    (unique : (authority.members.map Prod.fst).Nodup) :
    authority.supportWeight signers =
      mass authority.members (fun id ↦ signers.contains id) := by
  unfold Authority.supportWeight
  calc
    (signers.eraseDups.map authority.weight).sum =
        (signers.eraseDups.map fun id ↦
          mass authority.members (fun key ↦ key == id)).sum := by
      apply congrArg List.sum
      apply List.map_inj_left.mpr
      intro id _
      exact weight_eq_mass authority.members id unique
    _ = mass authority.members (fun id ↦ signers.eraseDups.contains id) :=
      sum_singleton_mass _ _ (eraseDups_nodup signers)
    _ = mass authority.members (fun id ↦ signers.contains id) := by
      apply mass_congr
      intro entry _
      apply Bool.eq_iff_iff.mpr
      simp only [List.contains_iff_mem, List.mem_eraseDups]

theorem intersection_arithmetic {left right honest total : Nat}
    (leftQuorum : 2 * total < 3 * left)
    (rightQuorum : 2 * total < 3 * right)
    (honestQuorum : 2 * total < 3 * honest)
    (noOverlap : left + right + honest ≤ 2 * total) : False := by
  omega

theorem crossAuthorityIntersectionArithmetic
    {left right honest oldTotal newTotal leftHonest rightHonest : Nat}
    (leftQuorum : 2 * oldTotal < 3 * left)
    (rightQuorum : 2 * newTotal < 3 * right)
    (honestQuorum : 2 * oldTotal < 3 * honest)
    (leftCover : left + honest ≤ oldTotal + leftHonest)
    (rightCover : right + honest ≤ newTotal + rightHonest)
    (noOverlap : leftHonest + rightHonest ≤ honest)
    (shrinks : newTotal ≤ oldTotal) : False := by
  omega

theorem twoRetainedIntersectionArithmetic
    {left right honest leftTotal rightTotal total leftHonest rightHonest : Nat}
    (leftQuorum : 2 * leftTotal < 3 * left)
    (rightQuorum : 2 * rightTotal < 3 * right)
    (honestQuorum : 2 * total < 3 * honest)
    (leftCover : left + honest ≤ leftTotal + leftHonest)
    (rightCover : right + honest ≤ rightTotal + rightHonest)
    (noOverlap : leftHonest + rightHonest ≤ honest)
    (leftShrinks : leftTotal ≤ total)
    (rightShrinks : rightTotal ≤ total) : False := by
  omega

private theorem no_overlap_bound {left right honest leftHonest rightHonest total : Nat}
    (leftCover : left + honest ≤ total + leftHonest)
    (rightCover : right + honest ≤ total + rightHonest)
    (disjoint : leftHonest + rightHonest ≤ honest) :
    left + right + honest ≤ 2 * total := by
  omega

theorem sameAuthorityQuorums_shareHonest (authority : Authority)
    (honest left right : List ValidatorId)
    (unique : (authority.members.map Prod.fst).Nodup)
    (honestQuorum : authority.hasQuorum honest = true)
    (leftQuorum : authority.hasQuorum left = true)
    (rightQuorum : authority.hasQuorum right = true) :
    ∃ signer, signer ∈ honest ∧ signer ∈ left ∧ signer ∈ right := by
  classical
  apply Classical.byContradiction
  intro absent
  have disjoint : ∀ entry ∈ authority.members,
      ¬(left.contains entry.1 = true ∧ right.contains entry.1 = true ∧
        honest.contains entry.1 = true) := by
    intro entry _ ⟨inLeft, inRight, isHonest⟩
    apply absent
    exact ⟨entry.1, List.contains_iff_mem.mp isHonest,
      List.contains_iff_mem.mp inLeft, List.contains_iff_mem.mp inRight⟩
  have leftCover := mass_cover authority.members left.contains honest.contains
  have rightCover := mass_cover authority.members right.contains honest.contains
  have honestDisjoint :=
    mass_disjoint authority.members left.contains right.contains honest.contains disjoint
  have leftMass : 2 * authority.total < 3 * mass authority.members left.contains := by
    have equal := supportWeight_eq_mass authority left unique
    simpa only [Authority.hasQuorum, decide_eq_true_eq, equal] using leftQuorum
  have rightMass : 2 * authority.total < 3 * mass authority.members right.contains := by
    have equal := supportWeight_eq_mass authority right unique
    simpa only [Authority.hasQuorum, decide_eq_true_eq, equal] using rightQuorum
  have honestMass : 2 * authority.total < 3 * mass authority.members honest.contains := by
    have equal := supportWeight_eq_mass authority honest unique
    simpa only [Authority.hasQuorum, decide_eq_true_eq, equal] using honestQuorum
  apply intersection_arithmetic leftMass rightMass honestMass
  exact no_overlap_bound leftCover rightCover honestDisjoint

/-- A quorum measured after removing validators, expressed in the old weight table. -/
def retainedQuorum (authority : Authority) (retained : ValidatorId → Bool)
    (signers : List ValidatorId) : Bool :=
  3 * mass authority.members (fun id ↦ signers.contains id && retained id) >
    2 * mass authority.members retained

theorem retainedQuorums_shareHonest (authority : Authority)
    (retained : ValidatorId → Bool) (honest left right : List ValidatorId)
    (unique : (authority.members.map Prod.fst).Nodup)
    (honestRetained : ∀ entry ∈ authority.members,
      honest.contains entry.1 = true → retained entry.1 = true)
    (honestQuorum : authority.hasQuorum honest = true)
    (leftQuorum : authority.hasQuorum left = true)
    (rightQuorum : retainedQuorum authority retained right = true) :
    ∃ signer, signer ∈ honest ∧ signer ∈ left ∧ signer ∈ right := by
  classical
  apply Classical.byContradiction
  intro absent
  let selectedRight : ValidatorId → Bool :=
    fun id ↦ right.contains id && retained id
  have disjoint : ∀ entry ∈ authority.members,
      ¬(left.contains entry.1 = true ∧ selectedRight entry.1 = true ∧
        honest.contains entry.1 = true) := by
    intro entry _ ⟨inLeft, inRight, isHonest⟩
    apply absent
    have rightParts : right.contains entry.1 = true ∧ retained entry.1 = true := by
      simpa [selectedRight] using inRight
    exact ⟨entry.1, List.contains_iff_mem.mp isHonest,
      List.contains_iff_mem.mp inLeft,
      List.contains_iff_mem.mp rightParts.1⟩
  have leftCover := mass_cover authority.members left.contains honest.contains
  have rightCover := mass_cover_within authority.members retained selectedRight
    honest.contains
    (by
      intro entry _ selected
      have parts : right.contains entry.1 = true ∧ retained entry.1 = true := by
        simpa [selectedRight] using selected
      exact parts.2)
    honestRetained
  have honestDisjoint := mass_disjoint authority.members left.contains selectedRight
    honest.contains disjoint
  have leftMass : 2 * authority.total < 3 * mass authority.members left.contains := by
    have equal := supportWeight_eq_mass authority left unique
    simpa only [Authority.hasQuorum, decide_eq_true_eq, equal] using leftQuorum
  have honestMass : 2 * authority.total < 3 * mass authority.members honest.contains := by
    have equal := supportWeight_eq_mass authority honest unique
    simpa only [Authority.hasQuorum, decide_eq_true_eq, equal] using honestQuorum
  have rightMass :
      2 * mass authority.members retained < 3 * mass authority.members selectedRight := by
    simpa only [retainedQuorum, decide_eq_true_eq] using rightQuorum
  apply crossAuthorityIntersectionArithmetic leftMass rightMass honestMass
    leftCover rightCover honestDisjoint
  exact mass_le_total authority.members retained

theorem retainedQuorums_shareHonest_both (authority : Authority)
    (leftRetained rightRetained : ValidatorId → Bool)
    (honest left right : List ValidatorId)
    (unique : (authority.members.map Prod.fst).Nodup)
    (leftHonestRetained : ∀ entry ∈ authority.members,
      honest.contains entry.1 = true → leftRetained entry.1 = true)
    (rightHonestRetained : ∀ entry ∈ authority.members,
      honest.contains entry.1 = true → rightRetained entry.1 = true)
    (honestQuorum : authority.hasQuorum honest = true)
    (leftQuorum : retainedQuorum authority leftRetained left = true)
    (rightQuorum : retainedQuorum authority rightRetained right = true) :
    ∃ signer, signer ∈ honest ∧ signer ∈ left ∧ signer ∈ right := by
  classical
  apply Classical.byContradiction
  intro absent
  let selectedLeft : ValidatorId → Bool :=
    fun id ↦ left.contains id && leftRetained id
  let selectedRight : ValidatorId → Bool :=
    fun id ↦ right.contains id && rightRetained id
  have disjoint : ∀ entry ∈ authority.members,
      ¬(selectedLeft entry.1 = true ∧ selectedRight entry.1 = true ∧
        honest.contains entry.1 = true) := by
    intro entry _ ⟨inLeft, inRight, isHonest⟩
    apply absent
    have leftParts : left.contains entry.1 = true ∧ leftRetained entry.1 = true := by
      simpa [selectedLeft] using inLeft
    have rightParts : right.contains entry.1 = true ∧ rightRetained entry.1 = true := by
      simpa [selectedRight] using inRight
    exact ⟨entry.1, List.contains_iff_mem.mp isHonest,
      List.contains_iff_mem.mp leftParts.1, List.contains_iff_mem.mp rightParts.1⟩
  have leftCover := mass_cover_within authority.members leftRetained selectedLeft
    honest.contains
    (by
      intro entry _ selected
      have parts : left.contains entry.1 = true ∧ leftRetained entry.1 = true := by
        simpa [selectedLeft] using selected
      exact parts.2)
    leftHonestRetained
  have rightCover := mass_cover_within authority.members rightRetained selectedRight
    honest.contains
    (by
      intro entry _ selected
      have parts : right.contains entry.1 = true ∧ rightRetained entry.1 = true := by
        simpa [selectedRight] using selected
      exact parts.2)
    rightHonestRetained
  have honestDisjoint := mass_disjoint authority.members selectedLeft selectedRight
    honest.contains disjoint
  have leftMass :
      2 * mass authority.members leftRetained <
        3 * mass authority.members selectedLeft := by
    simpa only [retainedQuorum, decide_eq_true_eq, selectedLeft] using leftQuorum
  have rightMass :
      2 * mass authority.members rightRetained <
        3 * mass authority.members selectedRight := by
    simpa only [retainedQuorum, decide_eq_true_eq, selectedRight] using rightQuorum
  have honestMass : 2 * authority.total < 3 * mass authority.members honest.contains := by
    have equal := supportWeight_eq_mass authority honest unique
    simpa only [Authority.hasQuorum, decide_eq_true_eq, equal] using honestQuorum
  apply twoRetainedIntersectionArithmetic leftMass rightMass honestMass
    leftCover rightCover honestDisjoint
  · exact mass_le_total authority.members leftRetained
  · exact mass_le_total authority.members rightRetained

private theorem filteredKeysNodup (members : List (ValidatorId × Stake))
    (retained : ValidatorId → Bool)
    (unique : (members.map Prod.fst).Nodup) :
    ((members.filter fun entry ↦ retained entry.1).map Prod.fst).Nodup := by
  induction members with
  | nil => simp
  | cons entry rest ih =>
      have head := List.nodup_cons.mp unique
      cases keep : retained entry.1
      · simpa [keep] using ih head.2
      · simp only [List.filter_cons, keep, ↓reduceIte,
          List.map_cons, List.nodup_cons]
        constructor
        · intro present
          apply head.1
          exact List.mem_map.mpr <| by
            obtain ⟨candidate, member, same⟩ := List.mem_map.mp present
            exact ⟨candidate, (List.mem_filter.mp member).1, same⟩
        · exact ih head.2

theorem afterEvidence_hasQuorum_eq_retainedQuorum
    (authority : Authority) (evidence : List CarriedEvidence)
    (signers : List ValidatorId)
    (unique : (authority.members.map Prod.fst).Nodup) :
    (authority.afterEvidence evidence).hasQuorum signers =
      retainedQuorum authority (retainedAfterEvidence evidence) signers := by
  let retained := retainedAfterEvidence evidence
  have newUnique :
      (((authority.afterEvidence evidence).members.map Prod.fst).Nodup) := by
    apply filteredKeysNodup authority.members retained unique
  have newSupport := supportWeight_eq_mass
    (authority.afterEvidence evidence) signers newUnique
  have supportBridge :
      (authority.afterEvidence evidence).supportWeight signers =
        mass authority.members (fun id ↦ signers.contains id && retained id) := by
    rw [newSupport]
    rw [show (authority.afterEvidence evidence).members =
        authority.members.filter (fun entry ↦ retained entry.1) by
      rfl]
    rw [mass_filter]
    apply mass_congr
    intro entry _
    simp [Bool.and_comm]
  have totalBridge :
      (authority.afterEvidence evidence).total = mass authority.members retained := by
    unfold Authority.total
    rw [← mass_true]
    rw [show (authority.afterEvidence evidence).members =
        authority.members.filter (fun entry ↦ retained entry.1) by
      rfl]
    rw [mass_filter]
    apply mass_congr
    intro entry _
    simp
  simp only [Authority.hasQuorum, retainedQuorum, supportBridge, totalBridge]
  rfl

theorem honest_retainedAfterEvidence
    (authority : Authority) (evidence : List CarriedEvidence)
    (honest : List ValidatorId)
    (honestSafe : ∀ item ∈ evidence, item.proof.offender ∉ honest) :
    ∀ entry ∈ authority.members,
      honest.contains entry.1 = true → retainedAfterEvidence evidence entry.1 = true := by
  intro entry _ isHonest
  have none : evidence.any (fun item ↦ item.proof.offender = entry.1) = false := by
    apply List.any_eq_false.mpr
    intro item itemMember offender
    apply honestSafe item itemMember
    have offenderEq : item.proof.offender = entry.1 := by simpa using offender
    simpa [offenderEq] using List.contains_iff_mem.mp isHonest
  simp [retainedAfterEvidence, none]

theorem afterEvidenceQuorums_shareHonest (authority : Authority)
    (evidence : List CarriedEvidence) (honest left right : List ValidatorId)
    (unique : (authority.members.map Prod.fst).Nodup)
    (honestSafe : ∀ item ∈ evidence, item.proof.offender ∉ honest)
    (honestQuorum : authority.hasQuorum honest = true)
    (leftQuorum : authority.hasQuorum left = true)
    (rightQuorum : (authority.afterEvidence evidence).hasQuorum right = true) :
    ∃ signer, signer ∈ honest ∧ signer ∈ left ∧ signer ∈ right := by
  let retained := retainedAfterEvidence evidence
  have honestRetained : ∀ entry ∈ authority.members,
      honest.contains entry.1 = true → retained entry.1 = true := by
    intro entry _ isHonest
    have none : evidence.any (fun item ↦ item.proof.offender = entry.1) = false := by
      apply List.any_eq_false.mpr
      intro item itemMember offender
      apply honestSafe item itemMember
      have offenderEq : item.proof.offender = entry.1 := by simpa using offender
      simpa [offenderEq] using List.contains_iff_mem.mp isHonest
    simp [retained, retainedAfterEvidence, none]
  have newUnique :
      (((authority.afterEvidence evidence).members.map Prod.fst).Nodup) := by
    apply filteredKeysNodup authority.members retained unique
  have newSupport := supportWeight_eq_mass
    (authority.afterEvidence evidence) right newUnique
  have supportBridge :
      (authority.afterEvidence evidence).supportWeight right =
        mass authority.members (fun id ↦ right.contains id && retained id) := by
    rw [newSupport]
    rw [show (authority.afterEvidence evidence).members =
        authority.members.filter (fun entry ↦ retained entry.1) by
      rfl]
    rw [mass_filter]
    apply mass_congr
    intro entry _
    simp [Bool.and_comm]
  have totalBridge :
      (authority.afterEvidence evidence).total = mass authority.members retained := by
    unfold Authority.total
    rw [← mass_true]
    rw [show (authority.afterEvidence evidence).members =
        authority.members.filter (fun entry ↦ retained entry.1) by
      rfl]
    rw [mass_filter]
    apply mass_congr
    intro entry _
    simp
  have retainedRight : retainedQuorum authority retained right = true := by
    simpa only [Authority.hasQuorum, retainedQuorum, supportBridge, totalBridge]
      using rightQuorum
  exact retainedQuorums_shareHonest authority retained honest left right unique
    honestRetained honestQuorum leftQuorum retainedRight

theorem afterEvidenceQuorums_shareHonest_both (authority : Authority)
    (leftEvidence rightEvidence : List CarriedEvidence)
    (honest left right : List ValidatorId)
    (unique : (authority.members.map Prod.fst).Nodup)
    (leftSafe : ∀ item ∈ leftEvidence, item.proof.offender ∉ honest)
    (rightSafe : ∀ item ∈ rightEvidence, item.proof.offender ∉ honest)
    (honestQuorum : authority.hasQuorum honest = true)
    (leftQuorum : (authority.afterEvidence leftEvidence).hasQuorum left = true)
    (rightQuorum : (authority.afterEvidence rightEvidence).hasQuorum right = true) :
    ∃ signer, signer ∈ honest ∧ signer ∈ left ∧ signer ∈ right := by
  apply retainedQuorums_shareHonest_both authority
    (retainedAfterEvidence leftEvidence) (retainedAfterEvidence rightEvidence)
    honest left right unique
  · exact honest_retainedAfterEvidence authority leftEvidence honest leftSafe
  · exact honest_retainedAfterEvidence authority rightEvidence honest rightSafe
  · exact honestQuorum
  · rw [← afterEvidence_hasQuorum_eq_retainedQuorum authority leftEvidence left unique]
    exact leftQuorum
  · rw [← afterEvidence_hasQuorum_eq_retainedQuorum authority rightEvidence right unique]
    exact rightQuorum

end BFT
