import Base
import ../model/kernel.bend as K
import ./quorum_gates.bend as Q
import ./reduced_quorum_gate.bend as R
import ./feasibility.bend as F
import ./catchup_gate.bend as C
import ./reachable_safety.bend as S
import ./reachable_execution.bend as E
import ./network_execution.bend as N
import ./network_liveness.bend as NL

type Candidate is Data:
  Candidate{prefix: K.Chain(), tip: K.Block, valid: Bool}

def Candidate.target(candidate: Candidate) -> Nat:
  match candidate:
    case Candidate{_,tip,_}: K.Block.id(tip)

def Candidate.chain(candidate: Candidate) -> K.Chain():
  match candidate:
    case Candidate{prefix,tip,_}: List.append(&2,K.Block,prefix,[tip])

def Candidate.valid(candidate: Candidate) -> Bool:
  match candidate:
    case Candidate{_,_,valid}: valid

def Inventory() -> Data:
  List<&2,Candidate>

def selected(inventory: Inventory()) -> Maybe<&2,Candidate>:
  match inventory:
    case Nil{}: None{}
    case Con{first,_}: Some{first}

def Candidate.order(+best: Candidate, +candidate: Candidate) -> Cmp:
  K.compare_chains(Candidate.chain(best),Candidate.chain(candidate))

def NotWorseOrder(order: Cmp) -> Data:
  match order:
    case LT{}: Unit
    case EQ{}: Unit
    case GT{}: Empty

def NotWorse(+best: Candidate, +candidate: Candidate) -> Data:
  NotWorseOrder(Candidate.order(best,candidate))

def RankedAll(+best: Candidate, +candidates: Inventory()) -> Data:
  match candidates:
    case Nil{}: Unit
    case Con{candidate,rest}:
      Sigma<&2,&2,NotWorse(best,candidate),_ => RankedAll(best,rest)>

type CanonicalInventory is Data:
  CanonicalInventory{selected: Candidate, rest: Inventory(),
    selected_valid: {Candidate.valid(selected) == True{} : Bool},
    selected_best: RankedAll(selected,selected <> rest)}

def CanonicalInventory.candidates(inventory: CanonicalInventory) -> Inventory():
  match inventory:
    case CanonicalInventory{selected,rest,_,_}: selected <> rest

def CanonicalInventory.selected(inventory: CanonicalInventory) -> Candidate:
  match inventory:
    case CanonicalInventory{selected,_,_,_}: selected

# Observations have exactly one row per honest validator. A nonempty honest
# list therefore cannot be paired with an empty observation set.
type HonestObservation<-validator: Nat> is Data:
  HonestObservation{inventory: Inventory()}

def HonestObservation.inventory(+validator: Nat,
    observation: HonestObservation<validator>) -> Inventory():
  match observation:
    case HonestObservation{inventory}: inventory

def Observations(+honest: List<&2,Nat>) -> Data:
  match honest:
    case Nil{}: Unit
    case Con{validator,rest}:
      Sigma<&2,&2,HonestObservation<validator>,_ => Observations(rest)>

def Delivered(+honest: List<&2,Nat>, +inventory: Inventory(),
    +observed: Observations(honest)) -> Data:
  match honest:
    case Nil{}: Unit
    case Con{validator,rest}:
      (observation,tail) = observed
      Sigma<&2,&2,
        {HonestObservation.inventory(validator,observation) == inventory : Inventory()},
        _ => Delivered(rest,inventory,tail)>

def SelectedAll(+honest: List<&2,Nat>, +best: Candidate,
    +observed: Observations(honest)) -> Data:
  match honest:
    case Nil{}: Unit
    case Con{validator,rest}:
      (observation,tail) = observed
      Sigma<&2,&2,
        {selected(HonestObservation.inventory(validator,observation)) ==
          Some{best} : Maybe<&2,Candidate>},
        _ => SelectedAll(rest,best,tail)>

def delivered_selects(+honest: List<&2,Nat>, +best: Candidate,
    +rest: Inventory(), +observed: Observations(honest),
    delivered: Delivered(honest,best <> rest,observed)) ->
    SelectedAll(honest,best,observed):
  match honest:
    case Nil{}: Unit{}
    case Con{validator,honest_rest}:
      (observation,tail) = observed
      (same,next) = delivered
      selected_same :
        {selected(HonestObservation.inventory(validator,observation)) ==
          Some{best} : Maybe<&2,Candidate>} =
        %Equal.sym(Inventory(),HonestObservation.inventory(validator,observation),
          best <> rest,same) :
          {selected(_) == Some{best} : Maybe<&2,Candidate>}; {==}
      (selected_same,
        delivered_selects(honest_rest,best,rest,tail,next))

type Ready<-honest: List<&2,Nat>, -parent: K.ScannedTarget,
    -parent_chain: K.Chain()> is Data:
  QuorumReady{
    projected_chain:
      {K.target(parent) == K.chain_target(parent_chain) : Nat},
    authority_nonempty: K.NonEmptyAuthority<K.authority(parent)>,
    honest_nonempty: K.NonEmptySigners<honest>,
    parent_quorum:
      {K.has_quorum(K.authority(parent),honest) == True{} : Bool},
    endorsements: K.EndorsedAll(honest,parent)}

# One progress step combines the scanned-state transition and the actual Block
# chain extension. Its endorsements and quorum are checked at the parent.
type HonestStep<-honest: List<&2,Nat>, -parent: K.ScannedTarget,
    -parent_chain: K.Chain(), -child: K.ScannedTarget,
    -child_chain: K.Chain()> is Data:
  HonestStep{block: K.Block, offenders: List<&2,Nat>,
    admissible:
      K.AdmissibleChild<honest,parent,parent_chain,block,offenders>,
    built:
      {child == K.child(parent,K.Block.id(block),honest,offenders) : K.ScannedTarget},
    chain_extended:
      {child_chain == List.append(&2,K.Block,parent_chain,[block]) : K.Chain()}}

def equality_trans(-A: Data, +first: A, +middle: A, +last: A,
    first_middle: {first == middle : A},
    middle_last: {middle == last : A}) -> {first == last : A}:
  %middle_last : {first == _ : A}
  first_middle

def nonempty_same_authority(+left: K.Authority, +right: K.Authority,
    same: {left == right : K.Authority},
    nonempty: K.NonEmptyAuthority<left>) -> K.NonEmptyAuthority<right>:
  match nonempty:
    case K.NonEmptyAuthority{+first,+rest,built}:
      members_same = Equal.cong(K.Authority,List<&2,Nat>,K.Authority.members,
        left,right,same)
      right_built = equality_trans(List<&2,Nat>,K.Authority.members(right),
        K.Authority.members(left),first <> rest,
        Equal.sym(List<&2,Nat>,K.Authority.members(left),
          K.Authority.members(right),members_same),built)
      K.NonEmptyAuthority{first,rest,right_built}

def quorum_same_authority(+honest: List<&2,Nat>, +left: K.Authority,
    +right: K.Authority, same: {left == right : K.Authority},
    quorum: {K.has_quorum(left,honest) == True{} : Bool}) ->
    {K.has_quorum(right,honest) == True{} : Bool}:
  quorum_same = Equal.cong(K.Authority,Bool,
    authority => K.has_quorum(authority,honest),left,right,same)
  equality_trans(Bool,K.has_quorum(right,honest),K.has_quorum(left,honest),
    True{},Equal.sym(Bool,K.has_quorum(left,honest),
      K.has_quorum(right,honest),quorum_same),quorum)

def endorsements_same_authority(+honest: List<&2,Nat>,
    +left: K.ScannedTarget, +right: K.ScannedTarget,
    +same: {K.authority(left) == K.authority(right) : K.Authority},
    endorsements: K.EndorsedAll(honest,left)) -> K.EndorsedAll(honest,right):
  match honest:
    case Nil{}: Unit{}
    case Con{signer,rest}:
      (endorsed,next) = endorsements
      endorsement_same = Equal.cong(K.Authority,Bool,
        authority => K.contains(K.Authority.members(authority),signer),
        K.authority(left),K.authority(right),same)
      right_endorsed = equality_trans(Bool,K.endorsed(signer,right),
        K.endorsed(signer,left),True{},
        Equal.sym(Bool,K.endorsed(signer,left),K.endorsed(signer,right),
          endorsement_same),endorsed)
      (right_endorsed,
        endorsements_same_authority(rest,left,right,same,next))

def endorsements_cast(+left: List<&2,Nat>, +right: List<&2,Nat>,
    +parent: K.ScannedTarget, same: {left == right : List<&2,Nat>},
    endorsements: K.EndorsedAll(left,parent)) ->
    K.EndorsedAll(right,parent):
  %same : K.EndorsedAll(_,parent)
  endorsements

def quorum_signers_cast(+authority: K.Authority,
    +left: List<&2,Nat>, +right: List<&2,Nat>,
    same: {left == right : List<&2,Nat>},
    quorum: {K.has_quorum(authority,left) == True{} : Bool}) ->
    {K.has_quorum(authority,right) == True{} : Bool}:
  %same : {K.has_quorum(authority,_) == True{} : Bool}
  quorum

def endorsed_head(+signer: Nat, +rest: List<&2,Nat>,
    +parent: K.ScannedTarget,
    endorsements: K.EndorsedAll(signer <> rest,parent)) ->
    {K.endorsed(signer,parent) == True{} : Bool}:
  match endorsements:
    case (endorsed,_): endorsed

def pick_true(-A: Data, +condition: Bool, +yes: A, +no: A,
    proof: {condition == True{} : Bool}) ->
    {Bool.pick(A,condition,yes,no) == yes : A}:
  match condition:
    case False{}:
      Empty.absurd({Bool.pick(A,condition,yes,no) == yes : A},
        Q.false_empty(proof))
    case True{}: {==}

def child_q1_of_parent_quorum(+parent: K.ScannedTarget, +target: Nat,
    +signers: List<&2,Nat>, +offenders: List<&2,Nat>,
    quorum: {K.has_quorum(K.authority(parent),signers) == True{} : Bool}) ->
    {K.q1(K.child(parent,target,signers,offenders)) == parent : K.ScannedTarget}:
  match parent:
    case K.ScannedTarget{layers}:
      match layers:
        case Nil{}:
          Empty.absurd(
            {K.q1(K.child(parent,target,signers,offenders)) == parent : K.ScannedTarget},
            Q.false_empty(quorum))
        case Con{layer,rest}:
          chosen = Bool.pick(List<&2,K.Layer>,
            K.has_quorum(K.authority(K.ScannedTarget{layer <> rest}),signers),
            layer <> rest,K.scan_go(layer <> rest,signers))
          layers_equal = pick_true(List<&2,K.Layer>,
            K.has_quorum(K.authority(K.ScannedTarget{layer <> rest}),signers),
            layer <> rest,K.scan_go(layer <> rest,signers),quorum)
          Equal.cong(List<&2,K.Layer>,K.ScannedTarget,
            layers => K.ScannedTarget{layers},chosen,layer <> rest,layers_equal)

def HonestStep.q1(+honest: List<&2,Nat>, +parent: K.ScannedTarget,
    +parent_chain: K.Chain(), +child: K.ScannedTarget,
    +child_chain: K.Chain(),
    step: HonestStep<honest,parent,parent_chain,child,child_chain>) ->
    {K.q1(child) == parent : K.ScannedTarget}:
  match step:
    case HonestStep{+block,+offenders,admissible,built,_}:
      match admissible:
        case K.AdmissibleChild{_,_,quorum,_,_,_,_}:
          child_step = child_q1_of_parent_quorum(parent,K.Block.id(block),honest,
            offenders,quorum)
          mapped = Equal.cong(K.ScannedTarget,K.ScannedTarget,K.q1,child,
            K.child(parent,K.Block.id(block),honest,offenders),built)
          F.trans(K.q1(child),
            K.q1(K.child(parent,K.Block.id(block),honest,offenders)),parent,
            mapped,child_step)

def HonestStep.descends(+honest: List<&2,Nat>, +parent: K.ScannedTarget,
    +parent_chain: K.Chain(), +child: K.ScannedTarget,
    +child_chain: K.Chain(),
    step: HonestStep<honest,parent,parent_chain,child,child_chain>) ->
    K.ChildOf<parent,parent_chain,child,child_chain>:
  match step:
    case HonestStep{block,offenders,_,built,chain_extended}:
      K.ChildOf{block,honest,offenders,built,chain_extended}

def HonestStep.block(+honest: List<&2,Nat>, +parent: K.ScannedTarget,
    +parent_chain: K.Chain(), +child: K.ScannedTarget,
    +child_chain: K.Chain(),
    step: HonestStep<honest,parent,parent_chain,child,child_chain>) -> K.Block:
  match step:
    case HonestStep{block,_,_,_,_}: block

def HonestStep.extension(+honest: List<&2,Nat>,
    +parent: K.ScannedTarget, +parent_chain: K.Chain(),
    +child: K.ScannedTarget, +child_chain: K.Chain(),
    step: HonestStep<honest,parent,parent_chain,child,child_chain>) ->
    {child_chain == List.append(&2,K.Block,parent_chain,
      [HonestStep.block(honest,parent,parent_chain,child,child_chain,step)]) :
      K.Chain()}:
  match step:
    case HonestStep{block,_,_,_,chain_extended}: chain_extended

def HonestStep.suffix_nonempty(+honest: List<&2,Nat>,
    +parent: K.ScannedTarget, +parent_chain: K.Chain(),
    +child: K.ScannedTarget, +child_chain: K.Chain(),
    step: HonestStep<honest,parent,parent_chain,child,child_chain>) ->
    K.NonEmptyChain<
      [HonestStep.block(honest,parent,parent_chain,child,child_chain,step)]>:
  match step:
    case HonestStep{block,_,_,_,_}:
      K.NonEmptyChain{[],block,{==}}

def StepResult(+honest: List<&2,Nat>, +parent: K.ScannedTarget,
    +parent_chain: K.Chain()) -> Data:
  Sigma<&2,&2,K.ScannedTarget,child =>
    Sigma<&2,&2,K.Chain(),child_chain =>
      Sigma<&2,&2,
        HonestStep<honest,parent,parent_chain,child,child_chain>,_ =>
          Ready<honest,child,child_chain>>>>

# Activity supplies only a concrete proposal and readiness for that proposal's
# exact native child. It cannot smuggle in a completed quorum step or trace.
type ActivityProposal<-honest: List<&2,Nat>, -parent: K.ScannedTarget,
    -parent_chain: K.Chain()> is Data:
  ActivityProposal{block: K.Block, offenders: List<&2,Nat>,
    extension_valid: K.ValidExtension<parent_chain,block>,
    proposer_in_signers:
      {K.contains(honest,K.Block.signer(block)) == True{} : Bool},
    proposer_endorsed:
      {K.endorsed(K.Block.signer(block),parent) == True{} : Bool},
    childReady: Ready<honest,
      K.child(parent,K.Block.id(block),honest,offenders),
      List.append(&2,K.Block,parent_chain,[block])>}

type HonestActivity is Data:
  Continued{}

def nat_eq_successor_false(+value: Nat) ->
    {K.nat_eq(value,1n+value) == False{} : Bool}:
  match value:
    case 0n: {==}
    case 1n+value: nat_eq_successor_false(value)

def HonestActivity.next(+activity: HonestActivity,
    +honest: List<&2,Nat>, +parent: K.ScannedTarget,
    +parent_chain: K.Chain(),
    ready: Ready<honest,parent,parent_chain>) ->
    ActivityProposal<honest,parent,parent_chain>:
  match ready:
    case QuorumReady{projected,nonempty,honest_nonempty,quorum,+endorsements}:
      match honest_nonempty:
        case K.NonEmptySigners{+signer,+rest,+built}:
          +signer_endorsed = endorsed_head(signer,rest,parent,
            endorsements_cast(honest,signer <> rest,parent,built,endorsements))
          +block : K.Block =
            K.Block{1n+K.target(parent),signer,
              List.length(&2,K.Block,parent_chain),0n}
          +fresh_from_parent :
              {K.nat_eq(K.target(parent),K.Block.id(block)) == False{} : Bool} =
            nat_eq_successor_false(K.target(parent))
          +fresh_from_chain :
              {K.nat_eq(K.chain_target(parent_chain),K.Block.id(block)) ==
                False{} : Bool} =
            %projected :
              {K.nat_eq(_,K.Block.id(block)) == False{} : Bool};
            fresh_from_parent
          +extension_valid : K.ValidExtension<parent_chain,block> =
            K.ValidExtension{{==},fresh_from_chain}
          +child = K.child(parent,K.Block.id(block),signer <> rest,[])
          +child_parent_same = K.child_authority_empty(
            parent,K.Block.id(block),signer <> rest)
          +parent_child_same = Equal.sym(K.Authority,K.authority(child),
            K.authority(parent),child_parent_same)
          +child_nonempty = nonempty_same_authority(K.authority(parent),
            K.authority(child),parent_child_same,nonempty)
          +child_quorum = quorum_same_authority(signer <> rest,
            K.authority(parent),K.authority(child),parent_child_same,
            quorum_signers_cast(K.authority(parent),honest,signer <> rest,
              built,quorum))
          +child_endorsements = endorsements_same_authority(
            signer <> rest,parent,child,parent_child_same,
            endorsements_cast(honest,signer <> rest,parent,built,endorsements))
          +child_projected = Equal.sym(Nat,
            K.chain_target(List.append(&2,K.Block,parent_chain,[block])),
            K.Block.id(block),K.chain_target_append_block(parent_chain,block))
          +proposal : ActivityProposal<signer <> rest,parent,parent_chain> =
            ActivityProposal{block,[],extension_valid,
              Q.contains_head(signer,rest),signer_endorsed,
              QuorumReady{child_projected,child_nonempty,
              K.NonEmptySigners{signer,rest,{==}},child_quorum,
              child_endorsements}}
          %Equal.sym(List<&2,Nat>,honest,signer <> rest,built) :
            ActivityProposal<_,parent,parent_chain>
          proposal

# The proof helper, rather than the activity premise, derives the native child,
# actual chain append, parent quorum step, and preserved readiness.
def ready_step(+honest: List<&2,Nat>, +parent: K.ScannedTarget,
    +parent_chain: K.Chain(), ready: Ready<honest,parent,parent_chain>,
    proposal: ActivityProposal<honest,parent,parent_chain>) ->
    StepResult(honest,parent,parent_chain):
  match ready:
    case QuorumReady{projected,_,_,quorum,endorsements}:
      match proposal:
        case ActivityProposal{+block,+offenders,extension_valid,
            proposer_in_signers,proposer_endorsed,childReady}:
          +child = K.child(parent,K.Block.id(block),honest,offenders)
          +child_chain = List.append(&2,K.Block,parent_chain,[block])
          +admissible :
              K.AdmissibleChild<honest,parent,parent_chain,block,offenders> =
            K.AdmissibleChild{extension_valid,projected,quorum,endorsements,
              proposer_in_signers,proposer_endorsed,{==}}
          (child,(child_chain,(
            HonestStep{block,offenders,admissible,{==},{==}},
            childReady)))

type FourReadySteps<-honest: List<&2,Nat>, -base: K.ScannedTarget,
    -base_chain: K.Chain()> is Data:
  FourReadySteps{first: K.ScannedTarget, first_chain: K.Chain(),
    step1: HonestStep<honest,base,base_chain,first,first_chain>,
    ready1: Ready<honest,first,first_chain>,
    second: K.ScannedTarget, second_chain: K.Chain(),
    step2: HonestStep<honest,first,first_chain,second,second_chain>,
    ready2: Ready<honest,second,second_chain>,
    third: K.ScannedTarget, third_chain: K.Chain(),
    step3: HonestStep<honest,second,second_chain,third,third_chain>,
    ready3: Ready<honest,third,third_chain>,
    fourth: K.ScannedTarget, fourth_chain: K.Chain(),
    step4: HonestStep<honest,third,third_chain,fourth,fourth_chain>,
    ready4: Ready<honest,fourth,fourth_chain>}

def ready_steps_after_third(+honest: List<&2,Nat>,
    +base: K.ScannedTarget, +base_chain: K.Chain(),
    +first: K.ScannedTarget, +first_chain: K.Chain(),
    +step1: HonestStep<honest,base,base_chain,first,first_chain>,
    +ready1: Ready<honest,first,first_chain>,
    +second: K.ScannedTarget, +second_chain: K.Chain(),
    +step2: HonestStep<honest,first,first_chain,second,second_chain>,
    +ready2: Ready<honest,second,second_chain>,
    +third: K.ScannedTarget, +third_chain: K.Chain(),
    +step3: HonestStep<honest,second,second_chain,third,third_chain>,
    +ready3: Ready<honest,third,third_chain>,
    fourth_result: StepResult(honest,third,third_chain)) ->
    FourReadySteps<honest,base,base_chain>:
  match fourth_result:
    case (+fourth,(+fourth_chain,(+step4,ready4))):
      FourReadySteps{first,first_chain,step1,ready1,
        second,second_chain,step2,ready2,third,third_chain,step3,ready3,
        fourth,fourth_chain,step4,ready4}

def ready_steps_after_second(+honest: List<&2,Nat>,
    +base: K.ScannedTarget, +base_chain: K.Chain(),
    activity: HonestActivity,
    +first: K.ScannedTarget, +first_chain: K.Chain(),
    +step1: HonestStep<honest,base,base_chain,first,first_chain>,
    +ready1: Ready<honest,first,first_chain>,
    +second: K.ScannedTarget, +second_chain: K.Chain(),
    +step2: HonestStep<honest,first,first_chain,second,second_chain>,
    +ready2: Ready<honest,second,second_chain>,
    third_result: StepResult(honest,second,second_chain)) ->
    FourReadySteps<honest,base,base_chain>:
  match third_result:
    case (+third,(+third_chain,(+step3,+ready3))):
      ready_steps_after_third(honest,base,base_chain,
        first,first_chain,step1,ready1,second,second_chain,step2,ready2,
        third,third_chain,step3,ready3,
        ready_step(honest,third,third_chain,ready3,
          HonestActivity.next(
            activity,honest,third,third_chain,ready3)))

def ready_steps_after_first(+honest: List<&2,Nat>,
    +base: K.ScannedTarget, +base_chain: K.Chain(),
    +activity: HonestActivity,
    +first: K.ScannedTarget, +first_chain: K.Chain(),
    +step1: HonestStep<honest,base,base_chain,first,first_chain>,
    +ready1: Ready<honest,first,first_chain>,
    second_result: StepResult(honest,first,first_chain)) ->
    FourReadySteps<honest,base,base_chain>:
  match second_result:
    case (+second,(+second_chain,(+step2,+ready2))):
      ready_steps_after_second(honest,base,base_chain,activity,
        first,first_chain,step1,ready1,second,second_chain,step2,ready2,
        ready_step(honest,second,second_chain,ready2,
          HonestActivity.next(
            activity,honest,second,second_chain,ready2)))

def four_ready_steps_after_base(+honest: List<&2,Nat>,
    +base: K.ScannedTarget, +base_chain: K.Chain(),
    +activity: HonestActivity,
    first_result: StepResult(honest,base,base_chain)) ->
    FourReadySteps<honest,base,base_chain>:
  match first_result:
    case (+first,(+first_chain,(+step1,+ready1))):
      ready_steps_after_first(honest,base,base_chain,activity,
        first,first_chain,step1,ready1,
        ready_step(honest,first,first_chain,ready1,
          HonestActivity.next(
            activity,honest,first,first_chain,ready1)))

def four_ready_steps(+honest: List<&2,Nat>, +base: K.ScannedTarget,
    +base_chain: K.Chain(), +activity: HonestActivity,
    +baseReady: Ready<honest,base,base_chain>) ->
    FourReadySteps<honest,base,base_chain>:
  four_ready_steps_after_base(honest,base,base_chain,activity,
    ready_step(honest,base,base_chain,baseReady,
      HonestActivity.next(activity,honest,base,base_chain,baseReady)))

type LivenessResult<-best: Candidate, -honest: List<&2,Nat>,
    -observed: Observations(honest), -base: K.ScannedTarget,
    -candidates: Inventory()> is Data:
  LivenessResult{first: K.ScannedTarget, first_chain: K.Chain(),
    second: K.ScannedTarget, second_chain: K.Chain(),
    third: K.ScannedTarget, third_chain: K.Chain(),
    fourth: K.ScannedTarget, fourth_chain: K.Chain(),
    converged: SelectedAll(honest,best,observed),
    selected_valid: {Candidate.valid(best) == True{} : Bool},
    selected_best: RankedAll(best,candidates),
    base_finalized: {K.q3(third) == base : K.ScannedTarget},
    new_finalized: {K.q3(fourth) == first : K.ScannedTarget},
    first_suffix: K.Chain(),
    first_suffix_nonempty: K.NonEmptyChain<first_suffix>,
    first_extension:
      {first_chain == List.append(&2,K.Block,Candidate.chain(best),first_suffix) :
        K.Chain()},
    first_descends:
      K.ChildOf<base,Candidate.chain(best),first,first_chain>}

def liveness_from_ready_trace(+best: Candidate, +rest: Inventory(),
    +honest: List<&2,Nat>, +observed: Observations(honest),
    +base: K.ScannedTarget,
    delivered: Delivered(honest,best <> rest,observed),
    selected_valid: {Candidate.valid(best) == True{} : Bool},
    selected_best: RankedAll(best,best <> rest),
    trace: FourReadySteps<honest,base,Candidate.chain(best)>) ->
    LivenessResult<best,honest,observed,base,best <> rest>:
  match trace:
    case FourReadySteps{+first,+first_chain,+step1,_,+second,+second_chain,
        +step2,_,+third,+third_chain,+step3,_,+fourth,+fourth_chain,+step4,_}:
      +q1 = HonestStep.q1(
        honest,base,Candidate.chain(best),first,first_chain,step1)
      +q2 = HonestStep.q1(
        honest,first,first_chain,second,second_chain,step2)
      +q3 = HonestStep.q1(
        honest,second,second_chain,third,third_chain,step3)
      +q4 = HonestStep.q1(
        honest,third,third_chain,fourth,fourth_chain,step4)
      +first_block = HonestStep.block(
        honest,base,Candidate.chain(best),first,first_chain,step1)
      +first_suffix : K.Chain() = [first_block]
      LivenessResult{first,first_chain,second,second_chain,third,third_chain,
        fourth,fourth_chain,
        delivered_selects(honest,best,rest,observed,delivered),
        selected_valid,selected_best,
        F.three_quorum_steps_finalize(base,first,second,third,q1,q2,q3),
        F.four_quorum_steps_finalize_new(first,second,third,fourth,q2,q3,q4),
        first_suffix,
        HonestStep.suffix_nonempty(
          honest,base,Candidate.chain(best),first,first_chain,step1),
        HonestStep.extension(
          honest,base,Candidate.chain(best),first,first_chain,step1),
        HonestStep.descends(
          honest,base,Candidate.chain(best),first,first_chain,step1)}

def liveness_from_ready_steps(+best: Candidate, +rest: Inventory(),
    +honest: List<&2,Nat>, +observed: Observations(honest),
    +base: K.ScannedTarget,
    delivered: Delivered(honest,best <> rest,observed),
    selected_valid: {Candidate.valid(best) == True{} : Bool},
    selected_best: RankedAll(best,best <> rest),
    activity: HonestActivity,
    baseReady: Ready<honest,base,Candidate.chain(best)>) ->
    LivenessResult<best,honest,observed,base,best <> rest>:
  liveness_from_ready_trace(best,rest,honest,observed,base,delivered,
    selected_valid,selected_best,
    four_ready_steps(honest,base,Candidate.chain(best),activity,baseReady))

# Conditional asynchronous liveness from the exact ranked base. Delivery is
# honest-validator indexed; the single Ready step is invoked four times.
def ranked_descendant_conditional_liveness(+inventory: CanonicalInventory,
    +honest: List<&2,Nat>, +observed: Observations(honest),
    +authority: K.Authority,
    delivered:
      Delivered(honest,CanonicalInventory.candidates(inventory),observed),
    activity: HonestActivity,
    baseReady: Ready<honest,
      K.base(Candidate.target(CanonicalInventory.selected(inventory)),authority),
      Candidate.chain(CanonicalInventory.selected(inventory))>) ->
    LivenessResult<CanonicalInventory.selected(inventory),honest,observed,
      K.base(Candidate.target(CanonicalInventory.selected(inventory)),authority),
      CanonicalInventory.candidates(inventory)>:
  match inventory:
    case CanonicalInventory{best,rest,selected_valid,selected_best}:
      +base = K.base(Candidate.target(best),authority)
      liveness_from_ready_steps(best,rest,honest,observed,base,delivered,
        selected_valid,selected_best,activity,baseReady)

# Compatibility entry point for callers of the original theorem name.
def ranked_conditional_liveness(+inventory: CanonicalInventory,
    +honest: List<&2,Nat>, +observed: Observations(honest),
    +authority: K.Authority,
    delivered:
      Delivered(honest,CanonicalInventory.candidates(inventory),observed),
    activity: HonestActivity,
    baseReady: Ready<honest,
      K.base(Candidate.target(CanonicalInventory.selected(inventory)),authority),
      Candidate.chain(CanonicalInventory.selected(inventory))>) ->
    LivenessResult<CanonicalInventory.selected(inventory),honest,observed,
      K.base(Candidate.target(CanonicalInventory.selected(inventory)),authority),
      CanonicalInventory.candidates(inventory)>:
  ranked_descendant_conditional_liveness(inventory,honest,observed,authority,
    delivered,activity,baseReady)

# Concrete premises: one honest authority row, a validated endorsement, and a
# reusable Ready-preserving step. This makes the theorem premise visibly
# inhabited rather than a statement over an impossible function space.
def witness_block() -> K.Block:
  K.Block{1n,7n,0n,0n}

def concrete_base_ready() ->
    Ready<[7n],K.base(1n,K.Authority{[7n]}),[witness_block()]>:
  QuorumReady{{==},K.NonEmptyAuthority{7n,[],{==}},
    K.NonEmptySigners{7n,[],{==}},{==},({==},Unit{})}

def concrete_nonempty_ready_witness() ->
    Ready<[7n],K.base(1n,K.Authority{[7n]}),[witness_block()]>:
  concrete_base_ready()

def concrete_nonempty_activity_witness() -> HonestActivity:
  Continued{}

def witness_candidate() -> Candidate:
  Candidate{[],witness_block(),True{}}

def witness_inventory() -> CanonicalInventory:
  CanonicalInventory{witness_candidate(),[],{==},(Unit{},Unit{})}

def witness_observations() -> Observations([7n]):
  (HonestObservation{[witness_candidate()]},Unit{})

def witness_delivery() ->
    Delivered([7n],[witness_candidate()],witness_observations()):
  ({==},Unit{})

def concrete_ranked_liveness_witness() ->
    LivenessResult<witness_candidate(),[7n],witness_observations(),
      K.base(1n,K.Authority{[7n]}),[witness_candidate()]>:
  ranked_descendant_conditional_liveness(witness_inventory(),[7n],
    witness_observations(),K.Authority{[7n]},witness_delivery(),
    concrete_nonempty_activity_witness(),concrete_nonempty_ready_witness())

# Maintained Python-model endpoint. Selection convergence and the independently
# computed network execution now meet in one result: the same NetworkExecution
# contains native finality witnesses for the selected Block chain and one valid
# strict descendant.
type NetworkConditionalLivenessResult<-root_authority: K.Authority,
    -honest: List<&2,Nat>, -before: N.ValidatorState(),
    -inventory: CanonicalInventory, -observed: Observations(honest)> is Data:
  NetworkConditionalLivenessResult{
    converged:
      SelectedAll(honest,CanonicalInventory.selected(inventory),observed),
    selected_valid:
      {Candidate.valid(CanonicalInventory.selected(inventory)) == True{} : Bool},
    selected_best:
      RankedAll(CanonicalInventory.selected(inventory),
        CanonicalInventory.candidates(inventory)),
    outcome:
      NL.NetworkLivenessResult<root_authority,honest,before,
        Candidate.chain(CanonicalInventory.selected(inventory))>}

def NetworkExecution.ranked_conditional_liveness(+actions: Nat,
    +root_authority: K.Authority, +honest: List<&2,Nat>,
    +state: N.ValidatorState(),
    execution: N.NetworkExecution(actions,root_authority,honest,state),
    +inventory: CanonicalInventory, +observed: Observations(honest),
    delivered:
      Delivered(honest,CanonicalInventory.candidates(inventory),observed),
    future:
      NL.FutureActivity<root_authority,honest,state,
        Candidate.chain(CanonicalInventory.selected(inventory))>) ->
    NetworkConditionalLivenessResult<root_authority,honest,state,inventory,
      observed>:
  match inventory:
    case CanonicalInventory{best,rest,selected_valid,selected_best}:
      NetworkConditionalLivenessResult{
        delivered_selects(honest,best,rest,observed,delivered),
        selected_valid,selected_best,
        NL.extend_with_finality(root_authority,honest,state,
          Candidate.chain(best),(actions,execution),future)}

# A non-vacuous 3-of-4 NetworkExecution witness. Votes compute their own
# block_frontier, quorums, and historical_q3 from the exact ranked target.
def network_authority() -> K.Authority:
  K.Authority{[1n,2n,3n,4n]}

def network_honest() -> List<&2,Nat>:
  [1n,2n,3n]

def network_anchor() -> K.ScannedTarget:
  K.base(0n,network_authority())

def network_selected_target() -> K.ScannedTarget:
  K.child(network_anchor(),1n,network_honest(),[])

def network_descendant_target() -> K.ScannedTarget:
  K.child(network_selected_target(),2n,network_honest(),[])

def network_third_target() -> K.ScannedTarget:
  K.child(network_descendant_target(),3n,network_honest(),[])

def network_fourth_target() -> K.ScannedTarget:
  K.child(network_third_target(),4n,network_honest(),[])

def network_vote1() -> N.Vote:
  N.Vote{1n,1n,network_third_target(),Unit{}}

def network_vote2() -> N.Vote:
  N.Vote{2n,2n,network_third_target(),Unit{}}

def network_vote3() -> N.Vote:
  N.Vote{3n,3n,network_third_target(),Unit{}}

def network_vote4() -> N.Vote:
  N.Vote{4n,1n,network_fourth_target(),({==},Unit{})}

def network_vote5() -> N.Vote:
  N.Vote{5n,2n,network_fourth_target(),({==},Unit{})}

def network_vote6() -> N.Vote:
  N.Vote{6n,3n,network_fourth_target(),({==},Unit{})}

def network_state1() -> N.ValidatorState():
  E.emit_state(N.Vote.event(network_vote1()),N.genesis())

def network_state2() -> N.ValidatorState():
  E.emit_state(N.Vote.event(network_vote2()),network_state1())

def network_state3() -> N.ValidatorState():
  E.emit_state(N.Vote.event(network_vote3()),network_state2())

def network_self_pair(+vote: N.Vote) ->
    S.ClassifiedPair<network_honest(),N.Vote.event(vote),N.Vote.event(vote)>:
  S.Ranked{Inl{C.prefix_refl(S.VoteEvent.q2(N.Vote.event(vote)))}}

def network_vote1_accepted() ->
    NL.AcceptedVote<network_authority(),network_honest(),N.genesis(),
      network_state1()>:
  NL.AcceptedVote{network_vote1(),{==},Unit{},Unit{},
    (network_self_pair(network_vote1()),Unit{}),Unit{},Inl{{==}}}

def network_vote2_accepted() ->
    NL.AcceptedVote<network_authority(),network_honest(),network_state1(),
      network_state2()>:
  NL.AcceptedVote{network_vote2(),{==},(Unit{},Unit{}),
    (Inl{{==}},Unit{}),
    (network_self_pair(network_vote2()),
      (S.OtherSigner{{==}},Unit{})),
    ((S.OtherSigner{{==}},Unit{}),Unit{}),Inl{{==}}}

def network_vote3_accepted() ->
    NL.AcceptedVote<network_authority(),network_honest(),network_state2(),
      network_state3()>:
  NL.AcceptedVote{network_vote3(),{==},(Unit{},(Unit{},Unit{})),
    (Inl{{==}},(Inl{{==}},Unit{})),
    (network_self_pair(network_vote3()),
      (S.OtherSigner{{==}},(S.OtherSigner{{==}},Unit{}))),
    ((S.OtherSigner{{==}},Unit{}),
      ((S.OtherSigner{{==}},Unit{}),Unit{})),Inl{{==}}}

def network_selected_schedule() ->
    NL.VoteSchedule(3n,network_authority(),network_honest(),N.genesis(),
      network_state3()):
  (network_state1(),(network_vote1_accepted(),
    (network_state2(),(network_vote2_accepted(),
      (network_state3(),(network_vote3_accepted(),{==}))))))

def network_clean() ->
    R.Clean(K.Authority.members(network_authority()),[],network_honest()):
  ({==},({==},({==},({==},Unit{}))))

def network_selected_delivery() ->
    NL.FinalityDelivery<network_authority(),network_honest(),N.genesis(),[1n]>:
  NL.FinalityDelivery{3n,network_state3(),[1n,2n,3n,4n],[],
    network_selected_schedule(),{==},
    (C.prefix_refl([1n]),(C.prefix_refl([1n]),
      (C.prefix_refl([1n]),Unit{}))),
    (Unit{},(Unit{},(Unit{},Unit{}))),network_clean(),{==}}

def network_selected_after() -> N.ValidatorState():
  NL.FinalityDelivery.after(network_authority(),network_honest(),N.genesis(),
    [1n],network_selected_delivery())

def network_selected_lock() -> S.FinalityLock:
  NL.FinalityDelivery.lock(network_authority(),network_honest(),N.genesis(),
    [1n],network_selected_delivery())

def network_state4() -> N.ValidatorState():
  E.emit_state(N.Vote.event(network_vote4()),network_selected_after())

def network_state5() -> N.ValidatorState():
  E.emit_state(N.Vote.event(network_vote5()),network_state4())

def network_state6() -> N.ValidatorState():
  E.emit_state(N.Vote.event(network_vote6()),network_state5())

def network_vote4_q3_ready() ->
    S.Q3Ready([network_selected_lock()],N.Vote.event(network_vote4())):
  Inr{(network_selected_lock(),
    (S.member_head(S.FinalityLock,network_selected_lock(),[]),
      ({==},Unit{})))}

def network_vote5_q3_ready() ->
    S.Q3Ready([network_selected_lock()],N.Vote.event(network_vote5())):
  Inr{(network_selected_lock(),
    (S.member_head(S.FinalityLock,network_selected_lock(),[]),
      ({==},Unit{})))}

def network_vote6_q3_ready() ->
    S.Q3Ready([network_selected_lock()],N.Vote.event(network_vote6())):
  Inr{(network_selected_lock(),
    (S.member_head(S.FinalityLock,network_selected_lock(),[]),
      ({==},Unit{})))}

def network_vote4_accepted() ->
    NL.AcceptedVote<network_authority(),network_honest(),
      network_selected_after(),network_state4()>:
  NL.AcceptedVote{network_vote4(),{==},
    (Unit{},(Unit{},(Unit{},Unit{}))),
    (Inl{{==}},(Inl{{==}},(Inr{{==}},Unit{}))),
    (network_self_pair(network_vote4()),
      (S.OtherSigner{{==}},(S.OtherSigner{{==}},
        (S.ReverseTime{Unit{}},Unit{})))),
    ((S.OtherSigner{{==}},Unit{}),
      ((S.OtherSigner{{==}},Unit{}),
        ((S.Ranked{Inl{({==},Unit{})}},Unit{}),Unit{}))),
    network_vote4_q3_ready()}

def network_vote5_accepted() ->
    NL.AcceptedVote<network_authority(),network_honest(),network_state4(),
      network_state5()>:
  NL.AcceptedVote{network_vote5(),{==},
    (Unit{},(Unit{},(Unit{},(Unit{},Unit{})))),
    (Inl{{==}},(Inl{{==}},(Inr{{==}},(Inl{{==}},Unit{})))),
    (network_self_pair(network_vote5()),
      (S.OtherSigner{{==}},(S.OtherSigner{{==}},
        (S.ReverseTime{Unit{}},(S.OtherSigner{{==}},Unit{}))))),
    ((S.OtherSigner{{==}},Unit{}),
      ((S.OtherSigner{{==}},Unit{}),
        ((S.Ranked{Inl{({==},Unit{})}},Unit{}),
          ((S.OtherSigner{{==}},Unit{}),Unit{})))),
    network_vote5_q3_ready()}

def network_vote6_accepted() ->
    NL.AcceptedVote<network_authority(),network_honest(),network_state5(),
      network_state6()>:
  NL.AcceptedVote{network_vote6(),{==},
    (Unit{},(Unit{},(Unit{},(Unit{},(Unit{},Unit{}))))),
    (Inl{{==}},(Inl{{==}},(Inr{{==}},
      (Inl{{==}},(Inl{{==}},Unit{}))))),
    (network_self_pair(network_vote6()),
      (S.OtherSigner{{==}},(S.OtherSigner{{==}},
        (S.ReverseTime{Unit{}},(S.OtherSigner{{==}},
          (S.OtherSigner{{==}},Unit{})))))),
    ((S.OtherSigner{{==}},Unit{}),
      ((S.OtherSigner{{==}},Unit{}),
        ((S.Ranked{Inl{({==},Unit{})}},Unit{}),
          ((S.OtherSigner{{==}},Unit{}),
            ((S.OtherSigner{{==}},Unit{}),Unit{}))))),
    network_vote6_q3_ready()}

def network_descendant_schedule() ->
    NL.VoteSchedule(3n,network_authority(),network_honest(),
      network_selected_after(),network_state6()):
  (network_state4(),(network_vote4_accepted(),
    (network_state5(),(network_vote5_accepted(),
      (network_state6(),(network_vote6_accepted(),{==}))))))

def network_descendant_delivery() ->
    NL.FinalityDelivery<network_authority(),network_honest(),
      network_selected_after(),[1n,2n]>:
  NL.FinalityDelivery{3n,network_state6(),[1n,2n,3n,4n,5n],[],
    network_descendant_schedule(),{==},
    (C.prefix_refl([1n,2n]),(C.prefix_refl([1n,2n]),
      (C.prefix_refl([1n,2n]),Unit{}))),
    (Unit{},(Unit{},(Unit{},Unit{}))),network_clean(),{==}}

def network_selected_block() -> K.Block:
  K.Block{1n,1n,0n,0n}

def network_descendant_block() -> K.Block:
  K.Block{2n,1n,1n,0n}

def network_descendant_admissible() ->
    K.AdmissibleChild<network_honest(),network_selected_target(),
      [network_selected_block()],network_descendant_block(),[]>:
  K.AdmissibleChild{K.ValidExtension{{==},{==}},{==},{==},
    ({==},({==},({==},Unit{}))),{==},{==},{==}}

def network_future_activity() ->
    NL.FutureActivity<network_authority(),network_honest(),N.genesis(),
      [network_selected_block()]>:
  NL.FutureActivity{network_selected_target(),network_descendant_block(),[],
    network_descendant_admissible(),network_selected_delivery(),
    network_descendant_delivery()}

def network_candidate() -> Candidate:
  Candidate{[],network_selected_block(),True{}}

def network_inventory() -> CanonicalInventory:
  CanonicalInventory{network_candidate(),[],{==},(Unit{},Unit{})}

def network_observations() -> Observations(network_honest()):
  (HonestObservation{[network_candidate()]},
    (HonestObservation{[network_candidate()]},
      (HonestObservation{[network_candidate()]},Unit{})))

def network_delivery() ->
    Delivered(network_honest(),[network_candidate()],network_observations()):
  ({==},({==},({==},Unit{})))

def network_execution() ->
    N.NetworkExecution(0n,network_authority(),network_honest(),N.genesis()):
  {==}

# Concrete theorem application: a non-Genesis selected chain and its valid
# strict child become Finalized in the same reachable 3-of-4 NetworkExecution.
def concrete_network_execution_liveness_witness() ->
    NetworkConditionalLivenessResult<network_authority(),network_honest(),
      N.genesis(),network_inventory(),network_observations()>:
  NetworkExecution.ranked_conditional_liveness(0n,network_authority(),
    network_honest(),N.genesis(),network_execution(),network_inventory(),
    network_observations(),network_delivery(),network_future_activity())

def network_result_safety(
    result: NetworkConditionalLivenessResult<network_authority(),
      network_honest(),N.genesis(),network_inventory(),
      network_observations()>) ->
    Sigma<&2,&2,K.Chain(),descendant_chain =>
      C.Compatible([1n],K.chain_path(descendant_chain))>:
  match result:
    case NetworkConditionalLivenessResult{_,_,_,outcome}:
      NL.NetworkLivenessResult.finalized_safety(network_authority(),
        network_honest(),N.genesis(),[network_selected_block()],outcome,{==})

# The two finality witnesses produced above also satisfy the maintained safety
# theorem on that exact execution.
def concrete_network_execution_safety_witness() ->
    Sigma<&2,&2,K.Chain(),descendant_chain =>
      C.Compatible([1n],K.chain_path(descendant_chain))>:
  network_result_safety(concrete_network_execution_liveness_witness())
