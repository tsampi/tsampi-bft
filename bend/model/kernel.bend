import Base

# Consensus values only. Networking, owners, signatures, hashing, persistence,
# and evidence verification are outside this model.

type Block is Data:
  Block{id: Nat, signer: Nat, position: Nat, score: Nat}

type Authority is Data:
  # One row per unit of stake. Repeated identities are weights, not duplicate
  # signatures. This is equivalent to finite nonnegative integer weights.
  Authority{members: List<&2,Nat>}

type Layer is Data:
  Layer{target: Nat, authority: Authority, parent_signers: List<&2,Nat>}

type ScannedTarget is Data:
  ScannedTarget{layers: List<&2,Layer>}

type ActionKind is Data:
  SignVote{}
  Propose{}
  PublishVote{}
  PublishProposal{}
  DeliverVote{}
  DeliverProposal{}
  Idle{}

def Chain() -> Data:
  List<&2,Block>

def Authority.members(authority: Authority) -> List<&2,Nat>:
  match authority:
    case Authority{members}: members

def ScannedTarget.layers(target: ScannedTarget) -> List<&2,Layer>:
  match target:
    case ScannedTarget{layers}: layers

def Block.id(block: Block) -> Nat:
  match block:
    case Block{id,_,_,_}: id

def Block.signer(block: Block) -> Nat:
  match block:
    case Block{_,signer,_,_}: signer

def Block.position(block: Block) -> Nat:
  match block:
    case Block{_,_,position,_}: position

def Block.score(block: Block) -> Nat:
  match block:
    case Block{_,_,_,score}: score

# Safety finality uses identifier paths while ranking uses full Blocks. This
# projection is the explicit bridge between those two views of one chain.
def chain_path(chain: Chain()) -> List<&2,Nat>:
  match chain:
    case Nil{}: []
    case Con{block,rest}: Block.id(block) <> chain_path(rest)

def chain_target(chain: Chain()) -> Nat:
  match chain:
    case Nil{}: 0n
    case Con{block,Nil{}}: Block.id(block)
    case Con{block,rest}: chain_target(rest)

# A valid extension occupies the next chain position and has a fresh identity.
# Block identities stand for hashes, so their numeric order has no meaning.
# These are raw block checks, not a completed protocol step or finality fact.
type ValidExtension<-parent_chain: Chain(), -block: Block> is Data:
  ValidExtension{
    position:
      {Block.position(block) == List.length(&2,Block,parent_chain) : Nat},
    fresh:
      {nat_eq(chain_target(parent_chain),Block.id(block)) == False{} : Bool}}

def chain_path_append_block(+chain: Chain(), +block: Block) ->
    {chain_path(List.append(&2,Block,chain,[block])) ==
      List.append(&2,Nat,chain_path(chain),[Block.id(block)]) : List<&2,Nat>}:
  match chain:
    case Nil{}: {==}
    case Con{head,rest}:
      Equal.cong(List<&2,Nat>,List<&2,Nat>,
        tail => Block.id(head) <> tail,
        chain_path(List.append(&2,Block,rest,[block])),
        List.append(&2,Nat,chain_path(rest),[Block.id(block)]),
        chain_path_append_block(rest,block))

def chain_target_append_block(+chain: Chain(), +block: Block) ->
    {chain_target(List.append(&2,Block,chain,[block])) == Block.id(block) : Nat}:
  match chain:
    case Nil{}: {==}
    case Con{head,rest}:
      match rest:
        case Nil{}: {==}
        case Con{next,tail}:
          chain_target_append_block(next <> tail,block)

def Layer.target(layer: Layer) -> Nat:
  match layer:
    case Layer{target,_,_}: target

def Layer.authority(layer: Layer) -> Authority:
  match layer:
    case Layer{_,authority,_}: authority

def Layer.parent_signers(layer: Layer) -> List<&2,Nat>:
  match layer:
    case Layer{_,_,parent_signers}: parent_signers

# Paths omit the oldest anchor layer, which represents Python's Genesis
# frontier. Remaining layer targets are returned oldest first, like
# Validator.ancestry(...)[::-1].
def scanned_path_go(layers: List<&2,Layer>) -> List<&2,Nat>:
  match layers:
    case Nil{}: []
    case Con{layer,Nil{}}: []
    case Con{layer,rest}:
      List.append(&2,Nat,scanned_path_go(rest),[Layer.target(layer)])

def scanned_path(target: ScannedTarget) -> List<&2,Nat>:
  scanned_path_go(ScannedTarget.layers(target))

def nat_eq(a: Nat, b: Nat) -> Bool:
  Cmp.is_eq(Nat.cmp(a,b))

def contains(xs: List<&2,Nat>, +wanted: Nat) -> Bool:
  match xs:
    case Nil{}: False{}
    case Con{x,xs}: nat_eq(x,wanted) || contains(xs,wanted)

def total(authority: Authority) -> Nat:
  List.length(&2,Nat,Authority.members(authority))

# Iterating stake rows, instead of the signer list, means repeated signatures
# never add weight.
def support_weight_go(authority: List<&2,Nat>, +signers: List<&2,Nat>) -> Nat:
  match authority:
    case Nil{}: 0n
    case Con{+id,members}:
      Nat.add(Bool.pick(Nat,contains(signers,id),1n,0n),support_weight_go(members,signers))

def support_weight(authority: Authority, signers: List<&2,Nat>) -> Nat:
  support_weight_go(Authority.members(authority),signers)

def has_quorum(+authority: Authority, +signers: List<&2,Nat>) -> Bool:
  (Nat.mul(2n,total(authority)) < Nat.mul(3n,support_weight(authority,signers)) : Nat)

def after_evidence_go(authority: List<&2,Nat>, +offenders: List<&2,Nat>) -> List<&2,Nat>:
  match authority:
    case Nil{}: []
    case Con{+id,members}:
      List.append(&2,Nat,Bool.pick(List<&2,Nat>,contains(offenders,id),[],[id]),
        after_evidence_go(members,offenders))

def after_evidence(authority: Authority, offenders: List<&2,Nat>) -> Authority:
  Authority{after_evidence_go(Authority.members(authority),offenders)}

# Higher score wins. A smaller Block identity breaks a score tie.
def compare_blocks_go(+left: Block, +right: Block, score: Cmp) -> Cmp:
  match score:
    case LT{}: GT{}
    case GT{}: LT{}
    case EQ{}: Nat.cmp(Block.id(left),Block.id(right))

def compare_blocks(+left: Block, +right: Block) -> Cmp:
  compare_blocks_go(left,right,Nat.cmp(Block.score(left),Block.score(right)))

def compare_chains_go(+a: Block, +b: Block, identity: Cmp, equal: Unit -> Cmp) -> Cmp:
  match identity:
    case EQ{}: equal(Unit{})
    case LT{}: compare_blocks(a,b)
    case GT{}: compare_blocks(a,b)

# Exact first-divergence comparison. LT means the left chain wins.
def compare_chains(left: Chain, right: Chain) -> Cmp:
  match left right:
    case Nil{} Nil{}: EQ{}
    case Nil{} Con{_,_}: GT{}
    case Con{_,_} Nil{}: LT{}
    case Con{+a,as} Con{+b,bs}:
      compare_chains_go(a,b,Nat.cmp(Block.id(a),Block.id(b)),u => compare_chains(as,bs))

def base(target: Nat, authority: Authority) -> ScannedTarget:
  ScannedTarget{[Layer{target,authority,[]}]}

def authority(target: ScannedTarget) -> Authority:
  match target:
    case ScannedTarget{Nil{}}: Authority{[]}
    case ScannedTarget{Con{layer,_}}: Layer.authority(layer)

# In this proof model, an endorsement is validated when its signer is a member
# of the authority that governs the parent state. Cryptographic verification is
# outside the model boundary.
def endorsed(+signer: Nat, +parent: ScannedTarget) -> Bool:
  contains(Authority.members(authority(parent)),signer)

# Every signer used for progress is checked against the exact parent authority.
def EndorsedAll(+signers: List<&2,Nat>, +parent: ScannedTarget) -> Data:
  match signers:
    case Nil{}: Unit
    case Con{signer,rest}:
      Sigma<&2,&2,{endorsed(signer,parent) == True{} : Bool},
        _ => EndorsedAll(rest,parent)>

def target(target: ScannedTarget) -> Nat:
  match target:
    case ScannedTarget{Nil{}}: 0n
    case ScannedTarget{Con{layer,_}}: Layer.target(layer)

# A carrier is admitted with the parent authority. Its verified evidence only
# changes the authority used by its children.
def child(+parent: ScannedTarget, target: Nat, signers: List<&2,Nat>, offenders: List<&2,Nat>) -> ScannedTarget:
  ScannedTarget{Layer{target,after_evidence(authority(parent),offenders),signers} <>
    ScannedTarget.layers(parent)}

# Python-style child admission. The parent state admits the endorsements; only
# then does verified evidence determine the child's output authority.
type AdmissibleChild<-signers: List<&2,Nat>, -parent: ScannedTarget,
    -parent_chain: Chain(), -block: Block,
    -offenders: List<&2,Nat>> is Data:
  AdmissibleChild{
    extension_valid: ValidExtension<parent_chain,block>,
    projected_parent:
      {target(parent) == chain_target(parent_chain) : Nat},
    parent_quorum:
      {has_quorum(authority(parent),signers) == True{} : Bool},
    endorsements: EndorsedAll(signers,parent),
    proposer_in_signers:
      {contains(signers,Block.signer(block)) == True{} : Bool},
    proposer_endorsed:
      {endorsed(Block.signer(block),parent) == True{} : Bool},
    output_authority:
      {authority(child(parent,Block.id(block),signers,offenders)) ==
        after_evidence(authority(parent),offenders) : Authority}}

def AdmissibleChild.extension(+signers: List<&2,Nat>,
    +parent: ScannedTarget, +parent_chain: Chain(), +block: Block,
    +offenders: List<&2,Nat>,
    admissible: AdmissibleChild<signers,parent,parent_chain,block,offenders>) ->
    ValidExtension<parent_chain,block>:
  match admissible:
    case AdmissibleChild{extension,_,_,_,_,_,_}: extension

# Structural evidence that a chain has at least one Block.
type NonEmptyChain<-chain: Chain()> is Data:
  NonEmptyChain{prefix: Chain(), tip: Block,
    built: {chain == List.append(&2,Block,prefix,[tip]) : Chain()}}

# Structural evidence that an authority has at least one stake row.
type NonEmptyAuthority<-authority: Authority> is Data:
  NonEmptyAuthority{first: Nat, rest: List<&2,Nat>,
    built: {Authority.members(authority) == first <> rest : List<&2,Nat>}}

# Structural evidence that an honest signer set has a proposer.
type NonEmptySigners<-signers: List<&2,Nat>> is Data:
  NonEmptySigners{first: Nat, rest: List<&2,Nat>,
    built: {signers == first <> rest : List<&2,Nat>}}

# Native ancestry evidence couples the scanned-state child relation to the
# actual ranked Block chain. A sibling state cannot inhabit this type.
type ChildOf<-parent: ScannedTarget, -parent_chain: Chain(),
    -descendant: ScannedTarget, -descendant_chain: Chain()> is Data:
  ChildOf{block: Block, signers: List<&2,Nat>, offenders: List<&2,Nat>,
    built: {descendant == child(parent,Block.id(block),signers,offenders) : ScannedTarget},
    chain_extended: {descendant_chain == List.append(&2,Block,parent_chain,[block]) : Chain()}}

def after_evidence_go_empty(+members: List<&2,Nat>) ->
    {after_evidence_go(members,[]) == members : List<&2,Nat>}:
  match members:
    case Nil{}: {==}
    case Con{id,rest}:
      %after_evidence_go_empty(rest) :
        {after_evidence_go(id <> rest,[]) == id <> _ : List<&2,Nat>}
      {==}

def after_evidence_empty(+authority: Authority) ->
    {after_evidence(authority,[]) == authority : Authority}:
  match authority:
    case Authority{members}:
      %after_evidence_go_empty(members) :
        {after_evidence(Authority{members},[]) == Authority{_} : Authority}
      {==}

def child_authority_empty(+parent: ScannedTarget, +target: Nat,
    +signers: List<&2,Nat>) ->
    {authority(child(parent,target,signers,[])) == authority(parent) : Authority}:
  after_evidence_empty(authority(parent))

def scan_go(path: List<&2,Layer>, seen: List<&2,Nat>) -> List<&2,Layer>:
  match path:
    case Nil{}: []
    case Con{layer,Nil{}}: [layer]
    case Con{+carrier,+rest}:
      +combined : List<&2,Nat> = List.append(&2,Nat,seen,Layer.parent_signers(carrier))
      +parent : ScannedTarget = ScannedTarget{rest}
      Bool.pick(List<&2,Layer>,has_quorum(authority(parent),combined),rest,scan_go(rest,combined))

def scan(path: ScannedTarget, seen: List<&2,Nat>) -> ScannedTarget:
  ScannedTarget{scan_go(ScannedTarget.layers(path),seen)}

def q1(target: ScannedTarget) -> ScannedTarget:
  scan(target,[])

def q2(target: ScannedTarget) -> ScannedTarget:
  q1(q1(target))

def q3(target: ScannedTarget) -> ScannedTarget:
  q1(q2(target))

# Python calls these operations block_frontier, quorums, and historical_q3.
# Keep the proof kernel's small q1/q2/q3 helpers, but expose the protocol terms
# used by model/consensus.py at the public Bend boundary.
def block_frontier(target: ScannedTarget) -> ScannedTarget:
  q1(target)

type Quorums<-target: ScannedTarget> is Data:
  Quorums{q1: ScannedTarget, q2: ScannedTarget,
    first: {q1 == block_frontier(target) : ScannedTarget},
    second: {q2 == block_frontier(q1) : ScannedTarget}}

def quorums(+target: ScannedTarget) -> Quorums<target>:
  Quorums{q1(target),q2(target),{==},{==}}

def Quorums.q1(+target: ScannedTarget, value: Quorums<target>) -> ScannedTarget:
  match value:
    case Quorums{q1,_,_,_}: q1

def Quorums.q2(+target: ScannedTarget, value: Quorums<target>) -> ScannedTarget:
  match value:
    case Quorums{_,q2,_,_}: q2

def historical_q3(target: ScannedTarget) -> ScannedTarget:
  block_frontier(q2(target))

def emission_limit(kind: ActionKind) -> Nat:
  match kind:
    case SignVote{}: 1n
    case Propose{}: 2n
    case PublishVote{}: 0n
    case PublishProposal{}: 0n
    case DeliverVote{}: 0n
    case DeliverProposal{}: 0n
    case Idle{}: 0n
