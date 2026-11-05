"""Deterministic event queue for finite protocol checks, without protocol rounds.

Honest tasks use the source-derived Go owner policy; the optional hostile actor
can publish a wider class of messages. Finite progress is not a liveness proof.

Generation wakes after each changed receiver snapshot, through Go owner policy.
Every emitted object gets exactly one FIFO delivery event at every other
participant. Target and predecessor waiters retry locally after dependencies
arrive. Resource exhaustion is an error, never evidence that no protocol action
is enabled.

This ideal ingress models network/inbound_buffer.go's retained missing parent/
predecessor objects and release after admission; network/
driver_events.go wakes voting/proposal scans, and consensus/engine.go wakes a
proposal scan when later votes supply quorum. This harness ignores Go capacity
limits and internal-error handling; it is not a refinement proof of that runtime.
"""
import heapq

from consensus import (ModelError, Validator, generate_proposal, generate_vote,
                   submit_proposal, submit_vote)
from network import DEFAULT_ENDORSE_THRESHOLD, Network


class EventDelivery:
    GENERATION_DELAY = 1
    DELIVERY_DELAY = 1
    RETRY_DELAY = 1

    def __init__(self, unanimity=False, retry_dependencies=True, publisher=False,
                 network=None):
        # This option controls only the adversarial actor's chosen inbox policy.
        # Honest receivers always use Node's source-derived ingress rules.
        self.network = network if network is not None else Network(
            honest_stakes=(3, 3, 3), byzantine_stake=1,
            threshold=(1, 1) if unanimity else DEFAULT_ENDORSE_THRESHOLD)
        self.publisher = 3 if publisher else None
        if unanimity:
            if publisher:
                raise ValueError('unanimity check requires every validator honest')
            self.network.honest = (0, 1, 2, 3)
            self.network.receivers[3] = Validator.init(self.network.genesis, 3)
        self.attacker = Validator.init(self.network.genesis, 3) if publisher else None
        self.participants = tuple(self.network.honest) + ((3,) if publisher else ())
        self.retry_dependencies = retry_dependencies
        self.events, self.awake, self.pending = [], set(), {}
        # A scheduler attached to an existing prefix must allocate the unsent
        # backlog.  Successful or buffered delivery actions in that prefix are
        # already wire receipts and must never be allocated a second time.
        self.seen_votes, self.seen_proposals = set(), set()
        self.receipts = {
            action for action, _ in self.network.actions
            if action[0] in ('deliver_vote', 'deliver_proposal')
        }
        self.new_wire_receipts = set()
        self.now = self.serial = self.generated_after_receipt = 0
        self.failed_dependencies = self.published_proposals = 0
        self.publications = []
        self.first_finality_action = None
        self.first_finality_receipts = set()
        for who in self.participants:
            self.wake(who)
        self.broadcast()

    def validator(self, who):
        return self.attacker if who == self.publisher else self.network.receivers[who]

    def enqueue(self, kind, args, delay):
        self.serial += 1
        heapq.heappush(self.events, (self.now + delay, self.serial, kind, args))

    def wake(self, who):
        if who not in self.awake:
            self.awake.add(who)
            self.enqueue('generate', who, self.GENERATION_DELAY)
        for key in sorted(self.pending):
            previous = self.pending[key]
            if key[1] == who and previous != self.validator(who):
                del self.pending[key]
                self.enqueue('retry', key, self.RETRY_DELAY)

    def broadcast(self):
        for identity in sorted(self.network.votes.keys() - self.seen_votes):
            if not any(self.holds(who, 'deliver_vote', identity) for who in self.participants):
                continue
            vote = self.network.votes[identity]
            for who in sorted(self.participants):
                if who == vote.signer:
                    continue
                action = ('deliver_vote', who, identity)
                if action not in self.receipts:
                    self.enqueue('deliver', action, self.DELIVERY_DELAY)
            self.seen_votes.add(identity)
        for identity in sorted(self.network.proposals.keys() - self.seen_proposals):
            if not any(self.holds(who, 'deliver_proposal', *identity) for who in self.participants):
                continue
            block, _ = self.network.proposals[identity]
            for who in sorted(self.participants):
                if who == block.proposer:
                    continue
                action = ('deliver_proposal', who, *identity)
                if action not in self.receipts:
                    self.enqueue('deliver', action, self.DELIVERY_DELAY)
            self.seen_proposals.add(identity)

    def holds(self, who, kind, *identity):
        if who != self.publisher:
            return self.network.holds_message(who, kind, *identity)
        if kind == 'deliver_vote':
            return self.network.votes[identity[0]] in self.attacker.votes
        block, own = self.network.proposals[tuple(identity)]
        return block in self.attacker.blocks and own in self.attacker.votes

    def enabled(self, who):
        """One representative per currently enabled target or proposal parent.

        IDs are fresh deterministic fixture values. A fresh-ID replay of the
        same target without a new permitted signing transition is not a duty.
        """
        v = self.validator(who)
        if who != self.publisher:
            raise ValueError('honest work is chosen by owner policy, not generator enumeration')
        candidates = [('vote', b.id) for b in v.blocks]
        if v.latest is not None:
            candidates.append(('proposal', v.vote(v.latest).target))
        order = {'vote': 0, 'proposal': 1}
        for kind, target in sorted(candidates, key=lambda item: (item[1], order[item[0]])):
            first, second = self.network.alloc(), self.network.alloc()
            rank = self.network.rank(who)
            target_block = v.block(target)
            inner = (who, target_block.state.chain, target_block.height + 1,
                     target_block.proposer,
                     target_block.proposer_vote.inner_id if target_block.proposer_vote else None)
            old = next((vote for vote in v.votes if vote.inner == inner), None)
            vote_rank, signature = (old.race, old.sig_hash) if old else (rank, rank)
            try:
                if kind == 'vote':
                    result = generate_vote(v, target, first, vote_rank, signature)
                    yield ('sign_vote', who, target, first, vote_rank, signature), result
                else:
                    result = generate_proposal(v, target, first, second, rank, rank)
                    yield ('propose', who, target, first, second, rank, rank), result
            except ModelError:
                continue

    def generate(self, who):
        self.awake.discard(who)
        if who != self.publisher:
            before = self.validator(who)
            self.network.honest_vote(who)
            self.network.honest_proposal(who)
            self.broadcast()
            if self.validator(who) != before:
                if any(key[1] == who for key in self.receipts):
                    self.generated_after_receipt += 1
                self.wake(who)
            return
        selected = next(self.enabled(who), None)
        if selected is None:
            return
        action, result = selected
        if action[0] == 'propose' and result[1].height > self.network.max_block_height:
            raise RuntimeError('Block height budget exhausted; generation remains enabled')
        self.attacker = result[0]
        published = (('publish_vote', result[1]) if action[0] == 'sign_vote'
                     else ('publish_proposal', result[1], result[2]))
        error = self.network.step(published)
        self.publications.append(len(self.network.actions))
        self.published_proposals += action[0] == 'propose'
        if error is not None:
            raise AssertionError(('enabled action refused', action, error))
        if any(key[1] == who for key in self.receipts):
            self.generated_after_receipt += 1
        self.broadcast()
        self.wake(who)

    def deliver(self, action, retry=False):
        kind, who, *identity = action
        before = self.validator(who)
        dependency_error = False
        if not retry:
            self.receipts.add(action)
            self.new_wire_receipts.add(action)
        if who != self.publisher:
            self.network.step(action)
            dependency_error = self.network.last_delivery_status in ('buffered', 'dropped')
            after = self.validator(who)
        else:
            try:
                after = (submit_vote(before, self.network.votes[identity[0]]) if kind == 'deliver_vote'
                         else submit_proposal(before, *self.network.proposals[tuple(identity)]))
            except ModelError as exc:
                after = before
                dependency_error = exc.kind in ('missing_vote', 'missing_block')
            self.attacker = after
            if dependency_error and self.retry_dependencies:
                self.pending[action] = before
        if dependency_error:
            self.failed_dependencies += 1
        if after != before:
            self.wake(who)

    def next_event(self):
        if not self.events:
            return False
        self.now, _, kind, args = heapq.heappop(self.events)
        if kind == 'generate':
            self.generate(args)
        else:
            self.deliver(args, retry=kind == 'retry')
        if not self.network.agreement:
            raise AssertionError('conflicting finalized histories')
        if self.first_finality_action is None and any(
                v.block(v.finalized).height > 0 for v in self.network.receivers.values()):
            self.first_finality_action = len(self.network.actions)
            self.first_finality_receipts = {
                ('deliver_vote', who, vote.id)
                for vote in self.network.votes.values() for who in self.participants
                if who != vote.signer}
            self.first_finality_receipts.update(
                ('deliver_proposal', who, block.id, own.id)
                for block, own in self.network.proposals.values() for who in self.participants
                if who != block.proposer)
        return True

    def until_finalized(self, height, event_budget=3000):
        for _ in range(event_budget):
            if (all(v.block(v.finalized).height >= height for v in self.network.receivers.values())
                    and self.first_finality_receipts <= self.receipts):
                return
            if not self.next_event():
                raise AssertionError(('closed schedule below requested finality',
                                      self.network.progress_diagnostics(), self.pending))
        raise RuntimeError('event budget exhausted; no permanent-stall conclusion')
