"""Finite model checks, not Go-runtime tests or a consensus proof.

Exercise generated objects and public admission; malformed envelopes are rejection
probes. Network cases use fixed action and delivery orders.
Run: python3 -m unittest discover -s python -v
"""
import unittest
from dataclasses import replace

from consensus import (Block, Evidence, ModelError, State, Validator, block_exclusions,
                   generate_proposal, generate_vote, quorums, stage_block,
                   submit_proposal, submit_vote, verify_evidence, view_evidence)
from network import Network


def genesis(numerator=1, denominator=4):
    return Block.genesis(0, State(1, ((0, 1), (1, 1), (2, 1)),
                                  numerator, denominator))


class ModelTests(unittest.TestCase):
    def test_first_child(self):
        g = genesis(2, 3)
        a, b, c = [Validator.init(g, i) for i in range(3)]
        a, av = generate_vote(a, 0, 10, 30, 10)
        b, bv = generate_vote(b, 0, 11, 20, 11)
        c, cv = generate_vote(c, 0, 12, 10, 12)
        self.assertEqual(len(a.votes), 1)
        a = submit_vote(submit_vote(a, bv), cv)
        a, block, own = generate_proposal(a, 0, 1, 13, 15, 13)
        b = submit_proposal(submit_vote(b, av), block, own)
        c = submit_proposal(submit_vote(c, av), block, own)
        self.assertEqual((a.tip, b.tip, c.tip), (1, 1, 1))
        self.assertEqual((a.latest, b.latest, c.latest), (13, 11, 12))
        self.assertEqual(quorums(a, 1)[0].block.id, 0)

    def test_missing_dependencies_retry_and_replay(self):
        g = genesis()
        a, b, c = [Validator.init(g, i) for i in range(3)]
        a, _ = generate_vote(a, 0, 10, 10, 10)
        b, _ = generate_vote(b, 0, 11, 20, 11)
        c, _ = generate_vote(c, 0, 12, 30, 12)
        a, ab, av = generate_proposal(a, 0, 1, 13, 15, 13)
        b, bb, bv = generate_proposal(b, 0, 2, 14, 12, 14)
        a = submit_proposal(a, bb, bv)
        a, successor = generate_vote(a, 2, 15, 9, 15)
        with self.assertRaisesRegex(ModelError, 'missing Block 2'):
            submit_vote(c, successor)
        self.assertNotIn(successor, c.votes)
        c = submit_proposal(c, bb, bv)
        with self.assertRaisesRegex(ModelError, 'missing Vote 13'):
            submit_vote(c, successor)
        self.assertNotIn(successor, c.votes)
        c = submit_proposal(c, ab, av)
        before = (c.tip, c.latest, c.finalized)
        c = submit_vote(c, successor)
        self.assertEqual(c.vote(successor.id), successor)
        self.assertEqual(submit_vote(c, successor), c)
        # Standalone Vote receipt admits evidence without selecting its target
        # or advancing the receiver's own signing history.
        self.assertEqual((c.tip, c.latest, c.finalized), before)
        self.assertEqual(c.latest, 12)
        with self.assertRaisesRegex(ModelError, 'double vote for exact Block'):
            generate_vote(a, 2, 16, 9, 15)

    def test_failed_envelope_is_atomic(self):
        g = genesis()
        a, _ = generate_vote(Validator.init(g, 0), 0, 10, 10, 10)
        _, block, own = generate_proposal(a, 0, 1, 11, 10, 11)
        receiver = Validator.init(g, 1)
        with self.assertRaisesRegex(ModelError, 'detached self-vote'):
            submit_proposal(receiver, block, replace(own, target=0))
        self.assertEqual(receiver, Validator.init(g, 1))

    def test_threshold_and_parent_progress(self):
        g = genesis(2, 3)
        a, _ = generate_vote(Validator.init(g, 0), 0, 10, 10, 10)
        _, bv = generate_vote(Validator.init(g, 1), 0, 11, 20, 11)
        a = submit_vote(a, bv)
        with self.assertRaisesRegex(ModelError, 'insufficient endorsement stake'):
            generate_proposal(a, 0, 1, 12, 10, 12)
        g = genesis()
        a, _ = generate_vote(Validator.init(g, 0), 0, 10, 10, 10)
        a, _, _ = generate_proposal(a, 0, 1, 11, 10, 11)
        with self.assertRaisesRegex(ModelError, 'Block does not advance parent Q1 or unique Stake'):
            generate_proposal(a, 1, 2, 12, 10, 12)
        self.assertEqual((a.tip, a.latest), (1, 11))

    def test_single_validator_q1_q2_q3(self):
        g = Block.genesis(0, State(1, ((0, 1),), 2, 3))
        v, _ = generate_vote(Validator.init(g, 0), 0, 100, 10, 100)
        for height in range(1, 5):
            v, _, _ = generate_proposal(v, v.tip, height, 100 + height, 10, 100 + height)
            q1, q2 = quorums(v, v.tip)
            self.assertEqual(q1.block.height, height - 1)
            self.assertEqual(q2.block.height, max(0, height - 2))
            q3 = quorums(v, q2.block.id)[0]
            self.assertEqual(q3.block.height, max(0, height - 3))
            self.assertIn(v.finalized, [b.id for b in v.ancestry(v.tip)])

    def test_invalid_votes_and_duplicate_signers(self):
        g = genesis()
        a, vote = generate_vote(Validator.init(g, 0), 0, 10, 10, 10)
        receiver = Validator.init(g, 1)
        with self.assertRaisesRegex(ModelError, 'wrong stake'):
            submit_vote(receiver, replace(vote, stake=2))
        # Keep the original live-admission precedence even when the malformed
        # envelope also collides with an occupied exact Block.
        with self.assertRaisesRegex(ModelError, 'wrong stake'):
            submit_vote(a, replace(vote, id=12, stake=2, sig_hash=12))
        with self.assertRaisesRegex(ModelError, 'wrong Vote position'):
            submit_vote(a, replace(vote, id=13, height=2, sig_hash=13))
        with self.assertRaisesRegex(ModelError, 'double vote for exact Block'):
            submit_vote(a, replace(vote, id=11, sig_hash=20))
        with self.assertRaisesRegex(ModelError, 'Vote identity collision'):
            submit_vote(a, replace(vote, race=20))
        _, block, own = generate_proposal(a, 0, 1, 11, 10, 11)
        with self.assertRaisesRegex(ModelError, 'duplicate admission signer'):
            submit_proposal(receiver, replace(block, endorsements=(vote, vote)), own)
        self.assertEqual(receiver, Validator.init(g, 1))

    def test_historical_evidence_is_retained_after_finalization(self):
        g = genesis()
        a, _ = generate_vote(Validator.init(g, 0), 0, 10, 10, 10)
        b, _ = generate_vote(Validator.init(g, 1), 0, 20, 20, 20)
        # A separate conflicting signing branch supplies historical evidence.
        # This is an admission check, not an honest-network schedule.
        _, old, own = generate_proposal(a, 0, 1, 11, 10, 11)
        b = submit_vote(b, a.vote(10))
        b, better, better_own = generate_proposal(b, 0, 2, 21, 20, 21)
        a = submit_proposal(a, better, better_own)
        a, av = generate_vote(a, 2, 12, 10, 12)
        b = submit_vote(b, av)
        c = submit_proposal(Validator.init(g, 2), better, better_own)
        c = submit_vote(c, a.vote(10))
        c, cv = generate_vote(c, 2, 30, 30, 30)
        b = submit_vote(b, cv)
        b, child, child_own = generate_proposal(b, 2, 3, 22, 20, 22)
        a = submit_proposal(a, child, child_own)
        c = submit_proposal(c, child, child_own)
        a, av = generate_vote(a, 3, 13, 10, 13)
        c, cv = generate_vote(c, 3, 31, 30, 31)
        b = submit_vote(submit_vote(b, av), cv)
        b, child, child_own = generate_proposal(b, 3, 4, 23, 20, 23)

        a = submit_proposal(a, child, child_own)
        c = submit_proposal(c, child, child_own)
        a, av = generate_vote(a, 4, 14, 10, 14)
        c, cv = generate_vote(c, 4, 32, 30, 32)
        b = submit_vote(submit_vote(b, av), cv)
        b, _, _ = generate_proposal(b, 4, 5, 24, 20, 24)
        self.assertIn(2, [block.id for block in b.ancestry(b.finalized)])
        before = (b.tip, b.latest, b.finalized)
        b = submit_proposal(b, old, own)
        self.assertEqual((b.tip, b.latest, b.finalized), before)
        self.assertEqual(b.block(old.id), old)
        with self.assertRaisesRegex(ModelError, 'outside current finalized lineage'):
            generate_vote(b, old.id, 25, 20, 25)


class NetworkTests(unittest.TestCase):

    def test_default_endorsement_threshold_is_two_thirds(self):
        state = Network().genesis.state
        self.assertEqual((state.numerator, state.denominator), (2, 3))

    def test_publication_cannot_forge_honest_vote(self):
        sim = Network()
        _, forged = generate_vote(sim.receivers[0], 0, 123, 1, 1)
        before = sim.receivers.copy()
        self.assertEqual(sim.step(('publish_vote', forged)), 'honest Vote was not emitted')
        self.assertEqual(sim.receivers, before)
        self.assertFalse(sim.votes)

    def test_live_admission_ranks_siblings_and_accepts_one_vote_per_block(self):
        sim = Network()
        for who in sim.honest:
            sim.honest_vote(who)
        byzantine, _ = generate_vote(Validator.init(sim.genesis, 3), 0, 100, 4, 4)
        for vote in sim.votes.values():
            byzantine = submit_vote(byzantine, vote)
        _, left, lv = generate_proposal(byzantine, 0, 200, 101, 4, 4)
        _, right, rv = generate_proposal(byzantine, 0, 201, 102, 4, 4)
        # The two detached endorsements share PrevVoteHash but target different
        # exact Blocks, so both are valid signed actions.
        rv = replace(rv, inner_id=lv.inner_id)
        self.assertIsNone(sim.step(('publish_proposal', left, lv)))
        self.assertIsNone(sim.step(('publish_proposal', right, rv)))
        self.assertIsNone(sim.step(('deliver_proposal', 0, left.id, lv.id)))
        self.assertIsNone(sim.step(('deliver_proposal', 1, right.id, rv.id)))
        self.assertEqual(sim.receivers[0].tip, left.id)
        self.assertEqual(sim.receivers[1].tip, right.id)
        self.assertIsNone(sim.step(('deliver_proposal', 0, right.id, rv.id)))
        self.assertIsNone(sim.step(('deliver_proposal', 1, left.id, lv.id)))
        # Both Blocks and both exact-Block Votes remain live. Forked self-history
        # is still visible as Byzantine evidence, while ordinary ranking makes
        # every receiver select the same Block.
        for after, sibling_vote in (
                (sim.receivers[0], rv),
                (sim.receivers[1], lv)):
            self.assertIn(left, after.blocks)
            self.assertIn(right, after.blocks)
            self.assertEqual(after.tip, left.id)
            self.assertIn(sibling_vote, after.votes)
            self.assertNotIn(sibling_vote, after.evidence_votes)
            self.assertEqual({proof.offender for proof in view_evidence(after)}, {3})
        self.assertTrue(all(v.finalized == sim.genesis.id for v in sim.receivers.values()))
        self.assertTrue(sim.agreement)


if __name__ == '__main__':
    unittest.main()
