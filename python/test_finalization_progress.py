"""Depth-independent finalization checks; conflicts fail, not expected success."""
import unittest
from consensus import Block, State, Validator, generate_vote, generate_proposal, quorums


class FinalizationTests(unittest.TestCase):
    def test_finalization_progress_and_lineage(self):
        g = Block.genesis(0, State(1, ((0, 1),), 2, 3))
        v, _ = generate_vote(Validator.init(g, 0), 0, 100, 10, 100)
        for height in range(1, 7):
            previous = v.finalized
            v, _, _ = generate_proposal(v, v.tip, height, 100 + height, 10, 100 + height)
            self.assertIn(previous, [b.id for b in v.ancestry(v.finalized)])
            self.assertIn(v.finalized, [b.id for b in v.ancestry(v.tip)])
            q2 = quorums(v, v.tip)[1]
            self.assertEqual(v.finalized, quorums(v, q2.block.id)[0].block.id)
        self.assertGreater(v.block(v.finalized).height, 0)


if __name__ == '__main__':
    unittest.main()
