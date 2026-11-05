"""Go-derived dependency retention and local retry through public actions."""
import unittest
from unittest.mock import patch

from network import Network


class NetworkDeliveryTests(unittest.TestCase):
    def test_honest_proposal_reports_refusal_then_acceptance(self):
        sim = Network()
        self.assertEqual(sim.honest_proposal(0), 'insufficient endorsement stake')
        self.assertFalse(sim.proposals)
        for who in sim.honest:
            sim.honest_vote(who)
        for vote in tuple(sim.votes.values()):
            if vote.signer != 0:
                self.assertIsNone(sim.step(('deliver_vote', 0, vote.id)))
        self.assertIsNone(sim.honest_proposal(0))
        self.assertEqual(len(sim.proposals), 1)
        self.assertIsNone(sim.actions[-1][1])

    def test_honest_helpers_report_when_no_candidate_exists(self):
        sim = Network()
        with patch('network.best_endorseable', return_value=None):
            self.assertEqual(sim.honest_vote(0), 'no eligible Vote target')
        with patch.object(sim.owner(0), 'proposal_parent', return_value=None):
            self.assertEqual(sim.honest_proposal(0), 'no eligible proposal parent')
        self.assertEqual(sim.actions, [])

    def test_one_vote_delivery_is_rechecked_when_the_target_arrives(self):
        sim = Network()
        for who in sim.honest:
            sim.honest_vote(who)
        for vote in tuple(sim.votes.values()):
            if vote.signer != 0:
                self.assertIsNone(sim.step(('deliver_vote', 0, vote.id)))
        sim.honest_proposal(0)
        block, own = next(iter(sim.proposals.values()))

        self.assertIsNone(sim.step(('deliver_proposal', 2, block.id, own.id)))
        self.assertIsNone(sim.step(('sign_vote', 2, block.id, 30, 3, 3)))
        later = sim.votes[30]
        self.assertIsNone(sim.step(('deliver_vote', 1, later.id)))
        self.assertEqual(sim.last_delivery_status, 'buffered')
        self.assertIn(('vote', later.id), sim.owner(1).pending)

        self.assertIsNone(sim.step(('deliver_proposal', 1, block.id, own.id)))
        self.assertIn(later, sim.receivers[1].votes)
        self.assertNotIn(('vote', later.id), sim.owner(1).pending)
        self.assertEqual(
            [action for action, _ in sim.actions
             if action == ('deliver_vote', 1, later.id)],
            [('deliver_vote', 1, later.id)],
        )

if __name__ == '__main__':
    unittest.main()
