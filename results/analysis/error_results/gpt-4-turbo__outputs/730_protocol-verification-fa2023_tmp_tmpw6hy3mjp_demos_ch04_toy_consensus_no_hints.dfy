// Ported from ivy/examples/ivy/toy_consensus.ivy.

// Ivy only supports first-order logic, which is limited (perhaps in surprising
// ways). In this model of consensus, we use some tricks to model quorums in
// first-order logic without getting into the arithmetic of why sets of n/2+1
// nodes intersect.

type Node(==)
type Quorum(==)
type Choice(==)

ghost predicate Member(n: Node, q: Quorum)

// axiom: any two quorums intersect in at least one node
lemma {:axiom} QuorumIntersect(q1: Quorum, q2: Quorum) returns (n: Node)
  ensures Member(n, q1) && Member(n, q2)

datatype Variables = Variables(
  votes: map<Node, set<Choice>>,
  decision: set<Choice>
)
{
  ghost predicate WF()
  {
    forall n: Node :: n in votes
  }
}

datatype Step =
  | CastVoteStep(n: Node, c: Choice)
  | DecideStep(c: Choice, q: Quorum)

ghost predicate CastVote(v: Variables, v': Variables, step: Step)
  requires v.WF()
  requires step.CastVoteStep?
{
  var n := step.n;
  v.votes[n] == {} &&
  v' == v.(votes := v.votes[n := v.votes[n] + {step.c}])
}

ghost predicate Decide(v: Variables, v': Variables, step: Step)
  requires v.WF()
  requires step.DecideStep?
{
  (forall n: Node | Member(n, step.q) :: step.c in v.votes[n]) &&
  v' == v.(decision := v.decision + {step.c})
}

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  v.WF() &&
  match step {
       case CastVoteStep(_, _) => CastVote(v, v', step)
       case DecideStep(_, _) => Decide(v, v', step)
     }
}

lemma NextStepDeterministicGivenStep(v: Variables, step: Step, v'1: Variables, v'2: Variables)
  requires NextStep(v, v'1, step)
  requires NextStep(v, v'2, step)
  ensures v'1 == v'2
{
}

ghost predicate Next(v: Variables, v': Variables)
{
  exists step :: NextStep(v, v', step)
}

ghost predicate Init(v: Variables) {
  v.WF() &&
  (forall n: Node :: v.votes[n] == {}) &&
  v.decision == {}
}

ghost predicate Safety(v: Variables) {
  forall c1, c2: Choice :: c1 in v.decision && c2 in v.decision ==> c1 == c2
}

ghost predicate ChoiceQuorum(v: Variables, q: Quorum, c: Choice)
  requires v.WF()
{
  forall n: Node | Member(n, q) :: c in v.votes[n]
}

ghost predicate Inv(v: Variables) {
  v.WF() &&
  Safety(v) &&
  (forall n: Node, v1, v2: Choice | v1 in v.votes[n] && v2 in v.votes[n] :: v1 == v2) &&
  (forall c: Choice | c in v.decision :: exists q: Quorum :: ChoiceQuorum(v, q, c))
}

lemma InitImpliesInv(v: Variables)
  requires Init(v)
  ensures Inv(v)
{
}

lemma InvInductive(v: Variables, v': Variables)
  requires Inv(v)
  requires Next(v, v')
  ensures Inv(v')
{
  var step :| NextStep(v, v', step);
  match step {
    case CastVoteStep(n, c) => {
      assert forall c: Choice | c in v'.decision :: exists q: Quorum :: ChoiceQuorum(v', q, c);
    }
    case DecideStep(c, q) => {
      assert forall c: Choice | c in v'.decision :: exists q: Quorum :: ChoiceQuorum(v', q, c);
      assert forall c1, c2: Choice | c1 in v'.decision && c2 in v'.decision :: c1 == c2;
    }
  }
}

lemma SafetyHolds(v: Variables, v': Variables)
  ensures Init(v) ==> Inv(v)
  ensures Inv(v) && Next(v, v') ==> Inv(v')
  ensures Inv(v) ==> Safety(v)
{
  if Inv(v) && Next(v, v') {
    InvInductive(v, v');
  }
}