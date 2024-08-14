// Nim version 3: fix the bug and demonstrate a behavior.
//
// In this version, we've fixed the bug by actually flipping whose turn it is in
// each transition.

datatype Player = P1 | P2
{
  function Other(): Player {
    if this == P1 then P2 else P1
  }
}
datatype Variables = Variables(piles: seq<nat>, turn: Player)

ghost predicate Init(v: Variables) {
  && |v.piles| == 3
  && v.turn == P1
}

datatype Step =
  | TurnStep(take: nat, p: nat)
  | NoOpStep()

ghost predicate Turn(v: Variables, v': Variables, step: Step)
  requires step.TurnStep?
{
  var p := step.p;
  var take := step.take;
  && p < |v.piles|
  && take <= v.piles[p]
  && v' == v.(piles := v.piles[p := v.piles[p] - take]).(turn := v.turn.Other())
}

// nearly boilerplate (just gather up all transitions)
ghost predicate NextStep(v: Variables,  v': Variables, step: Step) {
  match step {
    case TurnStep(_, _) => Turn(v, v', step)
    case NoOpStep() => v' == v // we don't really need to define predicate NoOp
  }
}

// boilerplate
lemma NextStepDeterministicGivenStep(v: Variables, v': Variables, v'': Variables, step: Step)
  requires NextStep(v, v', step)
  requires NextStep(v, v'', step)
  ensures v' == v''
{
}

// boilerplate
ghost predicate Next(v: Variables,  v': Variables) {
  exists step :: NextStep(v, v', step)
}

lemma ExampleBehavior() returns (b: seq<Variables>)
  ensures |b| >= 3 // for this example, we just demonstrate there is some execution with three states
  ensures Init(b[0])
  ensures forall i:nat | i + 1 < |b| :: Next(b[i], b[i+1])
{
  // the syntax here constructs a Variables with named fields.
  var state0 := Variables(piles := [3, 5, 7], turn := P1);
  b := [
    state0,
    Variables(piles := [3, 3, 7], turn := P2),
    Variables(piles := [3, 3, 6], turn := P1)
  ];
  assert Init(state0);
  assert Next(b[0], b[1]) by {
    var step := TurnStep(2, 1);
    assert Turn(b[0], b[1], step);
  }
  assert Next(b[1], b[2]) by {
    var step := TurnStep(1, 2);
    assert Turn(b[1], b[2], step);
  }
}