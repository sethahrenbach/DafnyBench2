
// We'll define "Between" to capture how the ring wraps around.
ghost predicate Between(start: nat, i: nat, end: nat)
{
  if start < end then start <= i < end
  else i < end || start <= i
}

lemma BetweenTests()
{
  assert Between(5, 1, 3);
  assert Between(5, 0, 3);
  assert Between(5, 5, 3);
  assert Between(5, 6, 3);
  assert Between(5, 7, 3);
  assert !Between(5, 4, 3);
  assert !Between(5, 3, 3);
}

datatype Variables = Variables(ids: seq<nat>, highest_heard: seq<int>) {

  ghost predicate ValidIdx(i: int) {
    0 <= i < |ids|
  }

  ghost predicate UniqueIds() {
    forall i, j | ValidIdx(i) && ValidIdx(j) ::
      ids[i] == ids[j] ==> i == j
  }

  ghost predicate WF()
  {
    && 0 < |ids|
    && |ids| == |highest_heard|
  }

  ghost predicate IsChord(start: nat, end: nat)
  {
    && ValidIdx(start) && ValidIdx(end)
    && WF()
    && highest_heard[end] == ids[start]
  }
}

ghost predicate Init(v: Variables)
{
  && v.UniqueIds()
  && v.WF()
  && (forall i | v.ValidIdx(i) :: v.highest_heard[i] == -1)
}

ghost function max(a: int, b: int) : int {
  if a > b then a else b
}

ghost function NextIdx(v: Variables, idx: nat) : nat
  requires v.WF()
  requires v.ValidIdx(idx)
{
  if idx == |v.ids| - 1 then 0 else idx + 1
}

datatype Step = TransmissionStep(src: nat)

ghost predicate Transmission(v: Variables, v': Variables, step: Step)
  requires step.TransmissionStep?
{
  var src := step.src;
  && v.WF()
  && v.ValidIdx(src)
  && v'.ids == v.ids
  && var dst := NextIdx(v, src);
  && var message := max(v.highest_heard[src], v.ids[src]);
  && var dst_new_max := max(v.highest_heard[dst], message);
  && v'.highest_heard == v.highest_heard[dst := dst_new_max]
}

ghost predicate NextStep(v: Variables, v': Variables, step: Step)
{
  match step {
    case TransmissionStep(_) => Transmission(v, v', step)
  }
}

lemma NextStepDeterministicGivenStep(v: Variables, step: Step, v'1: Variables, v'2: Variables)
  requires NextStep(v, v'1, step)
  requires NextStep(v, v'2, step)
  ensures v'1 == v'2
{}

ghost predicate Next(v: Variables, v': Variables)
{
  exists step :: NextStep(v, v', step)
}

ghost predicate IsLeader(v: Variables, i: int)
  requires v.WF()
{
  && v.ValidIdx(i)
  && v.highest_heard[i] == v.ids[i]
}

ghost predicate Safety(v: Variables)
  requires v.WF()
{
  forall i, j | IsLeader(v, i) && IsLeader(v, j) :: i == j
}

ghost predicate ChordHeardDominated(v: Variables, start: nat, end: nat)
  requires v.IsChord(start, end)
  requires v.WF()
{
  forall i | v.ValidIdx(i) && Between(start, i, end) ::
    v.highest_heard[i] >= v.ids[start]
}

ghost predicate {:opaque} OnChordHeardDominatesId(v: Variables)
  requires v.WF()
{
  forall start: nat, end: nat | v.IsChord(start, end) ::
    ChordHeardDominated(v, start, end)
}

lemma UseChordDominated(v: Variables, start: nat, end: nat)
  requires v.WF()
  requires OnChordHeardDominatesId(v)
  requires v.IsChord(start, end)
  ensures ChordHeardDominated(v, start, end)
{
  reveal OnChordHeardDominatesId();
}

ghost predicate Inv(v: Variables)
{
  && v.WF()
  && v.UniqueIds()
  && OnChordHeardDominatesId(v)
}

lemma InitImpliesInv(v: Variables)
  requires Init(v)
  ensures Inv(v)
{
  reveal OnChordHeardDominatesId();
}

lemma NextPreservesInv(v: Variables, v': Variables)
  requires Inv(v)
  requires Next(v, v')
  ensures Inv(v')
{
  var step :| NextStep(v, v', step);
  var src := step.src;
  var dst := NextIdx(v, src);
  var message := max(v.highest_heard[src], v.ids[src]);
  var dst_new_max := max(v.highest_heard[dst], message);

  forall start: nat, end: nat | v'.IsChord(start, end)
    ensures ChordHeardDominated(v', start, end)
  {
    if dst == end {
      if dst_new_max == v.highest_heard[dst] {
        UseChordDominated(v, start, end);
      } else if v'.highest_heard[dst] == v.ids[src] {
        // New chord is formed
      } else if v'.highest_heard[end] == v.highest_heard[src] {
        // Extended a chord
        UseChordDominated(v, start, src);
      }
    } else {
      UseChordDominated(v, start, end);
    }
  }
  reveal OnChordHeardDominatesId();
}

lemma InvImpliesSafety(v: Variables)
  requires Inv(v)
  ensures Safety(v)
{
  forall i: nat, j: nat | IsLeader(v, i) && IsLeader(v, j)
    ensures i == j
  {
    if i != j {
      UseChordDominated(v, i, i);
    }
  }
}
