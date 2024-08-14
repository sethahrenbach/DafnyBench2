
// Each node's identifier (address)
datatype Constants = Constants(ids: seq<nat>) {
  predicate ValidIdx(i: int) {
    0<=i<|ids|
  }

  ghost predicate UniqueIds() {
    (forall i, j | ValidIdx(i) && ValidIdx(j) && ids[i]==ids[j] :: i == j)
  }

  ghost predicate WF() {
    && 0 < |ids|
    && UniqueIds()
  }
}

// The highest other identifier this node has heard about.
datatype Variables = Variables(highest_heard: seq<int>) {
  ghost predicate WF(c: Constants)
  {
    && c.WF()
    && |highest_heard| == |c.ids|
  }
}

ghost predicate Init(c: Constants, v: Variables)
{
  && v.WF(c)
  && c.UniqueIds()
  && (forall i | c.ValidIdx(i) :: v.highest_heard[i] == -1)
}

function max(a: int, b: int) : int {
  if a > b then a else b
}

function NextIdx(c: Constants, idx: nat) : nat
  requires c.WF()
  requires c.ValidIdx(idx)
{
  if idx + 1 == |c.ids| then 0 else idx + 1
}

ghost predicate Transmission(c: Constants, v: Variables, v': Variables, srcidx: nat)
{
  && v.WF(c)
  && v'.WF(c)
  && c.ValidIdx(srcidx)
  && var dstidx := NextIdx(c, srcidx)
  && var message := max(v.highest_heard[srcidx], c.ids[srcidx])
  && var dst_new_max := max(v.highest_heard[dstidx], message)
  && v' == v.(highest_heard := v.highest_heard[dstidx := dst_new_max])
}

datatype Step = TransmissionStep(srcidx: nat)

ghost predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
{
  match step {
    case TransmissionStep(srcidx) => Transmission(c, v, v', srcidx)
  }
}

ghost predicate Next(c: Constants, v: Variables, v': Variables)
{
  exists step :: NextStep(c, v, v', step)
}

ghost predicate IsLeader(c: Constants, v: Variables, i: int)
  requires v.WF(c)
{
  && c.ValidIdx(i)
  && v.highest_heard[i] == c.ids[i]
}

ghost predicate Safety(c: Constants, v: Variables)
  requires v.WF(c)
{
  forall i, j | IsLeader(c, v, i) && IsLeader(c, v, j) :: i == j
}

ghost predicate Inv(c: Constants, v: Variables)
{
  && v.WF(c)
  && Safety(c, v)
}

lemma InitImpliesInv(c: Constants, v: Variables)
  requires Init(c, v)
  ensures Inv(c, v)
{
}

lemma NextPreservesInv(c: Constants, v: Variables, v': Variables)
  requires Inv(c, v)
  requires Next(c, v, v')
  ensures Inv(c, v')
{
  var step :| NextStep(c, v, v', step);
  var srcidx := step.srcidx;
  var dstidx := NextIdx(c, srcidx);
  var message := max(v.highest_heard[srcidx], c.ids[srcidx]);
  var dst_new_max := max(v.highest_heard[dstidx], message);

  assert v'.highest_heard[dstidx] == dst_new_max;
  assert forall i | i != dstidx :: v'.highest_heard[i] == v.highest_heard[i];
  
  forall i, j | IsLeader(c, v', i) && IsLeader(c, v', j) ensures i == j {
  }
}

lemma InvImpliesSafety(c: Constants, v: Variables)
  requires Inv(c, v)
  ensures Safety(c, v)
{
}
