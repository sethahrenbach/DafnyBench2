
class Node {
  var nxt: Node?

  method ReverseInPlace(x: Node?, r: set<Node>) returns (reverse: Node?)
    requires x == null || x in r;
    requires (forall y :: y in r ==> y.nxt == null || y.nxt in r);  // region closure
    modifies r;
    ensures reverse == null || reverse in r;
    ensures (forall y :: y in r ==> y.nxt == null || y.nxt in r);  // region closure
  {
    var current: Node? := x;
    var oldReverse := reverse;
    reverse := null;
    while (current != null)
      invariant current in r;
      invariant reverse in r;
      invariant (forall z :: z in r ==> z.nxt == null || z.nxt in r);  // region closure
    {
      var tmp := current.nxt;
      current.nxt := reverse;
      reverse := current;
      current := tmp;
      assert (reverse == null || reverse in r);
      assert (forall y :: y in r ==> y.nxt == null || y.nxt in r);  // region closure
    }
    assert (reverse == null || reverse in r);
    assert oldReverse == null || oldReverse in r;
  }
}
