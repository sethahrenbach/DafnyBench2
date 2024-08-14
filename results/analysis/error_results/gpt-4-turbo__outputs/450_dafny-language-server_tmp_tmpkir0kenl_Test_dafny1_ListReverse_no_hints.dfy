// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
    reverse := null;
    while (current != null)
      decreases r
      invariant current == null || current in r
      invariant reverse == null || reverse in r
      invariant (forall y :: y in r && y != current ==> y.nxt == null || y.nxt in r || y.nxt == reverse)
      invariant (forall y :: y in r && y.nxt == reverse ==> y.nxt in r || y == current)
    {
      var tmp := current.nxt;
      current.nxt := reverse;
      reverse := current;
      current = tmp;
    }
  }
}