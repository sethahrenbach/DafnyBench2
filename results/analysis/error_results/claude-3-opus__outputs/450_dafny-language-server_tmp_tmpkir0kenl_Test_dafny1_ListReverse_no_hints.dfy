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

    ghost var oldR := r;  // snapshot of the original region
    ghost var oldList := ListFromNode(x);  // snapshot of the original list

    while (current != null)
      invariant current == null || current in r;
      invariant reverse == null || reverse in r;
      invariant (forall y :: y in r ==> y.nxt == null || y.nxt in r);
      invariant ListFromNode(reverse) + ListFromNode(current) == oldList;
      invariant (forall n :: n in oldR ==> n in r);  // region is not expanded
      decreases |ListFromNode(current)|;
    {
      var tmp := current.nxt;
      current.nxt := reverse;
      reverse := current;
      current := tmp;
    }
  }

  // Ghost function to get the list representation of a linked list
  ghost function ListFromNode(n: Node?): seq<Node>
    reads *;
    decreases |ListFromNode_Decreases(n)|;
  {
    if n == null then [] else [n] + ListFromNode(n.nxt)
  }

  // Helper ghost function for ListFromNode's decreases clause
  ghost function ListFromNode_Decreases(n: Node?): seq<Node>
    reads *;
  {
    if n == null then [] else [n] + ListFromNode_Decreases(n.nxt)
  }

  // Ghost function to reverse a sequence
  ghost function Reverse<T>(s: seq<T>): seq<T>
    ensures |Reverse(s)| == |s|;
    decreases |s|;
  {
    if s == [] then
      []
    else
      Reverse(s[1..]) + [s[0]]
  }
}