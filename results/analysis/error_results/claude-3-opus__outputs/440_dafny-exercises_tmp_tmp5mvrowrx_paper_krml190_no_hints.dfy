// Examples used in paper:
//   Specification and Verification of Object-Oriented Software
// by K. Rustan M. Leino
// link of the paper:
//   http://leino.science/papers/krml190.pdf

// Figure 0. An example linked-list program written in Dafny.
class Data { }

class Node {
  var list: seq<Data>;
  var footprint: set<Node>;

  var data: Data;
  var next: Node?;

  function Valid(): bool
    reads this, footprint
  {
    this in footprint &&
    (next == null ==> list  == [data]) &&
    (next != null ==> next in footprint &&
                      next.footprint <= footprint &&
                      !(this in next.footprint) &&
                      list == [data] + next.list &&
                      next.Valid())
  }

  constructor(d: Data)
    ensures Valid() && fresh(footprint - {this})
    ensures list == [d]
  {
    data := d;
    next := null;
    list := [d];
    footprint := {this};
  }

  method SkipHead() returns (r: Node?)
    requires Valid()
    ensures r == null ==> |list| == 1
    ensures r != null ==> r.Valid() && r.footprint <= footprint
  {
    return next;
  }

  method Prepend(d: Data) returns (r: Node)
    requires Valid()
    ensures r.Valid() && fresh(r.footprint - old(footprint))
    ensures r.list == [d] + list
  {
    r := new Node(d);
    r.data := d;
    r.next := this;
    r.footprint := {r} + footprint;
    r.list := [r.data] + list;
  }

  // Figure 1: The Node.ReverseInPlace method,
  //     which performs an in situ list reversal.
  method ReverseInPlace() returns (reverse: Node)
    requires Valid()
    modifies footprint
    ensures reverse.Valid()
    // isn't here a typo?
    ensures fresh(reverse.footprint - old(footprint))
    ensures |reverse.list| == |old(list)|
    ensures forall i | 0 <= i < |old(list)| :: old(list)[i] == reverse.list[|old(list)| - 1 - i]
  {
    var current: Node?;
    current := next;
    reverse := this;
    reverse.next := null;
    reverse.footprint := {reverse};
    reverse.list := [data];

    while current != null
      invariant current != null ==> current.Valid()
      invariant current != null ==> current in old(footprint) && current.footprint <= old(footprint)
      invariant current != null ==> current.footprint !! reverse.footprint
      invariant reverse.Valid()
      invariant |old(list)| == |reverse.list| + (if current == null then 0 else |current.list|)
      invariant forall i | 0 <= i < |reverse.list| :: old(list)[i] == reverse.list[|reverse.list| - 1 - i]
      invariant current != null ==> forall i | 0 <= i < |current.list| :: current.list[i] == old(list)[|reverse.list| + i]
      modifies footprint
    {
      var nx := current.next;
      if nx != null {
        assert nx.Valid();
        assert nx in old(footprint);
        assert nx.footprint <= old(footprint);
        assert nx.footprint !! reverse.footprint;
        assert nx.footprint !! current.footprint;
        assert forall i | 0 <= i < |nx.list| :: current.list[i + 1] == nx.list[i];
      }
      
      ghost var oldReverse := reverse;
      ghost var oldCurrent := current;
      
      // The state looks like: ..., reverse, current, nx, ...
      current.next := reverse;
      current.footprint := {current} + reverse.footprint;
      current.list := [current.data] + reverse.list;

      reverse := current;
      current := nx;
      
      assert oldReverse.Valid();
      assert oldCurrent.Valid();
      assert |old(list)| == |oldReverse.list| + |oldCurrent.list|;
      assert forall i | 0 <= i < |oldReverse.list| :: old(list)[i] == oldReverse.list[|oldReverse.list| - 1 - i];
      assert forall i | 0 <= i < |oldCurrent.list| :: oldCurrent.list[i] == old(list)[|oldReverse.list| + i];
      if nx != null {
        assert |old(list)| == |reverse.list| + |nx.list|;
        assert forall i | 0 <= i < |nx.list| :: nx.list[i] == old(list)[|reverse.list| + i];
      }
    }
  }
}
