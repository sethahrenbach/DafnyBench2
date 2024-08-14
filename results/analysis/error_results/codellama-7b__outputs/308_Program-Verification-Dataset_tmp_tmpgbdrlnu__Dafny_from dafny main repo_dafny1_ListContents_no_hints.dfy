
method ReverseInPlace() returns (reverse: Node<T>)
    requires Valid()
    modifies Repr
    ensures reverse.Valid() && reverse.Repr <= old(Repr)
    ensures |reverse.List| == |old(List)|
    ensures forall i :: 0 <= i < |reverse.List| ==> reverse.List[i] == old(List)[|old(List)|-1-i]
{
    var current := next;
    reverse := this;
    reverse.next := null;
    reverse.Repr := {reverse};
    reverse.List := [data];

    while current != null
        current.Valid() &&
        current in old(Repr) && current.Repr <= old(Repr) &&
        current.Repr !! reverse.Repr
        |old(List)| == |reverse.List| + |current.List| &&
        current.List == old(List)[|reverse.List|..]
    {
      var nx := current.next;

      // ..., reverse, current, nx, ...
      current.next := reverse;
      current.Repr := {current} + reverse.Repr;
      current.List := [current.data] + reverse.List;

      reverse := current;
      current := nx;
    }
}
