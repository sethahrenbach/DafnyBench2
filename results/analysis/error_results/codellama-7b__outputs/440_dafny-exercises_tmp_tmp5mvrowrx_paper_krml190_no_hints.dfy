
method Reverse() returns (reverse: Node)
    requires Valid()
    modifies footprint
    ensures reverse.Valid()
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
          current.Valid()
          current in old(footprint) && current.footprint <= old(footprint)
          current.footprint !! reverse.footprint
          |old(list)| == |reverse.list| + |current.list|
          forall i | 0 <= i < |current.list| ::
              current.list[i] == old(list)[|reverse.list| + i]
          old(list)[i] == reverse.list[|reverse.list| - 1 - i]
    {
        var nx: Node?;
        nx := current.next;
        forall i | 0 <= i < |nx.list| ::
            current.list[i + 1] == nx.list[i];
        // The state looks like: ..., reverse, current, nx, ...
        current.next := reverse;
        current.footprint := {current} + reverse.footprint;
        current.list := [current.data] + reverse.list;

        reverse := current;
        current := nx;
    }
}
