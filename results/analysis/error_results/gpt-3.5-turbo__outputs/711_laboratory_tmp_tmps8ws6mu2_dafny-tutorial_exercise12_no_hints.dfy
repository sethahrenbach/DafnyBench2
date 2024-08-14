method FindMax(a: array<int>) returns (i: int)
    // Annotate this method with pre- and postconditions
    // that ensure it behaves as described.
    requires 0 < a.Length;
    ensures 0 <= i < a.Length;
    ensures forall k: int :: 0 <= k < a.Length ==> a[k] <= a[i]
{
    var j := 0;
    var max := a[0];
    i := 1;
    while i < a.Length
        invariant 0 <= j < a.Length;
        invariant 0 <= i <= a.Length;
        invariant forall k: int :: 0 <= k < i ==> a[k] <= max;
    {
        if max < a[i] {
            max := a[i];
            j := i;
        }
        i := i + 1;
    }

    i := j;
}