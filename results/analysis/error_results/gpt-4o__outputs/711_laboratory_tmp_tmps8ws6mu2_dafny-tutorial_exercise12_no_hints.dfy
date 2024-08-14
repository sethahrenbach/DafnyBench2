method FindMax(a: array<int>) returns (i: int)
    requires 0 < a.Length
    ensures 0 <= i < a.Length
    ensures forall k: int :: 0 <= k < a.Length ==> a[k] <= a[i]
{
    var j := 0;
    var max := a[0];
    var idx := 1;
    while idx < a.Length
        invariant 1 <= idx <= a.Length
        invariant 0 <= j < idx
        invariant max == a[j]
        invariant forall k: int :: 0 <= k < idx ==> a[k] <= max
    {
        if max < a[idx] {
            max := a[idx];
            j := idx;
        }
        idx := idx + 1;
    }

    i := j;
    assert 0 <= i < a.Length;
    assert forall k: int :: 0 <= k < a.Length ==> a[k] <= a[i];
}