method barrier(v:array<int>, p:int) returns (b:bool)
    requires v.Length > 0
    requires 0 <= p < v.Length
    ensures b == forall k, l :: 0 <= k <= p && p < l < v.Length ==> v[k] < v[l]
{
    var i := 1;
    var max := 0;

    while i <= p
        invariant 1 <= i <= p + 1
        invariant 0 <= max < v.Length
        invariant forall k :: 1 <= k < i ==> v[k - 1] <= v[max]
    {
        if v[i] > v[max] {
            max := i;
        }

        i := i + 1;
    }

    while i < v.Length && v[i] > v[max]
        invariant p < i <= v.Length
        invariant forall k :: 1 <= k < i ==> v[k - 1] <= v[max]
    {
        i := i + 1;
    }
    b := i == v.Length;
}