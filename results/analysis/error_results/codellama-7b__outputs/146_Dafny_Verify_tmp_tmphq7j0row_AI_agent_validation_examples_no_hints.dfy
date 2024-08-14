
method Max(a: array<int>) returns (m: int)
    requires a.Length > 0
    ensures m == a[0]
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
{
    m := a[0];
    var n := 1;
    while n < a.Length
        decreases a.Length - n
        invariant m == a[0]
        invariant forall i :: 0 <= i < n ==> a[i] <= m
    {
        if a[n] > m then
            m := a[n];
        n := n + 1;
    }
}
