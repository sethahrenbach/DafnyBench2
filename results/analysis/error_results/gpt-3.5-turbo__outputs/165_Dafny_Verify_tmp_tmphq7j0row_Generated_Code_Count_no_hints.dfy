function has_count(v: int, a: array<int>, n: int): int
    reads a
    requires n >= 0 && n <= a.Length
{
    if n == 0 then 0 else
    (if a[n-1] == v then has_count(v, a, n-1) + 1 else has_count(v, a, n-1))
}

method count (v: int, a: array<int>, n: int) returns (r: int)
    requires n >= 0 && n <= a.Length;
    ensures has_count(v, a, n) == r;
{
    var i: int;

    i := 0;
    r := 0;

    while (i < n)
        invariant 0 <= i <= n
        invariant r == has_count(v, a, n) - has_count(v, a, i)
        invariant forall k :: i <= k < n ==> a[k] != v ==> has_count(v, a, k) == r
    {
        assert r == has_count(v, a, n) - has_count(v, a, i);
        assert i <= n;
        if (a[i] == v)
        {
            r := r + 1;
        }
        i := i + 1;
    }
    assert r == has_count(v, a, n) - has_count(v, a, i);
    assert i == n;
    return r;
}