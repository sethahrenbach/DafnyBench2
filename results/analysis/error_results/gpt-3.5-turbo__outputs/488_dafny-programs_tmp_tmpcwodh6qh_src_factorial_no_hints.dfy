function fact(n: nat): nat 
    ensures fact(n) >= 1
{
    if n == 0 then 1 else n * fact(n - 1)
}

method factorial(n: nat) returns (res: nat)
    ensures res == fact(n)
{
    var i := 1;
    res := 1;
    while i < n + 1 
    invariant 1 <= res <= fact(i) && i <= n + 1
    decreases n - i
    {
        assert i <= n + 1;
        assert 1 <= res <= fact(i);
        res := i * res;
        i := i + 1;
    }
    assert i == n + 1;
    assert res == fact(n);
    return res;
}