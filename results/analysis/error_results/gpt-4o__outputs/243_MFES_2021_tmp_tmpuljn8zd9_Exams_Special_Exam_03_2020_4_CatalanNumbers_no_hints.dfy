function C(n: nat): nat 
{
    if n == 0 then 1 else (4 * n - 2) * C(n-1) / (n + 1) 
}

method calcC(n: nat) returns (res: nat)
    ensures res == C(n)
{
    var i := 0;
    res := 1;

    while i < n 
        invariant 0 <= i <= n
        invariant res == C(i)
    {
        ghost var v0 := n - i;
        res := (4 * (i + 1) - 2) * res / (i + 1 + 1);
        i := i + 1;
    }
    assert res == C(i);
    assert i == n;
}