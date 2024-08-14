
ghost function pow(a: int, e: nat): int {
    if e == 0 then 1 else a * pow(a, e-1)
}

method Pow(a: nat, n: nat) returns (y: nat)
    requires n >= 0;
    ensures y == pow(a, n);
{
    var x: nat := 1;
    var k: nat := 0;
    while k < n
        invariant 0 <= k <= n;
        invariant x == pow(a, k);
    {
        x := a * x;
        k := k + 1;
    }
    assert k == n;
    assert x == pow(a, n);
    y := x;
}
