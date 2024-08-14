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
        invariant res * factorial(n-i) == C(i) * factorial(n-i)
    {
        ghost var v0 := n - i;
        i := i + 1;
        res := (4 * i - 2) * res / (i + 1);
    }
}

function factorial(n: nat): nat
{
    if n == 0 then 1 else n * factorial(n-1)
}