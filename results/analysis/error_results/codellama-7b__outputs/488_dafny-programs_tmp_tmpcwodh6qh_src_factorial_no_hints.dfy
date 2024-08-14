
function fact(n: nat): nat
    ensures fact(n) >= 1
{
    if n == 0 then 1 else n * fact(n - 1)
}

method factorial(n: nat) returns (res: nat)
    ensures res == fact(n)
    loop invariant 0 <= i <= n
    loop invariant res == i * fact(n - i)
{
    var i := 1;
    res := 1;
    while i < n + 1
    {
        res := i * res;
        i := i + 1;
    }
}
