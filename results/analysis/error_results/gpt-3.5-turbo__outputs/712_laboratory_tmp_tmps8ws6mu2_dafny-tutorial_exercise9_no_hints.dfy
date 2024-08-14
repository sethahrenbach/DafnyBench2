
function fib(n: nat): nat
{
    if n == 0 then 0 else
    if n == 1 then 1 else
                    fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
    ensures b == fib(n)
{
    var i: int := 0;
    var b_old := 0;
    var c := 1;
    while i < n
        invariant 0 <= i <= n &&
                  b == fib(i) &&
                  c == fib(i + 1) &&
                  b_old == fib(i - 1)
    {
        assert c == fib(i + 1);
        assert b == fib(i);
        assert b_old == fib(i - 1);

        var temp := b;
        b := c;
        c := temp + c;
        i := i + 1;
    }
}
