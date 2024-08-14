function fib(n: nat): nat
{
    if n == 0 then 0 else
    if n == 1 then 1 else
                    fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
   ensures b == fib(n)  // Do not change this postcondition
{
    var i: int := 0;
    b := 0;
    var c := 1;
    // Loop invariant
    // 1. 0 <= i <= n
    // 2. b == fib(i)
    // 3. c == fib(i + 1)
    while i < n
        invariant 0 <= i <= n
        invariant b == fib(i)
        invariant c == fib(i + 1)
    {
        var temp := b;
        b := c;
        c := c + temp;
        i := i + 1;
    }
    assert b == fib(n);
}