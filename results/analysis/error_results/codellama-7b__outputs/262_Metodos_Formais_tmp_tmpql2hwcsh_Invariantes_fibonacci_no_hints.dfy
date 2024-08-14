
function Fib(n:nat):nat
{
    if n < 2
    then n
    else Fib(n-2) + Fib(n-1)
}

method ComputeFib(n:nat) returns (x:nat)
ensures x == Fib(n)
{
    var i := 0;
    x := 0;
    var y := 1;
    while i < n
    {
        // Loop invariant: x = Fib(i)
        assert x == Fib(i);
        // Loop invariant: 0 <= i <= n
        assert 0 <= i <= n;
        // Loop invariant: y = Fib(i+1)
        assert y == Fib(i+1);
        x, y := y, x + y; //multiplas atribuições
        i := i + 1;
    }
}
