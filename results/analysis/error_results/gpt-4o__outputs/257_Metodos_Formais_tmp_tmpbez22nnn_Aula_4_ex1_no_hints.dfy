predicate Par(n:int)
{
    n % 2 == 0
}

method FazAlgo (a:int, b:int) returns (x:int, y:int)
requires a >= b && Par (a-b)
ensures x == y
{
    x := a;
    y := b;
    while x != y
        invariant a >= b
        invariant x >= y
        invariant Par(a - b)
        invariant Par(x - y)
        invariant x + y == a + b
        decreases x - y
    {
        assert x > y;
        x := x - 1;
        y := y + 1;
    }
    assert x == y;
}