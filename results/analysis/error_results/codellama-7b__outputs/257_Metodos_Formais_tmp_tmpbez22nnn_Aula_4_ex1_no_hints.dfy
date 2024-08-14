
predicate Par(n:int)
{
    n % 2 == 0
}

method FazAlgo (a:int, b:int) returns (x:int, y:int)
requires a >= b && Par (a-b)
ensures x == a && y == b
{
    x := a;
    y := b;
    while x != y
    {
        // loop invariant: x >= y
        assert x >= y;
        x := x - 1;
        y := y + 1;
        // loop invariant: x >= y && x - 1 >= y + 1
        assert x - 1 >= y + 1;
    }
}
