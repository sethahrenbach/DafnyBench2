predicate Par(n:int)
{
    n % 2 == 0
}

method FazAlgo (a:int, b:int) returns (x:int, y:int)
requires a >= b && Par(a-b)
ensures x == y && x == a-b
{
    var z := a - b;
    var w := 0;
    if a > b {
        while x != y
        invariant x + y == a + b
        invariant Par(x) && Par(y)
        decreases x - y
        {
            x := x - 1;
            y := y + 1;
        }
    }
    x := a;
    y := b;
}
