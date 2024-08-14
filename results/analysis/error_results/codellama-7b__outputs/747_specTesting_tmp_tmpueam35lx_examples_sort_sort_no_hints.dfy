  method foo(x: int) returns (y: int)
    ensures y == x
{
    y := x;
}

method bar(x: int) returns (y: int)
    ensures y == x
{
    y := x;
}

method main()
{
    var x := 5;
    var y := foo(x);
    var z := bar(y);
    assert z == y;
}
 