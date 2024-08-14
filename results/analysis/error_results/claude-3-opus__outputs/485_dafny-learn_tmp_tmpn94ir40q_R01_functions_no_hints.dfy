function abs(x: int): int
{
    if x < 0 then -x else x
}

method Testing_abs()
{
    var v := abs(3);
    assert v == 3;
    var w := abs(-5);
    assert w == 5;
}


function max(a: int, b: int): int
{
    if a > b then a else b
}

method Testing_max() {
    assert max(5, 3) == 5;
    assert max(-2, -1) == -1;
    assert max(0, 0) == 0;
    assert max(-10, 10) == 10;
}


method Abs(x: int) returns (y: int)
    ensures y == abs(x)
{
    if x < 0 {
        y := -x;
    } else {
        y := x;
    }
    assert y == abs(x);
}


ghost function Double(val:int) : int
{
    2 * val
}

method TestDouble(val: int) returns (val2:int)
    ensures val2 == Double(val)
{
    val2 := 2 * val;
    assert val2 == Double(val);
}