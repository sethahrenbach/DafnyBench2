
function abs(x: int): int
{
    if x < 0 then -x else x
}

method Testing_abs()
{
    var v := abs(3);
    assert v == 3;
}

function max(a: int, b: int): int
{
    if a > b then a else b
}

method Testing_max()
{
    var a := 5;
    var b := 3;
    var m := max(a, b);
    assert m == 5;
}

method Abs(x: int) returns (y: int)
    ensures abs(x) == y
{
    if x < 0 then
        return -x;
    else
        return x;
}

method TestDouble(val: int) returns (val2: int)
    ensures val2 == Double(val)
{
    val2 := 2 * val;
    assert val2 == 2 * val;
}
