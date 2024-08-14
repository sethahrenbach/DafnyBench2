function abs(x: int): int
{
    if x < 0 then -x else x
}

method Testing_abs()
{
    var v := abs(3);
    assert v == 3;
}


// Exercise 4. Write a function max that returns the larger of two given integer parameters. Write a test method using an assert that checks that your function is correct.

function max(a: int, b: int): int
{
    if a > b then a else b
}

method Testing_max() {
    assert max(5, 3) == 5;
    assert max(3, 5) == 5;
    assert max(-1, -3) == -1;
    assert max(0, 0) == 0;
}


// Exercise 6:

method AbsMethod(x: int) returns (y: int)
    ensures abs(x) == y
{
    if x < 0 {
        y := -x;
    } else {
        y := x;
    }
}


// Ghost
ghost function Double(val:int) : int
{
    2 * val
}

method TestDouble(val: int) returns (val2:int)
    ensures val2 == Double(val)
{
    val2 := 2 * val;
}