function abs(x: int): int
    ensures (x >= 0 ==> result == x) && (x < 0 ==> result == -x)
{
    if x < 0 then -x else x
}

method Testing_abs()
{
    var v := abs(3);
}


// Exercise 4. Write a function max that returns the larger of two given integer parameters. Write a test method using an assert that checks that your function is correct.

function max(a: int, b: int): int
    ensures result >= a && result >= b && (result == a || result == b)
{
    if a > b then a else b
}
method Testing_max() {
    assert max(3, 5) == 5;
    assert max(-2, 7) == 7;
}


// Exercise 6:

method Abs(x: int) returns (y: int)
    ensures y == abs(x)
{
    if x < 0 {
        return -x;
    } else {
        return x;
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