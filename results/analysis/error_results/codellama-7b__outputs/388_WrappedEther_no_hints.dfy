  method foo(x: int, y: int) returns (z: int)
    requires x > 0 && y > 0
    ensures z == x + y
{
    z := x + y;
}