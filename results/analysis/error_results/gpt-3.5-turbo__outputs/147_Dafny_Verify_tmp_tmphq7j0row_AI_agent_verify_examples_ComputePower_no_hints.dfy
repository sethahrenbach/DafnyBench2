
function Power(n: nat): nat 
    ensures Power(n) == if n == 0 then 1 else 2 * Power(n - 1)
{
    if n == 0 then 1 else 2 * Power(n - 1)
}

method ComputePower(N: int) returns (y: nat) requires N >= 0
    ensures y == Power(N)
{
    y := 1;
    var x := 0; 
    while x != N
        invariant 0 <= x <= N && y == Power(x)
        decreases N - x
    {
        x, y := x + 1, y + y;
    } 
}
