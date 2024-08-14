method CountToAndReturnN(n: int) returns (r: int)
    requires n >= 0
    ensures r == n 
{
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant r == i
    {
        i := i + 1;
    }
    assert i <= n;
    r := i;
}