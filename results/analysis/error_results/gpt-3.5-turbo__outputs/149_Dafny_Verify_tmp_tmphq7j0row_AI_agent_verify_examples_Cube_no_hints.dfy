method Cube(n: nat) returns (c: nat) 
    requires n >= 0
    ensures c == n * n * n
{
    c := 0;
    var i := 0;
    var k := 1;
    var m := 6;
    while i < n
        invariant 0 <= i <= n
        invariant c == i * k * m + k * k * k * (n - i)
    {
        assert c == i * k * m + k * k * k * (n - i);
        c, k, m := c + k, k + m, m + 6; 
        i := i + 1;
    }
}