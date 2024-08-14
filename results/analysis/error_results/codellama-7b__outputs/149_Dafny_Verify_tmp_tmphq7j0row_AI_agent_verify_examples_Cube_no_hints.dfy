
method Cube(n: nat) returns (c: nat)
    ensures c == n * n * n
    loop invariant 0 <= i <= n
    loop invariant c == n * n * n
    loop assigns c, i, k, m
{
    var i := 0;
    var k := 1;
    var m := 6;
    while i != n
    {
        c := c + k;
        k := k + m;
        m := m + 6;
        i := i + 1;
    }
}
