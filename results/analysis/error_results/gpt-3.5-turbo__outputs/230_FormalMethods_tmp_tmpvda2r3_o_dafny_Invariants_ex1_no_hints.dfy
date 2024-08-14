method Mult(x:nat, y:nat) returns (r:nat)
    requires true
    ensures r == x * y
{
    var m := x;
    var n := y;
    r := 0;
    while m > 0
        invariant m * n + r == x * y
    {
        r := r + n;
        m := m - 1;
    }
    assert m == 0;
    assert r == x * y;
    return r;
}