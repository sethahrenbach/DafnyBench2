method Mult(x:nat, y:nat) returns (r: nat)
    requires true
    ensures r == x * y
{
    var m := x;
    var n := y;
    r := 0;

    while m > 0
        invariant m >= 0
        invariant r == x * y - m * n
    {
        r := r + n;
        m := m - 1;
    }

    return r;
}