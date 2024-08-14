method Carre(a: nat) returns (c: nat)
    requires a >= 0
    ensures c == a*a
{
    var i := 0;
    c := 0;
    while i != a
    invariant 0 <= i <= a
    invariant c == i*i
    {
        assert c == i*i;
        assert i < a;
        c := c + 2*i + 1;
        i := i + 1;
    }
}