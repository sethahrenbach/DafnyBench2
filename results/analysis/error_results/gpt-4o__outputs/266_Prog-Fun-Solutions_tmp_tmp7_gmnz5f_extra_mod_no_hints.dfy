ghost function f(n: nat): nat {
    if n == 0 then 1 
    else if n%2 == 0 then 1 + 2*f(n/2)
    else 2*f(n/2)
}

method mod(n:nat) returns (a:nat) 
ensures a == f(n)
{
    var x:nat := 0;
    var y:nat := 1;
    var k:nat := n;
    while k > 0
        invariant k >= 0
        invariant x + y * f(k) == f(n)
    {
        if (k%2 == 0) {
            x := x + y;
            assert x + y + y * 2 * f(k/2) == f(n);
            assert x + y * (1 + 2 * f(k/2)) == f(n);
        } else {
            x := x;
            assert x + y * 2 * f(k/2) == f(n);
        }
        y := 2*y;
        k := k/2;
    }
    a := x+y;
    assert a == f(n);
}