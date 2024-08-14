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

    // loop invariant
    while k > 0
        invariant x + y*f(k) == f(n)
        decreases k
    {
        var kIsEven := k%2 == 0;
        if kIsEven {
            x := x + y;
            // assert to prove loop invariant
            assert x + y*f(k/2) == f(n);
        } else {
            // assert to prove loop invariant
            assert x + 2*y*f(k/2) == f(n);
        }
        y := 2*y;
        k := k/2;
        // assert at the end of loop body to prove loop invariant
        assert x + y*f(k) == f(n);
    }
    // k == 0 at this point
    assert f(0) == 1; // by definition of f
    assert x + y == x + y*f(0); // since f(0) == 1
    assert x + y*f(0) == f(n); // by loop invariant
    a := x+y;
}