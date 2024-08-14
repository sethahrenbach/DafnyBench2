ghost function f(n: nat): nat {
    if n == 0 then 1 
    else if n%2 == 0 then 1 + 2*f(n/2)
    else 2*f(n/2)
}

method mod(n:nat) returns (a:nat) 
requires n >= 0
ensures a == f(n)
{
    var x:nat := 0;
    var y:nat := 1;
    var k:nat := n;
    while k > 0
    invariant k >= 0
    invariant x + y == f(n)
    invariant y == 2*y
    invariant x == f(n - k)
    {
        if (k%2 == 0) {
            x := x + y;
        }
        y := 2*y;
        k := k/2;
    }
    a := x+y;
}