// problem 5:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXX

ghost function f(n: int): int {
  if n < 0 then 0 else 3*f(n-5) + n
}

method problem5(n:nat) returns (x: int)
ensures x == f(n)
{
    var a := 1;
    var b := 0;
    var k := n;

    // Loop invariant
    invariant k >= -5
    invariant b == f(n - (n - k))
    invariant a == 3^((n - k) / 5)
    while k >= 0
    {
        // Loop body
        b := a*k + b;
        a := 3*a;
        k := k - 5;
    }
    
    x := b;
}