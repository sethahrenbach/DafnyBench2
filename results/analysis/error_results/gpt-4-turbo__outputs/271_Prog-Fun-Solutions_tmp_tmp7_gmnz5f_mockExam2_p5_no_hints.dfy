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
    while k >= 0
      invariant a == power(3, (n - k) / 5)
      invariant b == f(k) - sum_of_series(a, k, (n - k) / 5)
      decreases k
    {
        b := a*k + b;
        a := 3*a;
        k := k - 5;
    }
    
    x := b;
}

function power(base: int, exp: nat): int
{
    if exp == 0 then 1 else base * power(base, exp - 1)
}

function sum_of_series(a: int, k: int, terms: nat): int
  requires terms >= 0
  decreases terms
{
    if terms == 0 then 0
    else a*k + sum_of_series(3*a, k-5, terms-1)
}