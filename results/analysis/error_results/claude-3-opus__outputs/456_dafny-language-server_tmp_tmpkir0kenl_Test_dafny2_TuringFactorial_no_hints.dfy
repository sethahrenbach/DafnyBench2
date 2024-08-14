// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

function Factorial(n: nat): nat
{
  if n == 0 then 1 else n * Factorial(n-1)
}

method ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n;
  ensures u == Factorial(n);
{
  var r := 1;
  u := 1;
  while (r < n)
    invariant 1 <= r <= n;
    invariant u == Factorial(r);
  {
    ghost var f := Factorial(r);
    var v := u;
    var s := 1;
    while (s <= r)
      invariant 1 <= s <= r + 1;
      invariant u == f + v * (Factorial(s - 1));
    {
      u := u + v;
      s := s + 1;
    }
    assert u == f + v * Factorial(r);
    assert v == f;
    assert u == f + f * r;
    assert u == f * (1 + r);
    assert 1 + r == r + 1;
    assert u == f * (r + 1);
    assert u == Factorial(r) * (r + 1);
    assert u == Factorial(r + 1);
    r := r + 1;
  }
}