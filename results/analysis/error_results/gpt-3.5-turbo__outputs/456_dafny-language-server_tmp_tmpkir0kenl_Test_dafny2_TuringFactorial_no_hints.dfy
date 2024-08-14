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
    var v := u;
    var s := 1;
    while (s < r + 1)
      invariant 1 <= s <= r + 1;
      invariant u == Factorial(r);
      invariant v == Factorial(s - 1);
    {
      u := u + v;
      s := s + 1;
    }
    r := r + 1;
  }
  assert u == Factorial(n);
}