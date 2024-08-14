
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
  {
    var v := Factorial(r-1);
    var s := Factorial(r-2);
    while (s < r + 1)
    {
      u := u + v;
      s := s + 1;
    }
    r := r + 1;
  }

  // Loop invariants:
  // 1. u == Factorial(r)
  // 2. v == Factorial(r-1)
  // 3. s == Factorial(r-2)

  // Assert statements:
  assert u == Factorial(n);
  assert v == Factorial(r-1);
  assert s == Factorial(r-2);
}
