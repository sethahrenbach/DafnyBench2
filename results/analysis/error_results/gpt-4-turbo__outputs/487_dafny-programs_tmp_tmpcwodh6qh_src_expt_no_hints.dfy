function Expt(b: int, n: nat): int
  requires n >= 0
{
  if n == 0 then 1 else b * Expt(b, n - 1)
}

method expt(b: int, n: nat) returns (res: int) 
  ensures res == Expt(b, n)
{
  var i := 1;
  res := 1;
  while i <= n 
    invariant 1 <= i <= n + 1
    invariant res == Expt(b, i - 1)
  {
    res := res * b;
    i := i + 1;
  }
}

lemma {:induction a} distributive(x: int, a: nat, b: nat) 
  ensures Expt(x, a) * Expt(x, b) == Expt(x, a + b)
{
  if a == 0 {
    assert Expt(x, 0) * Expt(x, b) == 1 * Expt(x, b);
    assert Expt(x, 0 + b) == Expt(x, b);
  } else {
    distributive(x, a - 1, b);
    assert Expt(x, a - 1) * Expt(x, b) == Expt(x, a - 1 + b);
    assert Expt(x, a) * Expt(x, b) == x * Expt(x, a - 1) * Expt(x, b);
    assert Expt(x, a + b) == x * Expt(x, a - 1 + b);
  }
}