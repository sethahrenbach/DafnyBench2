function Stairs(n: nat): nat {
  if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}

// A simple specification
method ClimbStairs(n: nat) returns (r: nat)
  ensures r == Stairs(n)
{
  var a, b := 1, 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant i == 0 ==> (a == 1 && b == 1)
    invariant i > 0 ==> (a == Stairs(i - 1) && b == Stairs(i))
  {
    a, b := b, a + b;
    i := i + 1;
  }
  return a;
}