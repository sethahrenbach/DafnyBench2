
function Stairs(n: nat): nat
  reads n
{
  if n <= 1 then 1 else Stairs(n - 2) + Stairs(n - 1)
}

method ClimbStairs(n: nat) returns (r: nat)
  requires n >= 0
  ensures r == Stairs(n)
{
  var a := 1;
  var b := 1;
  var i := 1;
  while i < n
    invariant i >= 1
    invariant a == Stairs(i)
    invariant b == Stairs(i+1)
    invariant i <= n
    decreases n - i
  {
    a, b := b, a + b;
    i := i + 1;
  }
  return b;
}
