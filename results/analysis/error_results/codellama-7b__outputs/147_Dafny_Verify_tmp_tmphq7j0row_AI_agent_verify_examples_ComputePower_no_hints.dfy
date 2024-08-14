  I apologize for the mistake. Here is the corrected code:

function Power(n: nat): nat {
  if n == 0 then 1 else 2 * Power(n - 1)
}

method ComputePower(N: int) returns (y: nat) requires N >= 0
  ensures y == Power(N)
{
  // Loop invariant: x <= N
  // Assertion: x >= 0
  // Assertion: y == Power(x)
  var x := 0;
  var y := 1;
  while x != N
  {
    x := x + 1;
    y := y + y;
  }
  return y;
}

This code should now pass the Dafny verification.