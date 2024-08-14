method climbStairs(n: nat) returns (res: nat)
  ensures res == (if n == 0 then 1 else if n == 1 then 1 else if n == 2 then 2 else climbStairs(n-1) + climbStairs(n-2))
{
  if n == 0 {
    return 1;
  } else if n == 1 {
    return 1;
  } else if n == 2 {
    return 2;
  }

  var steps := new nat[n+1];
  steps[0] := 1;
  steps[1] := 1;
  steps[2] := 2;

  for i := 3 to n {
    steps[i] := steps[i-1] + steps[i-2];
  }

  return steps[n];
}