
function C(n: nat): nat
{
  if n == 0 then 1 else (4 * n - 2) * C(n-1) / (n + 1)
}

method calcC(n: nat) returns (res: nat)
  ensures res == C(n)
{
  var i := 0;
  res := 1;

  while i < n
  {
    // Loop invariant: res is the result of the recursive call C(n-i)
    // with the current value of i
    assert res == C(n-i);

    // Loop invariant: v0 is the value of n - i
    ghost var v0 := n - i;

    // Loop invariant: i is the current index
    i := i + 1;

    // Loop invariant: res is the result of the recursive call C(n-i)
    // with the current value of i
    res := (4 * i - 2) * res / (i + 1);
  }
}
