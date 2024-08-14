
function Sum(n: nat): nat
{
  if n == 0 then 0 else n + Sum(n - 1)
}

method ComputeSum(n: nat) returns (s: nat)
  ensures s == Sum(n)
  loop invariant i <= n
  loop invariant s == Sum(i)
  loop variant n - i
{
  s := 0;
  var i := 0;
  while i < n
  {
    s := s + i + 1;
    i := i + 1;
  }
}
