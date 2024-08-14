
method SqrSum(n: int) returns (s: int)
  ensures s == n * n
{
  s := 0;
  var i := 1;
  while (i <= n)
  {
    s := s + i * i;
    i := i + 1;
  }
  assert s == n * n;
}
