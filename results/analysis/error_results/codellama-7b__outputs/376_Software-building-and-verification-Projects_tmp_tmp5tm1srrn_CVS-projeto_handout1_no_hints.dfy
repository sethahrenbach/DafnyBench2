
method sum(a: array<int>) returns (s: int)
  requires a.Length > 0
  ensures s == sum(a, 0, a.Length)
{
  s := 0;
  for i := 0 to a.Length - 1 do
    s := s + a[i];
}

method sum(a: array<int>, i: int, j: int) returns (s: int)
  requires i <= j && j <= a.Length
  ensures s == sum(a, i, j)
{
  if i == j then
    s := 0;
  else
    s := a[j - 1] + sum(a, i, j - 1);
}
