
function sumTo(a: array<int>, n: int): int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  reads a;
  loop invariant 0 <= n && n <= a.Length;
  loop invariant n == 0 || sumTo(a, n - 1) + a[n - 1] == sumTo(a, n);
{
  if (n == 0) then 0 else sumTo(a, n - 1) + a[n - 1]
}

method sum_array(a: array<int>): int
  requires a != null;
  ensures sum == sumTo(a, a.Length);
  loop invariant 0 <= i && i <= a.Length;
  loop invariant sum == sumTo(a, i);
{
  var i := 0;
  sum := 0;
  while (i < a.Length)
  {
    sum := sum + a[i];
    i := i + 1;
  }
}
