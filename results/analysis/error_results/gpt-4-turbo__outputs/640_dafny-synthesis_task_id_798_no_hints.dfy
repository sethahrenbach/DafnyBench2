function sumTo(a: array<int>, n: int): int
  requires a != null
  requires 0 <= n && n <= a.Length
  reads a
{
  if (n == 0) then 0 else sumTo(a, n-1) + a[n-1]
}

method ArraySum(a: array<int>) returns (result: int)
    ensures result == sumTo(a, a.Length)
{
    result := 0;
    var i := 0;
    for i := 0 to a.Length - 1
        invariant 0 <= i && i <= a.Length
        invariant result == sumTo(a, i)
    {
        result := result + a[i];
    }
}