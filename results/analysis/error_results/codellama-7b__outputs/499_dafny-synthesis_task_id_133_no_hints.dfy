
function sumNegativesTo(a: array<int>, n: int): int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  reads a;
{
  if (n == 0) then 0 else if a[n-1] < 0 then sumNegativesTo(a, n-1) + a[n-1] else sumNegativesTo(a, n-1)
}

method SumOfNegatives(a: array<int>): int
    ensures result == sumNegativesTo(a, a.Length)
{
    result := 0;
    for i := 0 to a.Length
    {
        if a[i] < 0 {
            result := result + a[i];
        }
    }
}
