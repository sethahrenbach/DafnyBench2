function sumNegativesTo( a:array<int>, n:int ) : int
  requires a != null;
  requires 0 <= n && n <= a.Length;
  reads a;
{
  if (n == 0) then 0 else if a[n-1] < 0 then sumNegativesTo(a, n-1) + a[n-1] else sumNegativesTo(a, n-1)
}

method SumOfNegatives(a: array<int>) returns (result: int)
    ensures result == sumNegativesTo(a, a.Length)
{
    result := 0;
    var i := 0;
    while i < a.Length
      invariant 0 <= i <= a.Length;
      invariant result == sumNegativesTo(a, a.Length) - sumNegativesTo(a, i);
    {
        if i < a.Length && a[i] < 0 {
            result := result + a[i];
        }
        i := i + 1;
    }
}