function Sum(n:nat):nat
    ensures Sum == (n*(n+1))/2
{
    if n == 0 then 0 else n + Sum(n-1)
}

method ComputeSum(n:nat) returns (s:nat)
    ensures s == Sum(n)
{
    s := 0;
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant s == Sum(i)
      decreases n - i
      {
        s := s + i + 1;
        i := i + 1;
      }
}