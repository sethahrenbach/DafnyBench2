
function NChoose2(n: int): int
{
  n * (n - 1) / 2
}

function SumRange(lo: int, hi: int): int
{
  if lo >= hi then 0
  else SumRange(lo, hi - 1) + hi - 1
}

lemma SumRangeNChoose2(n: nat)
  ensures SumRange(0, n) == NChoose2(n)
{}

lemma SumRangeUnrollLeft(lo: int, hi: int)
  ensures SumRange(lo, hi) ==
          if lo >= hi then 0 else lo + SumRange(lo + 1, hi)
{}

method BubbleSort(a: array<int>) returns (n: nat) 
  modifies a
  ensures n <= NChoose2(a.Length)
{
  if a.Length == 0 { return 0; }  

  var i := a.Length - 1;
  n := 0;

  while i > 0
    invariant 0 <= i < a.Length
    invariant n <= NChoose2(a.Length)
  {
    var j := 0;
    while j < i
      invariant 0 <= j < i
      invariant forall k | j <= k < i :: a[k] <= a[k+1]
      invariant n == SumRange(0, a.Length - i)
    {
      if a[j] > a[j+1]
      {
        a[j], a[j+1] := a[j+1], a[j];
        n := n + 1;
      }
      j := j + 1;
    }

    SumRangeUnrollLeft(i, a.Length);
    i := i - 1;
  }

  calc {
    n;
    SumRange(1, a.Length);
    { SumRangeUnrollLeft(0, a.Length); }
    SumRange(0, a.Length);
    { SumRangeNChoose2(a.Length); }
    NChoose2(a.Length);
  }
}
