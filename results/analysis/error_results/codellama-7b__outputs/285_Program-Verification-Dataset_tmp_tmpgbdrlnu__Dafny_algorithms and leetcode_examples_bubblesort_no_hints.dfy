
method BubbleSort(a: array<int>) returns (n: nat)
  modifies a
  ensures n <= NChoose2(a.Length)
{
  // it simplifies the remaining invariants to handle the empty array here
  if a.Length == 0 { return 0; }

  var i := a.Length - 1;
  n := 0;

  while i > 0
  {
    var j := 0;
    while j < i
    {
      if a[j] > a[j+1]
      {
        a[j], a[j+1] := a[j+1], a[j];
        n := n + 1;
      }
      j := j + 1;
    }

    SumRangeUnrollLeft(i, a.Length);  // see lemma below
  }

  calc <= {
    n;  // less or equal to next line by the loop invariant
    SumRange(1, a.Length);
    { SumRangeUnrollLeft(0, a.Length); }
    SumRange(0, a.Length);
    { SumRangeNChoose2(a.Length); }  // see lemma below
    NChoose2(a.Length);
  }
}
