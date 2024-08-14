
predicate sorted_seg(a: array<int>, i: int, j: int)
  reads a
{
  i <= j
  forall k in [i..j-1] :: a[k] <= a[k+1]
}

method bubbleSort(a: array<int>, c: int, f: int)
  modifies a
  requires 0 <= c <= f <= a.Length
  ensures sorted_seg(a, c, f)
  ensures multiset(a[c..f]) == old(multiset(a[c..f]))
  ensures a[..c] == old(a[..c]) && a[f..] == old(a[f..])
{
  var i := c;
  var b := true;

  while (i < f && b)
  {
    var j := f - 1;

    b := false;

    while (j > i)
    {
      if (a[j - 1] > a[j])
      {
        a[j], a[j - 1] := a[j - 1], a[j];
        b := true;
      }
      j := j - 1;
    }
    i := i + 1;
  }
}
