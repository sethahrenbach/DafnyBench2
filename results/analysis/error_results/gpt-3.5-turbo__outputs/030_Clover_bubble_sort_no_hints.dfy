method BubbleSort(a: array<int>)
  modifies a
  ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..])==multiset(old(a[..]))
{
  var i := a.Length - 1;
  while (i > 0)
    invariant 0 <= i < a.Length
    invariant forall k::0 <= k < a.Length - i ==> a[k] <= a[k + 1]
  {
    var j := 0;
    while (j < i)
      invariant 0 <= j < a.Length
      invariant forall k::0 <= k < j ==> a[k] <= a[k + 1]
      invariant forall k::j <= k < a.Length - 1 ==> a[k] <= a[k + 1]
    {
      if (a[j] > a[j + 1])
      {
        a[j], a[j + 1] := a[j + 1], a[j];
        assert a[j] <= a[j + 1];
      }
      j := j + 1;
    }
    i := i - 1;
  }
}