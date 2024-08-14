method BubbleSort(a: array<int>)
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var i := a.Length - 1;
  while (i > 0)
    decreases i
    invariant 0 <= i < a.Length
    invariant forall k, l :: 0 <= k < l <= i ==> a[k] <= a[l]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j := 0;
    while (j < i)
      decreases i - j
      invariant 0 <= j <= i
      invariant forall k :: 0 <= k < j ==> a[k] <= a[k + 1]
      invariant forall k :: j < i ==> a[k] <= a[k + 1]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      if (a[j] > a[j + 1])
      {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    i := i - 1;
  }
}