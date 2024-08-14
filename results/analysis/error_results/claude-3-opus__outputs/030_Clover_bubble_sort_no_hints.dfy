method BubbleSort(a: array<int>)
  modifies a
  ensures forall i,j::0<= i < j < a.Length ==> a[i] <= a[j]
  ensures multiset(a[..])==multiset(old(a[..]))
{
  var i := a.Length - 1;
  while (i > 0)
    invariant 0 <= i < a.Length
    invariant forall k,l :: i <= k < l < a.Length ==> a[k] <= a[l]
    invariant forall k,l :: 0 <= k < l <= i ==> a[k] <= a[l]
    invariant multiset(a[..]) == multiset(old(a[..]))
  {
    var j := 0;
    while (j < i)
      invariant 0 <= j <= i
      invariant forall k,l :: i <= k < l < a.Length ==> a[k] <= a[l]
      invariant forall k,l :: 0 <= k < l <= j ==> a[k] <= a[l]
      invariant forall k :: j <= k <= i ==> a[k] >= a[j]
      invariant multiset(a[..]) == multiset(old(a[..]))
    {
      if (a[j] > a[j + 1])
      {
        a[j], a[j + 1] := a[j + 1], a[j];
      }
      j := j + 1;
    }
    assert forall k :: 0 <= k <= i ==> a[k] >= a[i];
    i := i - 1;
  }
}