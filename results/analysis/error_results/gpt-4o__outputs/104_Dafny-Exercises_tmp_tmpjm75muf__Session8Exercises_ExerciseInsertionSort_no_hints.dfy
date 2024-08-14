predicate sorted_seg(a:array<int>, i:int, j:int) //i and j included
requires 0 <= i <= j+1 <= a.Length
reads a
{
    forall l, k :: i <= l <= k <= j ==> a[l] <= a[k]
}

method InsertionSort(a: array<int>)
  modifies a;
  ensures sorted_seg(a,0,a.Length-1) 
  ensures multiset(a[..]) == old(multiset(a[..])) //Add and prove this
{
  var i := 0;
  while (i < a.Length)
    invariant 0 <= i <= a.Length
    invariant sorted_seg(a, 0, i-1)
    invariant multiset(a[..i]) == old(multiset(a[..i]))
  {
    var temp := a[i];
    var j := i;
    while (j > 0 && temp < a[j - 1])
      invariant 0 <= j <= i
      invariant multiset(a[..i+1]) == old(multiset(a[..i+1]))
      invariant sorted_seg(a, 0, j-1)
      invariant forall k :: j <= k < i ==> a[k] > temp
    {
      a[j] := a[j - 1];
      j := j - 1;
    }
    a[j] := temp;
    i := i + 1;
  }
  assert sorted_seg(a, 0, a.Length-1);
  assert multiset(a[..]) == old(multiset(a[..]));
}