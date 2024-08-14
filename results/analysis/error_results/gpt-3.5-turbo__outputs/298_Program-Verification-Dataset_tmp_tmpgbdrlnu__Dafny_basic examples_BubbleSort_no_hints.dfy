predicate sorted(a: array<int>, from: int, to: int)
  requires a != null;
  reads a;
  requires 0 <= from <= to <= a.Length;
{
  forall u, v :: from <= u < v < to ==> a[u] <= a[v]
}

method bubbleSort(a: array<int>)
  requires a != null && a.Length > 0;
  modifies a;
  ensures sorted(a, 0, a.Length);
  ensures multiset(a[..]) == multiset(old(a[..]));
{
  var i: nat := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length;
    invariant forall k :: 0 <= k < i ==> sorted(a, 0, k+1);
    decreases a.Length - i;
  {
    var j: nat := a.Length - 1;
    while j > i
      invariant i <= j < a.Length;
      invariant forall k :: i <= k < j ==> a[k] <= a[k+1];
      decreases j - i;
    {
      if a[j] < a[j-1] {
        var temp: int := a[j];
        a[j] := a[j-1];
        a[j-1] := temp;
      }
      j := j - 1;
    }
    i := i + 1;
  }
}