predicate sorted_between(a: array<int>, from: nat, to: nat)
  reads a;
  requires a != null;
  requires from <= to;
  requires to <= a.Length;
{
  forall i, j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate sorted(a: array<int>)
  reads a;
  requires a != null;
{
  sorted_between(a, 0, a.Length)
}

method bubbleSort(a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;
  ensures sorted(a);
  ensures multiset(old(a[..])) == multiset(a[..]);
{
  var i: nat := 0;

  while i < a.Length
    invariant 0 <= i <= a.Length;
    invariant forall k :: 0 <= k < i ==> sorted_between(a, 0, k + 1);
  {
    var j: nat := a.Length - 1;
    while j > i
      invariant i <= j < a.Length;
      invariant forall k :: i <= k < j ==> a[k] <= a[k+1];
    {
      if a[j-1] > a[j] {
        var temp: int := a[j-1];
        a[j-1] := a[j];
        a[j] := temp;
      }
      j := j - 1;
    }
    i := i + 1;
  }
}