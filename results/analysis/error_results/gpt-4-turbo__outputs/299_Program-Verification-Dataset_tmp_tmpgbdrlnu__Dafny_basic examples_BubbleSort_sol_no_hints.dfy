predicate sorted_between (a:array<int>, from:nat, to:nat)
  reads a;
  requires a != null;
  requires from <= to;
  requires to <= a.Length;
{
  forall i,j :: from <= i < j < to && 0 <= i < j < a.Length ==> a[i] <= a[j]
}
  
predicate sorted (a:array<int>)
  reads a;
  requires a!=null;
{
  sorted_between (a, 0, a.Length)
}

method bubbleSort (a: array<int>)
  modifies a;
  requires a != null;
  requires a.Length > 0;
  ensures sorted(a);
  ensures multiset(old(a[..])) == multiset(a[..]);
{
  var i:nat := 1;

  while (i < a.Length)
    invariant 1 <= i <= a.Length
    invariant sorted_between(a, 0, i)
    invariant multiset(old(a[..])) == multiset(a[..])
  {
    var j:nat := i;
    while (j > 0)
      invariant 1 <= j <= i
      invariant sorted_between(a, 0, j)
      invariant multiset(old(a[..])) == multiset(a[..])
    {
      if (a[j-1] > a[j]) {
        var temp:int := a[j-1];
        a[j-1] := a[j];
        a[j] := temp;
        assert sorted_between(a, 0, j+1); // Strengthening the invariant assertion
      }
      j := j - 1;
    }
    i := i + 1;
  }
}