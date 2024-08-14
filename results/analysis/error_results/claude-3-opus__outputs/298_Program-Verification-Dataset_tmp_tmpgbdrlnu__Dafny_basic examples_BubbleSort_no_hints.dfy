predicate sorted(a:array<int>, from:int, to:int)
  requires 0 <= from <= to <= a.Length;
  reads a;
{
  forall u, v :: from <= u < v < to ==> a[u] <= a[v]
}

predicate pivot(a:array<int>, to:int, pvt:int)
  requires 0 <= pvt < to <= a.Length;
  reads a;
{
  forall u, v :: 0 <= u < pvt < v < to ==> a[u] <= a[v]
}

method bubbleSort (a: array<int>)
  requires a.Length > 0;
  modifies a;
  ensures sorted(a, 0, a.Length);
  ensures multiset(a[..]) == multiset(old(a[..]));
{
  var i:nat := 1;

  while (i < a.Length)
    invariant 1 <= i <= a.Length;
    invariant sorted(a, 0, i);
    invariant multiset(a[..]) == multiset(old(a[..]));
  {
    ghost var a_old := a[..];
    var j:nat := i;
    while (j > 0)
      invariant 0 <= j <= i;
      invariant pivot(a, i, j);
      invariant sorted(a, 0, j) && sorted(a, j, i);
      invariant multiset(a[..]) == multiset(a_old[..]);
    {
      if (a[j-1] > a[j]) {
        a[j-1], a[j] := a[j], a[j-1];
      }
      j := j - 1;
    }
    assert sorted(a, 0, i) && (i == a.Length-1 || a[i] <= a[i+1]);
    i := i+1;
  }
}