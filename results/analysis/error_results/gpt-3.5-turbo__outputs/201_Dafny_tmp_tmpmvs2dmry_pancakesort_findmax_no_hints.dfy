method findMax(a: array<int>, n: int) returns (r: int)
  requires a.Length > 0
  requires 0 < n <= a.Length
  ensures 0 <= r < n <= a.Length;
  ensures forall k :: 0 <= k < n ==> a[r] >= a[k];
  ensures multiset(a[..n]) == multiset(old(a[..n]));
{
  var mi: int;
  var i: int;
  mi := 0;
  i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant 0 <= mi < a.Length
    invariant forall k :: 1 <= k < i ==> a[mi] >= a[k-1];
    invariant multiset(a[..i]) == multiset(old(a[..i]));
  {
    assert 1 <= i <= n;
    assert 0 <= mi < a.Length;
    assert forall k :: 1 <= k < i ==> a[mi] >= a[k-1];
    assert multiset(a[..i]) == multiset(old(a[..i]));

    if a[i] > a[mi]
    {
      mi := i;
    }
    i := i + 1;
  }
  return mi;
}