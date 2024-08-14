
method findMax (a : array<int>, n : int) returns (r:int)
  requires a.Length > 0
  requires 0 < n <= a.Length
  ensures 0 <= r < n <= a.Length
  ensures forall k :: 0 <= k < n <= a.Length ==> a[r] >= a[k]
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var mi;
  var i;
  mi := 0;
  i := 0;
  while (i < n)
  {
    // loop invariant: a[mi] >= a[i]
    assert a[mi] >= a[i];
    // loop invariant: a[mi] >= a[i] && a[i] >= a[mi]
    assert a[mi] >= a[i] && a[i] >= a[mi];
    // loop invariant: a[mi] >= a[i] && a[i] >= a[mi] && a[mi] >= a[i]
    assert a[mi] >= a[i] && a[i] >= a[mi] && a[mi] >= a[i];
    if (a[i] > a[mi])
    { 
      mi := i; 
    }
    i := i + 1;
  }
  return mi;
}
