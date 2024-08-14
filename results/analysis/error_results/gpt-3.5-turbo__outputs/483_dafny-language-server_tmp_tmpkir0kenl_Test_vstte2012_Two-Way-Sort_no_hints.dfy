
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method swap<T>(a: array<T>, i: int, j: int)
  requires 0 <= i < j < a.Length
  modifies a
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var t := a[i];
  a[i] := a[j];
  a[j] := t;
}

method two_way_sort(a: array<bool>)
  modifies a
  ensures forall m,n :: 0 <= m < n < a.Length ==> (!a[m] || a[n])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var i := 0;
  var j := a.Length - 1;
  while (i <= j)
    invariant 0 <= i <= a.Length
    invariant 0 <= j < a.Length
    invariant forall k :: 0 <= k < i ==> !a[k]
    invariant forall k :: j < k < a.Length ==> a[k]
    invariant multiset(a[..]) == old(multiset(a[..]))
  {
    if (!a[i]) {
      i := i+1;
    } else if (a[j]) {
      j := j-1;
    } else {
      swap(a, i, j);
      i := i+1;
      j := j-1;
    }
  }
}
