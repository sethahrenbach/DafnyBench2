
method incrementArray(a:array<int>)
  requires a.Length > 0
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
  modifies a
{
  var j : int := 0;
  while(j < a.Length)
    invariant 0 <= j <= a.Length
    invariant forall k :: 0 <= k < j ==> a[k] == old(a[k]) + 1
  {
    assert 0 <= j < a.Length;
    assert forall k :: 0 <= k < j ==> a[k] == old(a[k]) + 1;
    
    a[j] := a[j] + 1;
    j := j+1;
    
    assert forall k :: 0 <= k < j ==> a[k] == old(a[k]) + 1;
  }
  assert j == a.Length;
  assert forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1;
}
