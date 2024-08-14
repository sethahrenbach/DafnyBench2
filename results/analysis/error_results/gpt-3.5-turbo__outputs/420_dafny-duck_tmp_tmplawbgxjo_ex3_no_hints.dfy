predicate sortedbad(s: string)
{
  // no b's after non-b's
  forall i, j :: 0 <= i < j < |s| && s[i] == 'b' && s[j] != 'b' ==> i < j &&
  // only non-d's before d's
  forall i, j :: 0 <= i < j < |s| && s[i] != 'd' && s[j] == 'd' ==> i < j
}

method BadSort(a: string) returns (b: string)
  requires forall i :: 0 <= i < |a| ==> a[i] in {'b', 'a', 'd'}
  ensures sortedbad(b)
  ensures multiset(b[..]) == multiset(a[..])
{
  b := a;
  var next: int := 0;
  var aPointer: int := 0;
  var dPointer: int := |b|;

  while (next < dPointer)
    invariant 0 <= next <= |b|
    invariant 0 <= aPointer <= next
    invariant dPointer <= |b|
    invariant forall k :: 0 <= k < |b| ==> (k < next ==> (b[k] == 'a' || (k < aPointer && b[k] == 'b')) || (k >= dPointer ==> b[k] == 'd'))
  {
    if b[next] == 'a' {
      next := next + 1;
    } 
    else if b[next] == 'b' {
      assert aPointer < next;
      b := b[next := b[aPointer]][aPointer := b[next]];
      next := next + 1;
      aPointer := aPointer + 1;
    }
    else {
      assert dPointer > next;
      dPointer := dPointer - 1;
      b := b[next := b[dPointer]][dPointer := b[next]];
    } 
  } 
}