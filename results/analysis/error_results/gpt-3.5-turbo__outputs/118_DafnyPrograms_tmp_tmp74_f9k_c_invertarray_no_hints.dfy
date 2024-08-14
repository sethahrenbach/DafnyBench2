
/**
  Inverts an array of ints.
 */
method InvertArray(a: array<int>)
  modifies a
  ensures forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length-1-i])
{
  var index := 0;

  while index < a.Length / 2
    invariant 0 <= index <= a.Length / 2
    invariant forall i | 0 <= i < index :: a[i] == old(a[a.Length-1-i])
    invariant forall i | a.Length - index <= i < a.Length :: a[i] == old(a[a.Length-1-i])
    invariant forall i | index <= i < a.Length - index :: a[i] == old(a[a.Length-1-i])
  {
    assert a[index] == old(a[a.Length - 1 - index]);
    assert a[a.Length - 1 - index] == old(a[index]);
    var temp := a[index];
    a[index] := a[a.Length - 1 - index];
    a[a.Length - 1 - index] := temp;
    index := index + 1;
  }

  assert forall i | 0 <= i < a.Length :: a[i] == old(a[a.Length-1-i]);
}
