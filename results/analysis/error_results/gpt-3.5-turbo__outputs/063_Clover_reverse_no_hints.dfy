
method reverse(a: array<int>)
  modifies a
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i])
{
  var i := 0;
  while i < a.Length / 2
    invariant 0 <= i <= a.Length / 2
    invariant forall j :: 0 <= j < i ==> a[j] == old(a[a.Length - 1 - j])
    invariant forall j :: a.Length / 2 <= j < a.Length ==> a[j] == old(a[a.Length - 1 - j])
  {
    assert 0 <= i < a.Length;
    assert 0 <= a.Length - 1 - i < a.Length;
    assert i < a.Length / 2;
    assert a.Length - 1 - i >= a.Length / 2;
    assert a[i] == old(a[a.Length - 1 - i]);
    assert a[a.Length - 1 - i] == old(a[i]);

    var temp := a[i];
    a[i] := a[a.Length - 1 - i];
    a[a.Length - 1 - i] := temp;

    i := i + 1;
  }

  assert forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i]);
}
