
method mfirstCero(v:array<int>) returns (i:int)
  ensures 0 <= i <= v.Length
  ensures forall j :: 0 <= j < i ==> v[j] != 0
  ensures i != v.Length ==> v[i] == 0
{
  i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant forall j :: 0 <= j < i ==> v[j] != 0
    invariant i != v.Length ==> v[i] == 0
    invariant forall k :: i <= k < v.Length ==> v[k] != 0
  {
    assert 0 <= i <= v.Length;
    assert forall j :: 0 <= j < i ==> v[j] != 0;
    assert i != v.Length ==> v[i] == 0;
    assert forall k :: i <= k < v.Length ==> v[k] != 0;

    if v[i] == 0 {
      break;
    }
    i := i + 1;
  }
}
