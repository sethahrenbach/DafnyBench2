
method double_array_elements(s: array<int>)
  modifies s
  ensures forall i :: 0 <= i < s.Length ==> s[i] == 2 * old(s[i])
{
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall j :: 0 <= j < i ==> s[j] == 2 * old(s[j])
  {
    assert 0 <= i < s.Length;
    assert s[i] == 2 * old(s[i]);

    s[i] := 2 * old(s[i]);
    i := i + 1;
  }
}
