method iter_copy<T>(s: array<T>) returns (t: array<T>)
  requires s != null
  requires s.Length > 0
  ensures t != null
  ensures s.Length == t.Length
  ensures forall i :: 0 <= i < s.Length ==> s[i] == t[i]
{
  t := new T[s.Length];
  var i := 0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall j :: 0 <= j < i ==> s[j] == t[j]
    decreases s.Length - i
  {
    t[i] := s[i];
    assert forall j :: 0 <= j <= i ==> s[j] == t[j];
    i := i + 1;
  }
}