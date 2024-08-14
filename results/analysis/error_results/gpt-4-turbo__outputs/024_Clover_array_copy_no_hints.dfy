method iter_copy<T>(s: array<T>) returns (t: array<T>)
  ensures s.Length == t.Length
  ensures forall i :: 0 <= i < s.Length ==> s[i] == t[i]
{
  t := new T[s.Length](i => s[i]);
  var i := 0;
  while (i < s.Length)
    invariant 0 <= i <= s.Length
    invariant forall j :: 0 <= j < i ==> t[j] == s[j]
  {
    t[i] := s[i];
    i := i + 1;
  }
}