
method iter_copy<T>(s: array<T>) returns (t: array<T>)
  ensures s.Length==t.Length
  ensures forall i::0<=i<s.Length ==> s[i]==t[i]
{
  t := new T[s.Length];
  var i:= 0;
  while (i < s.Length)
  {
    // Loop Invariant: t[0..i-1] == s[0..i-1]
    assert t[0..i-1] == s[0..i-1];

    // Loop Invariant: t[i] == s[i]
    assert t[i] == s[i];

    // Postcondition: t[i] == s[i]
    assert t[i] == s[i];

    t[i] := s[i];
    i:=i+1;
  }
}
