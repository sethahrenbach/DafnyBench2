
method FindSmallest(s: array<int>) returns (min: int)
  requires s.Length > 0
  ensures forall i :: 0 <= i < s.Length ==> min <= s[i]
  ensures exists i :: 0 <= i < s.Length && min == s[i]
{
  min := s[0];
  var i: int := 1;
  while i < s.Length
    invariant 1 <= i <= s.Length
    invariant forall j :: 0 <= j < i ==> min <= s[j];
  {
    if s[i] < min
    {
      min := s[i];
    }
    i := i + 1;
  }
  min
}
