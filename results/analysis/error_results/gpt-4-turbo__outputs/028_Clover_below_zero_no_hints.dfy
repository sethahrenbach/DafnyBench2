method below_zero(operations: seq<int>) returns (s: array<int>, result: bool)
  ensures s.Length == |operations| + 1
  ensures s[0] == 0
  ensures forall i :: 0 <= i < s.Length - 1 ==> s[i + 1] == s[i] + operations[i]
  ensures result == true ==> (exists i :: 1 <= i <= |operations| && s[i] < 0)
  ensures result == false ==> forall i :: 0 <= i < s.Length ==> s[i] >= 0
{
  result := false;
  s := new int[|operations| + 1];
  s[0] := 0;

  var i := 1;
  // Loop invariant for maintaining the prefix sum and bounds
  invariant 1 <= i <= s.Length
  invariant s[0] == 0
  invariant forall j :: 1 <= j < i ==> s[j] == s[j-1] + operations[j-1]
  while i < s.Length
  {
    s[i] := s[i - 1] + operations[i - 1];
    i := i + 1;
  }

  i := 0;
  // Loop invariant for checking if any element is below zero
  invariant 0 <= i <= s.Length
  invariant result ==> (exists j :: 1 <= j < i && s[j] < 0)
  invariant !result ==> forall j :: 0 <= j < i ==> s[j] >= 0
  while i < s.Length
  {
    if s[i] < 0 {
      result := true;
      break;
    }
    i := i + 1;
  }
}