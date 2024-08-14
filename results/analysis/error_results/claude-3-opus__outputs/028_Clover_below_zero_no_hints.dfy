method below_zero(operations: seq<int>) returns (s:array<int>, result:bool)
  ensures s.Length == |operations| + 1
  ensures s[0]==0
  ensures forall i :: 0 <= i < s.Length-1 ==> s[i+1]==s[i]+operations[i]
  ensures result == true ==> (exists i :: 1 <= i <= |operations| && s[i] < 0)
  ensures result == false ==> forall i :: 0 <= i < s.Length ==> s[i] >= 0
{
  result := false;
  s := new int[|operations| + 1];
  var i := 0;
  s[i] := 0;
  while i < |operations|
    invariant 0 <= i <= |operations|
    invariant forall j :: 0 <= j <= i ==> s[j] == if j == 0 then 0 else s[j-1] + operations[j-1]
  {
    i := i + 1;
    s[i] := s[i - 1] + operations[i - 1];
  }
  assert s[0] == 0;
  assert forall i :: 0 <= i < |operations| ==> s[i+1]==s[i]+operations[i];
  
  i:=0;
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant result ==> exists j :: 1 <= j < i && s[j] < 0
    invariant !result ==> forall j :: 0 <= j < i ==> s[j] >= 0
  {
    if s[i] < 0 {
      result := true;
      break;
    }
    i := i + 1;
  }
  if result {
    assert exists i :: 1 <= i < s.Length && s[i] < 0;
  } else {
    assert forall i :: 0 <= i < s.Length ==> s[i] >= 0;
  }
}