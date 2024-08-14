
method GetEven(s: array<nat>) modifies s
  ensures forall i :: 0 <= i < s.Length ==> 
    if old(s[i]) % 2 == 1 then s[i] == old(s[i]) + 1
    else s[i] == old(s[i])
{
  var i := 0;
  while i < s.Length 
    if old(s[i]) % 2 == 1 then s[i] == old(s[i]) + 1
    else s[i] == old(s[i])
  {
    // Loop Invariant: s[0..i-1] is unchanged
    // Loop Invariant: s[i] is even
    // Loop Invariant: s[i+1..s.Length-1] is unchanged
    
    if s[i] % 2 == 1 {
      s[i] := s[i] + 1;
    }
    i := i + 1;
  }
}

method evenTest()
{
  var a:array<nat> := new nat[][0,9,4];
  GetEven(a);
}
