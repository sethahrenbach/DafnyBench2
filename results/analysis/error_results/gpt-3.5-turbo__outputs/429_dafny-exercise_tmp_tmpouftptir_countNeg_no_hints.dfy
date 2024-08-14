function verifyNeg(a: array<int>, idx: int) : nat
  reads a
  requires 0 <= idx <= a.Length
{
  if idx == 0 then 0 
  else verifyNeg(a, idx - 1) + (if a[idx - 1] < 0 then 1 else 0)
}

method CountNeg(a: array<int>) returns (cnt: nat) 
  ensures cnt == verifyNeg(a, a.Length)
{
  var i := 0;
  cnt := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant cnt <= verifyNeg(a, a.Length)
    invariant forall k :: 0 <= k < i ==> a[k] >= 0
    decreases a.Length - i
  {
    if a[i] < 0 {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
}

method Main()
{
  var arr: array<int> := new int[4];
  arr[0] := -1;
  arr[1] := 2;
  arr[2] := -3;
  arr[3] := 4;
  var res := CountNeg(arr);
}
