
method sort(a: array<int>) returns (b: array<int>)
  requires a.Length > 0
  ensures b.Length == a.Length
  ensures b[0] == a[0]
  ensures b[1] == a[1]
  ensures b[2] == a[2]
  ensures b[3] == a[3]
  ensures b[4] == a[4]
  ensures b[5] == a[5]
  ensures b[6] == a[6]
  ensures b[7] == a[7]
  ensures b[8] == a[8]
  ensures b[9] == a[9]
{
  var i := 0;
  var j := 1;
  while j < a.Length do
    if a[j] < a[i] then
      i := j;
    j := j + 1;
  b[0] := a[i];
  b[1] := a[i + 1];
  b[2] := a[i + 2];
  b[3] := a[i + 3];
  b[4] := a[i + 4];
  b[5] := a[i + 5];
  b[6] := a[i + 6];
  b[7] := a[i + 7];
  b[8] := a[i + 8];
  b[9] := a[i + 9];
  return b;
}
