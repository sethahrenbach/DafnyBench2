
function abs(a: int): nat
{
  if a < 0 then -a else a
}

method aba(a: array<int>): array<int>
{
  var b: array<int> := new int[a.Length];
  var i: int := 0;

  while i < a.Length
  {
    b[i] := abs(a[i]);
    i := i + 1;
  }

  return b;
}

method Main()
{
  var a: array<int> := new int[][1, -2, -2, 1];
  var b: array<int> := aba(a);
}
