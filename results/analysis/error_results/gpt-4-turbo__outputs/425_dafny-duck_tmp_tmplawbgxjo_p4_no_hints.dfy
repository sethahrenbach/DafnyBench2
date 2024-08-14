method single(x: array<int>, y: array<int>) returns (b: array<int>)
  requires x.Length > 0
  requires y.Length > 0
  ensures b[..] == x[..] + y[..]
{
  b := new int[x.Length + y.Length];
  var i := 0;
  var index := 0;

  while (i < x.Length)
    invariant 0 <= i <= x.Length
    invariant index == i
    invariant forall j :: 0 <= j < i ==> b[j] == x[j]
  {
    b[index] := x[i];
    i := i + 1;
    index := index + 1;
  }

  i := 0;

  while (i < y.Length)
    invariant 0 <= i <= y.Length
    invariant index == x.Length + i
    invariant forall j :: 0 <= j < i ==> b[x.Length + j] == y[j]
  {
    b[index] := y[i];
    i := i + 1;
    index := index + 1;
  }

  assert forall k :: 0 <= k < x.Length + y.Length ==> b[k] == (if k < x.Length then x[k] else y[k - x.Length]);
}

method Main()
{
  var a := new int[4];
  a[0] := 1; a[1] := 5; a[2] := 2; a[3] := 3;
  var b := new int[3];
  b[0] := 4; b[1] := 3; b[2] := 5;
  var c := new int[7];
  c := single(a, b);
  //print c[..];
}