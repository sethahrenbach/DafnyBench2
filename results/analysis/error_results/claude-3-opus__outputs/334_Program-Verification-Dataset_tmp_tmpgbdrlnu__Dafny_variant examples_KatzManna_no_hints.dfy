// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) returns (z: int)
  ensures proveFunctionalPostcondition ==> z == if x > 101 then x-10 else 91;
{
  var y1 := x;
  var y2 := 1;
  while (true)
    invariant y1 + 10*y2 == x + 11
    invariant y2 >= 1
    decreases if y1 > 100 then y2 else 101 - y1
  {
    if (y1 > 100) {
      if (y2 == 1) {
        break;
      } else {
        y1 := y1 - 10;
        y2 := y2 - 1;
      }
    } else {
      y1 := y1 + 11;
      y2 := y2 + 1;
    }
  }
  z := y1 - 10;
  assert y1 == if x > 101 then x else 101;
}

method Gcd(x1: int, x2: int)
  requires 1 <= x1 && 1 <= x2;
{
  var y1 := x1;
  var y2 := x2;
  while (y1 != y2)
    invariant y1 > 0 && y2 > 0
    invariant x1 % y1 == 0 && x2 % y1 == 0
    invariant x1 % y2 == 0 && x2 % y2 == 0
    decreases y1 + y2
  {
    while (y1 > y2)
      invariant y1 > 0 && y2 > 0
      invariant x1 % y1 == 0 && x2 % y1 == 0
      invariant x1 % y2 == 0 && x2 % y2 == 0
      decreases y1
    {
      y1 := y1 - y2;
    }
    while (y2 > y1)
      invariant y1 > 0 && y2 > 0
      invariant x1 % y1 == 0 && x2 % y1 == 0
      invariant x1 % y2 == 0 && x2 % y2 == 0
      decreases y2
    {
      y2 := y2 - y1;
    }
  }
}

method Determinant(X: array2<int>, M: int) returns (z: int)
  requires 1 <= M;
  requires X != null && M == X.Length0 && M == X.Length1;
  modifies X;
{
  var y := X[0,0];
  var a := 1;
  while (a != M)
    invariant 1 <= a <= M
    invariant forall i,j :: 0 <= i < a && 0 <= j < M && i != j ==> X[i,j] == 0
    invariant y == (var p := 1; for i := 0 to a-1 { p := p * X[i,i]; } p)
    decreases M - a
  {
    var b := a + 1;
    while (b != M+1)
      invariant a+1 <= b <= M+1
      invariant forall i,j :: 0 <= i < a && 0 <= j < M && i != j ==> X[i,j] == 0
      invariant forall i,j :: a <= i < b-1 && a <= j < M && i != j ==> X[i,j] == 0
      decreases M+1 - b
    {
      var c := M;
      while (c != a)
        invariant a <= c <= M
        invariant forall i,j :: 0 <= i < a && 0 <= j < M && i != j ==> X[i,j] == 0
        invariant forall i,j :: a <= i < b && a <= j < c && i != j ==> X[i,j] == 0
        decreases c
      {
        assume X[a-1,a-1] != 0;
        var factor := X[b-1,a-1] / X[a-1,a-1];
        X[b-1, c-1] := X[b-1,c-1] - factor * X[a-1,c-1];
        c := c - 1;
      }
      b := b + 1;
    }
    a := a + 1;
    y := y * X[a-1,a-1];
  }
  z := y;
}