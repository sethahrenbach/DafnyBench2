
// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

method NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) returns (z: int)
  ensures proveFunctionalPostcondition ==> z == if x > 101 then x - 10 else 91;
{
  var y1 := x;
  var y2 := 1;
  while (y2 != 1 || y1 <= 100)
    invariant proveFunctionalPostcondition ==> (y2 == 1 && y1 > 100) ==> z == y1 - 10
    invariant proveFunctionalPostcondition ==> (y2 != 1 || y1 <= 100) ==> z == 91
    decreases y2, 101 - y1
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
}

method Gcd(x1: int, x2: int)
  requires 1 <= x1 && 1 <= x2;
{
  var y1 := x1;
  var y2 := x2;
  while (y1 != y2)
    invariant 1 <= y1 && 1 <= y2
    decreases y1 + y2
  {
    if (y1 > y2) {
      y1 := y1 - y2;
    } else {
      y2 := y2 - y1;
    }
  }
}

method Determinant(X: array2<int>, M: int) returns (z: int)
  requires 1 <= M;
  requires X != null && M == X.Length0 && M == X.Length1;
  modifies X;
{
  var y := X[0, 0];
  var a := 1;
  while (a < M)
    invariant 1 <= a < M
    invariant forall i: int, j: int | 0 <= i < a && 0 <= j < M :: X[i, j] == old(X[i, j]) {:trigger X[i, j]}
    decreases M - a
  {
    var b := a + 1;
    while (b <= M)
      invariant a < b <= M
      invariant forall j: int | a <= j < M :: X[b-1, j] == old(X[b-1, j]) {:trigger X[b-1, j]}
      decreases M - b
    {
      var c := M;
      while (c > a)
        invariant a < c <= M
        invariant forall k: int | c < k <= M :: X[b-1, k] == old(X[b-1, k]) {:trigger X[b-1, k]}
        decreases c - a
      {
        assume X[a-1, a-1] != 0;
        X[b-1, c-1] := X[b-1, c-1] - X[b-1, a-1] / X[a-1, a-1] * X[a-1, c-1];
        c := c - 1;
      }
      b := b + 1;
    }
    a := a + 1;
    y := y * X[a-1, a-1];
  }
  z := y;
}
