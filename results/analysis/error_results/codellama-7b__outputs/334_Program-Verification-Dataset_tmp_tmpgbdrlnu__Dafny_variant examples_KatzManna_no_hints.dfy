
method NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) returns (z: int)
  ensures proveFunctionalPostcondition ==> z == if x > 101 then x-10 else 91;
  loop invariant 0 <= y1 <= 100;
  loop invariant 0 <= y2 <= 10;
  loop invariant y1 == x - 10 * y2;
{
  var y1 := x;
  var y2 := 1;
  while (true)
    // the following two invariants are needed only to prove the postcondition
    // the following two lines justify termination, as in the paper by Katz and Manna
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
  loop invariant x1 >= x2;
  loop invariant x2 >= 1;
{
  var y1 := x1;
  var y2 := x2;
  while (y1 != y2)
  {
    while (y1 > y2)
    {
      y1 := y1 - y2;
    }
    while (y2 > y1)
    {
      y2 := y2 - y1;
    }
  }
}

method Determinant(X: array2<int>, M: int) returns (z: int)
  requires 1 <= M;
  requires X != null && M == X.Length0 && M == X.Length1;
  modifies X;
  loop invariant 0 <= a <= M;
  loop invariant 0 <= b <= M;
  loop invariant 0 <= c <= M;
  loop invariant X[a-1,a-1] != 0;
  loop invariant X[b-1,c-1] == X[b-1,c-1] - X[b-1,a-1] / X[a-1,a-1] * X[a-1,c-1];
{
  var y := X[1-1,1-1];
  var a := 1;
  while (a != M)
  {
    var b := a + 1;
    while (b != M+1)
    {
      var c := M;
      while (c != a)
      {
        assume X[a-1,a-1] != 0;
        X[b-1, c-1] := X[b-1,c-1] - X[b-1,a-1] / X[a-1,a-1] * X[a-1,c-1];
        c := c - 1;
      }
      b := b + 1;
    }
    a := a + 1;
    y := y * X[a-1,a-1];
  }
  z := y;
}
