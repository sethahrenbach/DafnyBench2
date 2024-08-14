
method NinetyOne(x: int, ghost proveFunctionalPostcondition: bool) returns (z: int)
  ensures proveFunctionalPostcondition ==> z == if x > 101 then x-10 else 91;
{
  var y1 := x;
  var y2 := 1;
  while (true)
    invariant y1 >= 0;
    invariant y2 >= 0;
    invariant y1 + y2 * 10 == x;
    invariant y2 <= x / 10 + 1;
    invariant y1 <= x - y2 * 10;
    invariant (y1 > 100 ==> y2 == 1);
    invariant (y1 <= 100 ==> y1 + 11 <= x);
    invariant (y1 <= 100 ==> y2 + 1 <= x / 10 + 1);
    invariant (y1 <= 100 ==> y1 - 10 <= x);
    invariant (y1 <= 100 ==> y2 <= x / 10 + 1);
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
{
  var y1 := x1;
  var y2 := x2;
  while (y1 != y2)
    invariant y1 > 0;
    invariant y2 > 0;
    invariant gcd(y1, y2) == gcd(x1, x2);
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
{
  var y := X[1-1,1-1];
  var a := 1;
  while (a != M)
    invariant 1 <= a <= M;
    invariant y == product(i | 1 <= i <= a :: X[i-1,i-1]);
    invariant forall i,j :: 1 <= i < a && a < j <= M :: X[j-1,a-1] == 0;
  {
    var b := a + 1;
    while (b != M+1)
      invariant a < b <= M + 1;
      invariant forall i,j :: 1 <= i < a && a < j < b :: X[j-1,a-1] == 0;
    {
      var c := M;
      while (c != a)
        invariant a <= c <= M;
        invariant forall i,j :: 1 <= i < a && a < j < b && c < j <= M :: X[j-1,a-1] == 0;
        invariant X[a-1,a-1] != 0;
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
