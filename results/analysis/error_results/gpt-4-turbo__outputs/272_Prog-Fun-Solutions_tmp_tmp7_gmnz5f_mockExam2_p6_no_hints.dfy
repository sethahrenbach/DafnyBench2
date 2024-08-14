// problem 6:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXXX

ghost function f(n: int): int {
  if n <= 0 then 1 else n + f(n-1)*f(n-2)
}

ghost function fSum(n: nat): int {
 // give the body of this function
  // it should return Sum(i: 0<=i < n: f(i))
  if n <= 0 then 0 else f(n-1) + fSum(n-1)
}

method problem6(n:nat) returns (a: int)
ensures a == fSum(n)
{
  a := 0;
  var k := 0;
  var x := 1;
  var y := 2;

  while k < n
    invariant k <= n
    invariant a == fSum(k)
    invariant x == f(k)
    invariant y == k+1 + f(k)*f(k-1)
  {
    k := k + 1;
    a := a + x;
    var tempX := x;
    x := y;
    y := k+1 + tempX*y;    
  }
}