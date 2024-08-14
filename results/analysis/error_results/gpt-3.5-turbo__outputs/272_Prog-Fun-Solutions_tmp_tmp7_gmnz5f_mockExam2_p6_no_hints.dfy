// problem 6:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXXX

ghost function f(n: int): int {
  if n <= 0 then 1 else n + f(n-1)*f(n-2)
}

ghost function fSum(n: nat): int {
  if n <= 0 then 0 else f(n-1) + fSum(n-1)
}

method problem6(n:nat) returns (a: int)
requires n >= 0
ensures a == fSum(n)
{
  a := 0;
  var k := 0;
  var x := 1;
  var y := 1;
  while k < n
    invariant 0 <= k <= n
    invariant a == fSum(k)
    invariant x == f(k)
    invariant y == f(k+1)
    invariant x*f(k) + y*f(k+1) == f(k+1)*f(k)
  {
    k := k + 1;
    a := a + x;

    x, y := y, x + y;
  }
}