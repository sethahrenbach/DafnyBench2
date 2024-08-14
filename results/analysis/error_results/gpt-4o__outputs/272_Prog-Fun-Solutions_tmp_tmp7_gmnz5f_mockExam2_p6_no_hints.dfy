// problem 6:
// name:      Gabriele Berardi
// s-number: s4878728
// table:     XXXXX

function f(n: int): int {
  if n <= 0 then 1 else n + f(n-1)*f(n-2)
}

function fSum(n: nat): int {
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
    invariant 0 <= k <= n
    invariant a == fSum(k)
    invariant x == if k == 0 then 1 else f(k-1)
    invariant y == if k == 0 then 2 else if k == 1 then 2 else k + f(k-1)*f(k-2)
    decreases n - k
  {
    a := a + x;
    k := k + 1;
    x, y := y, k + 1 + f(k-1)*f(k-2);    
  }
}