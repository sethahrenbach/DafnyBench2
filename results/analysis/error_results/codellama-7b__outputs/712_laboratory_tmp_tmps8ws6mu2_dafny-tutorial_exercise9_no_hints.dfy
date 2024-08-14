  function fib(n: nat): nat
{
  if n == 0 then 0 else
  if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (b: nat)
  ensures b == fib(n)
{
  var i: int := 0;
  var b1: nat := 0;
  var c: nat := 1;
  while i < n
  {
    b1 := c;
    c := c + b1;
    i := i + 1;
  }
  b := b1;
  assert b == fib(n);
  assert c == fib(n - 1) + fib(n - 2);
}