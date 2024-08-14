// definition of Fibonacci numbers
function Fibonacci(n: nat): nat
  ensures Fibonacci(n) == Fibonacci(n - 1) + Fibonacci(n - 2)
{
  match n {
    case 0 => 0
    case 1 => 1
    case _ => Fibonacci(n - 1) + Fibonacci(n - 2)
  }
}

// iterative calculation of Fibonacci numbers
method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == Fibonacci(n)
{
  if n < 2 {
    return n;
  }

  var prev := 1;
  f := 1;
  var i := 2;

  while i < n
    invariant 1 <= i <= n &&
              f == Fibonacci(i) &&
              prev == Fibonacci(i - 1)
  {
    var temp := f;
    f := f + prev;
    prev := temp;
    i := i + 1;
  }
  assert f == Fibonacci(n - 1) + Fibonacci(n - 2);
  assert i == n;
}