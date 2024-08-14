// definition of Fibonacci numbers
function Fibonacci(n: nat): nat {
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

  while i <= n
    invariant 2 <= i <= n + 1
    invariant f == Fibonacci(i - 1)
    invariant prev == Fibonacci(i - 2)
    invariant forall j :: 2 <= j < i ==> Fibonacci(j) == Fibonacci(j - 1) + Fibonacci(j - 2)
  {
    prev, f := f, f + prev;
    i := i + 1;
  }

  assert f == Fibonacci(n);
}