  I apologize for the confusion, and thank you for the feedback. Here's another attempt at the solution:

function fib(n: nat): nat
{
  if n == 0 then 0 
  else if n == 1 then 1 
  else fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: nat) returns (f: nat)
  ensures f == fib(n);
{
  if (n == 0) 
    { f := 0; }
  else {
    var i := 1;
    var f_2 := 0;
    var f_1 := 0;
        f   := 1;    
    while (i < n) 
    {
      // Loop invariant: f_2 = fib(n-2), f_1 = fib(n-1), f = fib(n)
      assert(f_2 == fib(n-2));
      assert(f_1 == fib(n-1));
      assert(f == fib(n));

      f_2 := f_1;
      f_1 := f; 
      f   := f_1 + f_2;

      i := i + 1;
    }
  }
}

This solution should now pass the Dafny verification.