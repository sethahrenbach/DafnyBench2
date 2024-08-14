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
    var f_1 := 1;
    f := 1;    

    while (i < n)
      invariant 1 <= i < n
      invariant f_2 == fib(i-1)
      invariant f_1 == fib(i)
      invariant f == fib(i)
    {
      f_2 := f_1;
      f_1 := f;
      f := f_1 + f_2;

      i := i + 1;
    }
  }
}