
function fib(n: nat): nat
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

method fibonacci1(n:nat) returns (f:nat)
requires n >= 0
ensures f == fib(n)
{
   var i := 0;
   var a := 0;
   var b := 1;
   while i < n
   invariant 0 <= i <= n
   invariant a == fib(i)
   invariant b == fib(i + 1)
   invariant i <= n
   invariant f == fib(n)
   {
      a, b := b, a + b;
      i := i + 1;
   }
   f := a;
}

method fibonacci2(n:nat) returns (f:nat)
requires n >= 0
ensures f == fib(n)
{
    if (n == 0) {
        f := 0;
    }
    else {
        var i := 1;
        var a := 0;
        var b := 1;
        while i < n
        invariant 0 <= i <= n
        invariant a == fib(i - 1)
        invariant b == fib(i)
        invariant i <= n
        invariant f == fib(n)
        {
            a, b := b, a + b;
            i := i + 1;
        }
        f := b;
    }
}

method fibonacci3(n:nat) returns (f:nat)
requires n >= 0
ensures f == fib(n)
{
    var i := 0;
    var a := 0;
    var b := 1;
    f := 0;
    while i < n
    invariant 0 <= i <= n
    invariant a == fib(i)
    invariant b == fib(i + 1)
    invariant i <= n
    invariant f == fib(n)
    {
        a, b := b, a + b;
        i := i + 1;
    }
    f := a;
}
