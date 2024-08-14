
//Problem01
function fib(n: nat):nat
{
    if n < 2 then n else fib(n-2)+fib(n-1)
}

method fibIter(n:nat) returns (a:nat)
requires n > 0
ensures a == fib(n)
{
    a := 0;
    var b,x := 1,0;
    while x < n 
        invariant x <= n && a == fib(x) && b == fib(x+1)
        decreases n - x
    {
        a,b := b,a+b;
        x := x+1;
    }
}

//Problem02
function fact(n:nat):nat
{if n==0 then 1 else n*fact(n-1)}

method factIter(n:nat) returns (a:nat)
requires n >= 0;
ensures a == fact(n)
{
    a := 1;
    var i := 1;
    while i <= n
        invariant a == fact(i-1) && i >= 1 && i <= n+1
        decreases n - i + 1
    {
        a := a * i;
        i := i + 1;
    }
} 

//Problem03
function gcd(m: nat, n: nat): nat
    requires m > 0 && n > 0
{
    if m == n then m
    else if m > n then gcd(m - n, n)
    else gcd(m, n - m)
}

method gcdI(m: int, n: int) returns (g: int)
    requires  m > 0 && n > 0 
    ensures g == gcd(m, n)
{
    var x: int;
    g := m;
    x := n;
    while (g != x)
        invariant g > 0 && x > 0 && gcd(g, x) == gcd(m, n)
        decreases g + x
    {
        if (g > x)
        {
            g := g - x;
        }
        else
        {
            x := x - g;
        }
    }
}
