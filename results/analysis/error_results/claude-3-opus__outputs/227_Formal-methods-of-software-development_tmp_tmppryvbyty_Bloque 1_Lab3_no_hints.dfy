method multipleReturns (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures less < x < more
{
    more := x + y;
    less := x - y;
}

method multipleReturns2 (x:int, y:int) returns (more:int, less:int) 
requires y > 0
ensures more + less == 2*x
{
    more := x + y;
    less := x - y;
}

method multipleReturns3 (x:int, y:int) returns (more:int, less:int)
requires y > 0 
ensures more - less == 2*y
{
    more := x + y;
    less := x - y;
}

function factorial(n:int):int
requires n>=0
{
    if n==0 || n==1 then 1 else n*factorial(n-1)
}

method ComputeFact (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)
{   
    f:=1;
    var x:=n;
    while x > 0 
    invariant x >= 0 && f == factorial(n-x)
    {
        f:= f*x;
        x:=x-1;
    }
    assert f == factorial(n);
}

method ComputeFact2 (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)
{
    var x:= 0;
    f:= 1;
    while x<n
    invariant 0 <= x <= n && f == factorial(x)
    {
        x:=x+1;
        f:= f*x;
    }
    assert f == factorial(n);
}

method Sqare(a:int) returns (x:int)
requires a>=1
ensures x == a*a
{
    var y:=0;
    x:=0;
    while y < a 
    invariant 0 <= y <= a && x == y*y
    {
        y:= y+1;
        x:= x+ (2*y-1);
    }
    assert x == a*a;
}

function sumSerie(n:int):int
requires n >=0
{
    if n==0 then 0 else sumSerie(n-1) + 2*n -1
}

lemma {:induction false} Sqare_Lemma (n:int)
requires n>=0
ensures sumSerie(n) == n*n
{
    if n==0 {}
    else{
        Sqare_Lemma(n-1);

        calc == {
            sumSerie(n);
            sumSerie(n-1) + 2*n -1;
            {
                Sqare_Lemma(n-1);
            }
            (n-1)*(n-1) + 2*n -1;
            n*n-2*n+1 +2*n -1;
            n*n;
        }
    }
}

method Sqare2(a:int) returns (x:int)
requires a>=1
ensures x == a*a
{
    var y:=0;
    x:=0;
    while y < a
    invariant 0 <= y <= a && x == sumSerie(y)
    {
        y:= y+1;
        x:= x +2*y -1;
    }
    Sqare_Lemma(a);
    assert x == a*a;
}