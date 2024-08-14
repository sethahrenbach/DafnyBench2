method multipleReturns (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures less < x < more
{
    more := x + y;
    less := x - y;
    assert less < x < more;
}

method multipleReturns2 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more + less == 2*x
{
    more := x + y;
    less := x - y;
    assert more + less == 2*x;
}

// TODO: Hacer en casa
method multipleReturns3 (x:int, y:int) returns (more:int, less:int)
requires y > 0
ensures more - less == 2*y
{
    more := x + y;
    less := x - y;
    assert more - less == 2*y;
}

function factorial(n:int):int
requires n>=0
{
    if n==0 || n==1 then 1 else n*factorial(n-1)
}

// PROGRAMA VERIFICADOR DE WHILE
method ComputeFact (n:int) returns (f:int)
requires n >=0
ensures f== factorial(n)
{   
    f:=1;
    var x:=n;
    while x > 0 
    decreases x
    invariant x >= 0
    invariant f * factorial(x) == factorial(n)
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
    decreases n - x
    invariant 0 <= x <= n
    invariant f * factorial(n - x) == factorial(n)
    {
        x:=x+1;
        f:= f*x;
    }
    assert f == factorial(n);
}

// n>=1 ==> 1 + 3 + 5 + ... + (2*n-1) = n*n
method Sqare(a:int) returns (x:int)
requires a>=1
ensures x == a*a
{
    var y:=1;
    x:=1;
    while y < a 
    decreases a - y
    invariant 1 <= y <= a
    invariant x == (y - 1) * (y - 1) + 2 * (y - 1) + 1
    {
        y:= y+1;
        x:= x+ (2*y-1);
    }
    assert x == a * a;
}

function sumSerie(n:int):int
requires n >=1 
{
    if n==1 then 1 else sumSerie(n-1) + 2*n -1
}

lemma {:induction false} Sqare_Lemma (n:int)
requires n>=1
ensures sumSerie(n) == n*n
{
    if n==1 {}
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
    var y:=1;
    x:=1;
    while y < a 
    decreases a - y
    invariant 1 <= y <= a
    invariant x == (y - 1) * (y - 1) + 2 * (y - 1) + 1
    {
        y:= y+1;
        x:= x +2*y -1;
    }
    assert x == a * a;
}