
method factImp(n: int) returns (r: int)
    requires n >= 0
    ensures r == fact(n)
{
    r := 1;
    var m := n;
    while (m > 0)
        invariant m >= 0
        invariant r == fact(n-m)*fact(m)
    {
        r := r*m;
        m := m-1;
    }
}

function power(n: int, m: nat) : int
    ensures power(n, m) == pow(n, m, 1)
{
    pow(n, m, 1)
}

function pow(n: int, m: nat, r: int) : int
    ensures pow(n, m, r) == powerAlt(n, m)
{
    if m == 0 then r else pow(n, m-1, r*n)
}

function powerAlt(n: int, m: nat) : int
    ensures powerAlt(n, m) == pow(n, m, 1)
{
    pow(n, m, 1)
}

function equivalentes(n: int, m: nat, r: int) : int
    ensures equivalentes(n, m, r) == power(n, m)
{
    pow(n, m, r)
}

lemma l1(n: int, m: nat, r: int)
    ensures equivalentes(n, m, r) == powerAlt(n, m)

function fact(n: nat) : nat
{
    if n == 0 then 1 else n*fact(n-1)
}

function factAcc(n: nat, a: int) : int
{
    if n == 0 then a else factAcc(n-1, n*a)
}

function factAlt(n: nat) : int { factAcc(n, 1) }

lemma factAcc_correct(n: nat, a: int)
    ensures factAcc(n, a) == fact(n)*a

lemma equiv(n: nat)
    ensures fact(n) == factAlt(n)
{
    factAcc_correct(n, 1);
}

function mystery1(n: nat, m: nat) : nat
    ensures mystery1(n, m) == n+m
{
    if n == 0 then m else mystery1(n-1, m+1)
}

function mystery2(n: nat, m: nat) : nat
    ensures mystery2(n, m) == n+m
{
    if m == 0 then n else mystery2(n+1, m-1)
}

function mystery3(n: nat, m: nat) : nat
    ensures mystery3(n, m) == n*m
{
    if n == 0 then 0 else m + mystery3(n-1, m)
}

function mystery4(n: nat, m: nat) : nat
    ensures mystery4(n, m) == power(n, m)
{
    if m == 0 then 1 else n * mystery4(n, m-1)
}

// 6

// 8

// 9

// 10

// 11