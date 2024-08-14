
method SqrSum(n: int) returns (s: int)
    requires n >= 0
    ensures s == SqrSumRec(n)
{
    var i,k : int;
    s := 0;
    k := 1;
    i := 1;
    while (i <= n)
        invariant 1 <= i <= n+1 && k == i*i
        decreases n - i
    {
        assert s == SqrSumRec(i-1);
        s := s + k;
        k := k + 2 * i + 1;
        i := i+1;
    }
    assert s == SqrSumRec(n);
}

function SqrSumRec(n: int) : int
    requires n >= 0
{
    if (n == 0) then 0 else n*n + SqrSumRec(n-1)
}

least lemma L1(n: int)
    requires n >= 0
    ensures SqrSumRec(n) == n*(n+1)*(2*n + 1)/6
{
    // OK
}

method DivMod(a: int, b: int) returns (q: int, r: int)
    requires b > 0
    requires a >= 0
    ensures a == b*q + r
    ensures 0 <= r < b
{
    q := 0;
    r := a;
    while (r >= b)
        invariant a == b*q + r
        invariant r >= 0
        invariant r < b
        decreases r
    {
        r := r - b;
        q := q + 1;
    }
    assert a == b*q + r;
    assert 0 <= r < b;
}

method Main()
{
    var v := SqrSum(5);
    print "SqrSum(5): ", v, "\n";

    var q, r := DivMod(5, 3);
    print "DivMod(5, 3): ", q, ", ", r, "\n";
}
