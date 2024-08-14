
method SqrSum(n: int) returns (s: int)
{
    var i, k: int;
    s := 0;
    k := 1;
    i := 1;
    while (i <= n)
        invariant 1 <= i <= n+1
        invariant s == ((i-1)*i*(2*i-1))/6
        invariant k == 2*i-1
        decreases n - i + 1
    {
        s := s + k;
        k := k + 2 * i + 1;
        i := i + 1;
    }
}

method DivMod(a: int, b: int) returns (q: int, r: int)
{
    q := 0;
    r := a;
    while (r >= b)
        invariant a == b*q + r && r >= 0
        decreases r
    {
        r := r - b;
        q := q + 1;
    }
}

method HoareTripleAssmAssrt()
{
    var i: int := *;
    var k: int := *;
    assume k == i*i;
    k := k + 2 * i + 1;
    assert k == (i+1)*(i+1); // Ensuring the postcondition is explicitly stated
}

method HoareTripleReqEns(i: int, k: int) returns (k': int)
    requires k == i*i
    ensures k' == (i+1)*(i+1)
{
    k' := k + 2 * i + 1;
}

method Invariant1()
{
    var n: int :| n >= 0;
    var y := n;
    var x := 0;
    while (y >= 0)
        invariant x + y == n
        decreases y
    {
        x := x + 1;
        y := y - 1;
    }
}

function SqrSumRec(n: int): int
    requires n >= 0
{
    if (n == 0) then 0 else n*n + SqrSumRec(n-1)
}

method SqrSum1(n: int) returns (s: int)
    requires n >= 0
    ensures s == SqrSumRec(n)
{
    var i, k: int;
    s := 0;
    k := 1;
    i := 1;
    while (i <= n)
        invariant 1 <= i <= n+1
        invariant s == SqrSumRec(i-1)
        invariant k == 2*i-1
        decreases n - i
    {
        s := s + k;
        k := k + 2 * i + 1;
        i := i + 1;
    }
}

method DivMod1(a: int, b: int) returns (q: int, r: int)
    requires b > 0 && a >= 0
    ensures a == b*q + r && 0 <= r < b
{
    q := 0;
    r := a;
    while (r >= b)
        invariant a == b*q + r && r >= 0
        decreases r
    {
        r := r - b;
        q := q + 1;
    }
}

method Main()
{
    var v := SqrSum(5);
    print "SqrSum(5): ", v, "\n";

    var q, r := DivMod(5, 3);
    print "DivMod(5, 3): ", q, ", ", r, "\n";
}
