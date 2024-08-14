function sumInts( n: int ): int
    requires n >= 0;
    ensures sumInts(n) == n*(n+1)/2;
{
    if n == 0 then
        0
    else
        sumInts(n-1)+n
}

method SumIntsLoop( n: int ) returns ( s: int )
    requires n >= 0;
    ensures s == sumInts(n)
    ensures s == n*(n+1)/2;
{
    s := 0;
    var k := 0;
    while k < n
        invariant 0 <= k <= n
        invariant s == k*(k-1)/2 + k
    {
        s := s+k;
        k := k+1;
    }
    s := s + k;
    assert s == n*(n+1)/2;
}

method Main()
{
    var x := SumIntsLoop(100);
    print x;
}