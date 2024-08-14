method TriangleNumber(N: int) returns (t: int)
    requires N >= 0
    ensures t == N * (N + 1) / 2
{
    t := 0;
    var n := 0;
    while n < N
        invariant 0 <= n <= N
        invariant t == n * (n + 1) / 2
        decreases N - n
    {
        n := n + 1;
        t := t + n;
    }
    assert t == N * (N + 1) / 2;
}