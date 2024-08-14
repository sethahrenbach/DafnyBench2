method UpWhileLess(N: int) returns (i: int)
    requires 0 <= N
    ensures i == N
{
    i := 0;
    while i < N 
        invariant 0 <= i <= N
        decreases N - i
    {
        i := i + 1;
    }
}

method UpWhileNotEqual(N: int) returns (i: int)
    requires 0 <= N
    ensures i == N
{
    i := 0;
    while i != N
        invariant 0 <= i <= N + 1
        decreases N - i
    {
        i := i + 1;
    }
}

method DownWhileNotEqual(N: int) returns (i: int)
    requires 0 <= N
    ensures i == 0
{
    i := N;
    while i != 0 
        invariant 0 <= i <= N + 1
        decreases i
    {
        i := i - 1;
    }
}

method DownWhileGreater(N: int) returns (i: int)
    requires 0 <= N
    ensures i == 0
{
    i := N;
    while 0 < i 
        invariant 0 <= i <= N + 1
        decreases i
    {
        i := i - 1;
    }
}

method Quotient()
{
    var x, y := 0, 191;
    while 7 <= y
        invariant 0 <= x <= 28 && 0 <= y <= 191
        decreases y
    {
        y := y - 7;
        x := x + 1;
    }
}

method Quotient1() 
{
    var x, y := 0, 191;
    while 7 <= y
        invariant 0 <= x <= 28 && 0 <= y <= 191
        decreases y
    {
        x, y := x + 1, y - 7;
    }
}