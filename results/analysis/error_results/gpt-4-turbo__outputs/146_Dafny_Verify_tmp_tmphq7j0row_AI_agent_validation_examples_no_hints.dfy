
function Power(n: nat): nat {
    if n == 0 then 1 else 2 * Power(n - 1)
}

method ComputePower(N: int) returns (y: nat) requires N >= 0
    ensures y == Power(N)
{
    y := 1;
    var x := 0; 
    while x < N
        decreases N - x
        invariant 0 <= x <= N
        invariant y == Power(x)
    {
        x := x + 1;
        y := 2 * y;
    } 
}

method Max(a: array<nat>) returns (m: int)
    ensures forall i :: 0 <= i < a.Length ==> a[i] <= m
    ensures (m == 0 && a.Length == 0) || exists i :: 0 <= i < a.Length && m == a[i] 
{
    m := 0;
    var n := 0;
    while n < a.Length
        invariant 0 <= n <= a.Length
        invariant forall i :: 0 <= i < n ==> a[i] <= m
        invariant m == (if n == 0 then 0 else a[..n].Max())
    {
        if m < a[n] {
            m := a[n]; 
        }
        n := n + 1; 
    }
}

method Cube(n: nat) returns (c: nat)
    ensures c == n * n * n
{
    c := 0;
    var i := 0;
    var k := 1;
    var m := 6;
    while i < n
        invariant 0 <= i <= n
        invariant c == i * i * i
        invariant k == 6 * i + 1
        invariant m == 6
    {
        c := c + k;
        k := k + m;
        i := i + 1;
    }
}

method IncrementMatrix(a: array2<int>)
    modifies a
    ensures forall i, j :: 0 <= i < a.Length0 && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
{
    var m := 0;
    while m < a.Length0
        invariant 0 <= m <= a.Length0
        invariant forall i, j :: 0 <= i < m && 0 <= j < a.Length1 ==> a[i,j] == old(a[i,j]) + 1
    {
        var n := 0;
        while n < a.Length1
            invariant 0 <= n <= a.Length1
            invariant forall j :: 0 <= j < n ==> a[m,j] == old(a[m,j]) + 1
        {
            a[m,n] := a[m,n] + 1;
            n := n + 1; 
        }
        m := m + 1; 
    }
}

method CopyMatrix(src: array2, dst: array2)
    requires src.Length0 == dst.Length0 && src.Length1 == dst.Length1
    modifies dst
    ensures forall i, j :: 0 <= i < src.Length0 && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
{
    var m := 0;
    while m < src.Length0
        invariant 0 <= m <= src.Length0
        invariant forall i, j :: 0 <= i < m && 0 <= j < src.Length1 ==> dst[i,j] == old(src[i,j])
    {
        var n := 0;
        while n < src.Length1
            invariant 0 <= n <= src.Length1
            invariant forall j :: 0 <= j < n ==> dst[m,j] == old(src[m,j])
        {
            dst[m,n] := src[m,n]; n := n + 1;
        }
        m := m + 1; 
    }
}

method DoubleArray(src: array<int>, dst: array<int>)
    requires src.Length == dst.Length
    modifies dst
    ensures forall i :: 0 <= i < src.Length ==> dst[i] == 2 * old(src[i])
{
    var n := 0;
    while n < src.Length
        invariant 0 <= n <= src.Length
        invariant forall i :: 0 <= i < n ==> dst[i] == 2 * old(src[i])
    {
        dst[n] := 2 * src[n]; n := n + 1;
    } 
}
