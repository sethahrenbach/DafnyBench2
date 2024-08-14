
method SearchRecursive(a: seq<real>, i: int, j: int, x: real) returns (k: int)
    requires 0 <= i <= j <= a.Length;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j;
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;
{
    if i == j
    {
        return i;
    }
    var m := i + (j-i)/2;
    if a[m] < x
    {
        k := SearchRecursive(a, i, m, x);
    }
    else
    {
        k := SearchRecursive(a, m+1, j, x);
    }
}

method SearchLoop(a: seq<real>, i: int, j: int, x: real) returns (k: int)
    requires 0 <= i <= j <= a.Length;
    requires forall p, q :: i <= p < q < j ==> a[p] >= a[q];
    ensures i <= k <= j;
    ensures forall r | i <= r < k :: a[r] >= x;
    ensures forall r | k <= r < j :: a[r] < x;
{
    if i == j
    {
        return i;
    }
    var p := i;
    var q := j;
    while p < q
        invariant i <= p <= q <= j;
        invariant forall r | i <= r < p :: a[r] >= x;
        invariant forall r | q < r < j :: a[r] < x;
    {
        var m := p + (q-p)/2;
        if a[m] < x
        {
            q := m;
        }
        else
        {
            p := m + 1;
        }
    }
    return p;
}

method Test(a: seq<real>, x: real)
    requires forall p, q | 0 <= p < q < a.Length :: a[p] >= a[q];
{
    var k1 := SearchLoop(a, 0, a.Length, x);
    var k2 := SearchRecursive(a, 0, a.Length, x);
}
