
method SearchLoop(a: seq<real>, i: int, j: int, x: real) returns (k: int)
    requires 0 <= i <= j <= |a|;
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
    while p != q
    {
        var m := p + (q-p)/2;
        if a[m] < x
        {
            q := m;
        }
        else
        {
            p := m+1;
        }
    }
    return p;
}
