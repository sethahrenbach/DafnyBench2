//Problem 01
method sumOdds(n: nat) returns (sum: nat)
    requires n > 0;
    ensures sum == n * n;
{
    sum := 1;
    var i := 0;
    
    while i < n-1
        invariant 0 <= i <= n-1
        invariant sum == (i+1)*(i+1)
    {
        i := i + 1;
        sum := sum + 2 * i + 1;
        //assert sum == (i+1)*(i+1);
    }
    assert i == n-1;
    assert sum == n*n;
}

//problem02
//a)
method intDiv(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0 ;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d; 
{
    q := n / d;
    r := n % d;
    if q > n/2 {
        q := n/2;
        r := n - d*q;
    }
    assert 0 <= q <= n/2 && 0 <= r < d;
}

//b)c)
method intDivImpl(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d; 
{
    q := 0;
    r := n;
    while r >= d
        invariant r >= 0
        invariant (d*q) + r == n
        invariant 0 <= q <= n/2
        decreases r
    {
        if q == n/2 {
            break;
        }
        r := r - d;
        q := q + 1;
    }
    if r >= d {
        r := n - d * (n/2);
        q := n/2;
    }
    assert 0 <= q <= n/2 && r == n - d*q;
    assert 0 <= r < d;
}