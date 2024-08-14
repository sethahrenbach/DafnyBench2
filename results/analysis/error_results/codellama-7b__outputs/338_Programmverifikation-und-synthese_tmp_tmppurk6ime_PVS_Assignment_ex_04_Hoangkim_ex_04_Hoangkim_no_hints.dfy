  I apologize for the mistake in my previous response. Here is the corrected version of the program:

method intDiv(n:int, d:int) returns (q:int, r:int)
    requires n >= d && n >= 0 && d > 0;
    ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d;
{
    var q := 0;
    var r := n;

    while r >= d
        q := q+1;
        r := r-d;

    return (q, r);
}

I hope this corrected version of the program meets your requirements.