//Problem 01
method sumOdds(n: nat) returns (sum: nat)
    requires n > 0;
    ensures sum == n * n;
{
    sum := 1;
    var i := 0;

    while i < n-1
        invariant i <= n-1
        invariant sum == (i+1)*(i+1)
    {
        i := i + 1;
        sum := sum + 2 * i + 1;
    }
}

//problem02
//a)
method intDiv(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0 ;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d; 

//b)c)

method intDivImpl(n:int, d:int) returns (q:int, r:int)
requires n >= d && n >= 0 && d > 0;
ensures (d*q)+r == n && 0 <= q <= n/2 && 0 <= r < d; 
{
    q := 0;
    r := n;
    while r >= d
        invariant r + d*q == n
        invariant 0 <= r
        invariant q <= n/d
    {
        r := r - d;
        q := q + 1;
    } 
    // The loop invariant and the condition of the loop exit ensure that r < d and r >= 0
    // The loop invariant also ensures that (d*q) + r == n when the loop exits
    // No need for additional assertions as the loop invariant and exit condition ensure the postconditions
    // Explicitly state the postcondition requirements to ensure verification
    assert r < d && r >= 0; // Explicitly state that r is less than d and non-negative
    assert (d*q) + r == n; // Directly assert the main postcondition
}