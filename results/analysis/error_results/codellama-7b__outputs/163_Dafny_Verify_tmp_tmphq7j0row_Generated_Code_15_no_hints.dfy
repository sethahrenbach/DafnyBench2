
method main(n: int, k: int) returns (k_out: int)
    requires n > 0;
	requires k > n;
	ensures k_out >= 0;
{
	k_out := k;
    var j: int := 0;
    while(j < n)
    {
        j := j + 1;
        k_out := k_out - 1;
        // Loop Invariant: k_out >= 0
        // Loop Invariant: j <= n
        // Loop Invariant: k_out - j <= k
    }
    // Postcondition: k_out >= 0
    // Postcondition: k_out - n <= k
}
