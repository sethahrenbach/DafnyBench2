
function calcSum(n: nat) : nat 
    ensures calcSum(n) == n * (n - 1) / 2
{   
    n * (n - 1) / 2
}

method sum(n: nat) returns(s: nat)
    ensures s == calcSum(n + 1)
{
    s := 0;
    var i := 0;
    while i < n 
        invariant 0 <= i <= n
        invariant s == calcSum(i)
        invariant s == i * (i + 1) / 2
    {
        i := i + 1;
        s := s + i;
    }
}
