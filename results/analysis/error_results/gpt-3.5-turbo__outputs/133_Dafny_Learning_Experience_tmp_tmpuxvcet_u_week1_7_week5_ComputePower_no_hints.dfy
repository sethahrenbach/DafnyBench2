
function Power(n:nat):nat 
    ensures Power(n) == if n == 0 then 1 else 2 * Power(n-1);

method CalcPower(n:nat) returns (p:nat)
    ensures p == 2*n;
{
    p := 2*n;
}

method ComputePower(n:nat) returns (p:nat)
    ensures p == Power(n)
{
    var i := 0;
    var result := 1;
    while i < n
        invariant 0 <= i <= n
        invariant result == Power(i)
    {
        result := CalcPower(result);
        i := i + 1;
    }
    return result;
}
