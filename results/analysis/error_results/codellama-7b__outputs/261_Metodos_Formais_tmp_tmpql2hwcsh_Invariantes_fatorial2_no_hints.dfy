
function Fat(n:nat):nat
{
    if n == 0 then 1 else n*Fat(n-1)
}

method Fatorial(n:nat) returns (f:nat)
ensures f == Fat(n)
{
    f := 1;
    var i := 1;
    decreases n;
    while i <= n
    {
        f := f * i;
        i := i + 1;
    }
    return f;
}
