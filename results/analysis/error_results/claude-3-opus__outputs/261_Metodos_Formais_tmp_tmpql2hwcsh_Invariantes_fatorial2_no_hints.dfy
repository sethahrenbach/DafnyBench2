function Fat(n:nat):nat
{
    if n == 0 then 1 else n*Fat(n-1)
}

method Fatorial(n:nat) returns (f:nat)
ensures f == Fat(n)
{
    f := 1;
    var i := 0;
    while i < n
    invariant 0 <= i <= n
    invariant f == Fat(i)
    decreases n - i
    {
        //assert f == Fat(i);
        //assert i < n;
        i := i + 1;
        //assert f == Fat(i-1);
        f := f * i;
        //assert f == Fat(i-1) * i;
        //assert i > 0 ==> Fat(i) == Fat(i-1) * i;
        //assert f == Fat(i);
    }
    //assert i == n;
    //assert f == Fat(n);
    return f;
}