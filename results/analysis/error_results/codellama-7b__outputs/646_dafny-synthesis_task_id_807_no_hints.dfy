
method FindFirstOdd(a: array<int>) returns (found: bool, index: int)
    requires a != null
    ensures !found ==> forall i :: 0 <= i < a.Length ==> !IsOdd(a[i])
    ensures found ==> 0 <= index < a.Length && IsOdd(a[index]) && forall i :: 0 <= i < index ==> !IsOdd(a[i])
{
    found := false;
    index := 0;
    while (index < a.Length)
    {
        // Loop Invariant: !found ==> forall i :: 0 <= i < index ==> !IsOdd(a[i])
        // Loop Invariant: found ==> 0 <= index < a.Length && IsOdd(a[index]) && forall i :: 0 <= i < index ==> !IsOdd(a[i])
        if IsOdd(a[index])
        {
            found := true;
            return;
        }
        index := index + 1;
    }
}

function IsOdd(x: int): bool
{
    return x % 2 != 0;
}
