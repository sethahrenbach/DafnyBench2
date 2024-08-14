
method buscar(a:array<int>, x:int) returns (r:int)
    ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != x
    ensures 0 <= r < a.Length ==> a[r] == x
{
    r := 0;
    while r < a.Length
    {
        // Invariant: 0 <= r <= a.Length and forall i :: 0 <= i < r ==> a[i] != x
        // Loop invariant: 0 <= r <= a.Length and forall i :: 0 <= i < r ==> a[i] != x
        // Postcondition: 0 <= r < a.Length and a[r] == x
        // Precondition: True
        if a[r] == x
        {
            return r;
        }
        r := r + 1;
    }
    // Postcondition: r < 0 and forall i :: 0 <= i < a.Length ==> a[i] != x
    return -1;
}
