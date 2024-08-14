
method min(a: array<int>, n: int) returns (min: int)
    requires 0 < n <= a.Length;
    ensures (exists i: int :: 0 <= i && i < n && a[i] == min);
    ensures (forall i: int :: 0 <= i && i < n ==> a[i] >= min);
{
    var i: int;

    min := a[0];
    i := 1;

    while (i < n)
    {
        // Loop invariant: min is the minimum value in the array a[0..i-1]
        assert min <= a[i];

        if (a[i] < min)
        {
            // Update min
            min := a[i];
        }

        // Increment i
        i := i + 1;
    }

    // Postcondition: min is the minimum value in the entire array a[0..n-1]
    assert min <= a[n-1];
}
