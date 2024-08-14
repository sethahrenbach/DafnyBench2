
method Minimum(a: array<int>) returns (m: int)
    requires a.Length > 0
    ensures exists i :: 0 <= i < a.Length && m == a[i]
    ensures forall i :: 0 <= i < a.Length ==> m <= a[i]
{
    var n := 0;
    m := a[0];
    while n < a.Length
    {
        // Loop invariant: m is the minimum element in the subarray a[0..n]
        assert 0 <= n < a.Length;
        assert m <= a[n];

        if a[n] < m {
            m := a[n];
        }
        n := n + 1;
    }
    // Postcondition: m is the minimum element in the entire array a
    assert 0 <= n < a.Length;
    assert m <= a[n];
}
