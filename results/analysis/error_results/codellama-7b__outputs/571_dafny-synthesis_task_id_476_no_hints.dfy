
method SumMinMax(a: array<int>) returns (sum: int)
    requires a.Length > 0
    ensures sum == Max(a[..]) + Min(a[..])
{
    var minVal := a[0];
    var maxVal := a[0];

    for i := 1 to a.Length
    {
        // Loop Invariant: minVal and maxVal are the minimum and maximum values of the prefix of a up to index i
        assert minVal <= maxVal;
        assert maxVal <= a[i];
        assert minVal <= a[i];

        if a[i] < minVal {
            minVal := a[i];
        } else if a[i] > maxVal {
            maxVal := a[i];
        }
    }
    // Postcondition: minVal and maxVal are the minimum and maximum values of the entire array a
    assert minVal <= maxVal;
    assert maxVal <= a[a.Length-1];
    assert minVal <= a[a.Length-1];

    sum := minVal + maxVal;
}

function Min(a: seq<int>) : int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
        var minPrefix := Min(a[..|a|-1]);
        // Postcondition: minPrefix is the minimum value of the prefix of a up to index |a|-1
        assert minPrefix <= a[|a|-1];
        if a[|a|-1] <= minPrefix then a[|a|-1] else Min(a[..|a|-1])
}

function Max(a: seq<int>) : int
    requires |a| > 0
{
    if |a| == 1 then a[0]
    else
        var maxPrefix := Max(a[..|a|-1]);
        // Postcondition: maxPrefix is the maximum value of the prefix of a up to index |a|-1
        assert maxPrefix >= a[|a|-1];
        if a[|a|-1] >= maxPrefix then a[|a|-1] else Max(a[..|a|-1])
}
