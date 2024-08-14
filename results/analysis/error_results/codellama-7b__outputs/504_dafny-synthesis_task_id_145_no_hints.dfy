
method MaxDifference(a: array<int>) returns (diff: int)
    requires a.Length > 1
    ensures diff <= a[a.Length - 1] - a[0]
{
    var minVal := a[0];
    var maxVal := a[0];

    for i := 1 to a.Length
    {
        // Loop invariant: minVal is the minimum value seen so far, and maxVal is the maximum value seen so far
        assert 0 <= minVal && 0 <= maxVal;
        assert forall j :: 0 <= j < i ==> a[j] <= minVal;
        assert forall j :: i <= j < a.Length ==> a[j] <= maxVal;

        if a[i] < minVal {
            minVal := a[i];
        } else if a[i] > maxVal {
            maxVal := a[i];
        }
    }
    diff := maxVal - minVal;
}
