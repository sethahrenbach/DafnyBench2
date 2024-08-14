method non_overlapping_intervals(intervals: array2<int>) returns (count: int)
    modifies intervals
    requires 1 <= intervals.Length0 <= 100000
    requires intervals.Length1 == 2
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 0] <= 50000
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 1] <= 50000
    // TODO: modify the ensures clause so that count is indeed equal to the minimum number of intervals we need to remove to make the rest of the intervals non-overlapping.
    ensures count >= 0
    ensures count == intervals.Length0 - (|set j | 0 <= j < intervals.Length0 && (forall k :: 0 <= k < j ==> intervals[k, 1] <= intervals[j, 0])|)
{
    var row := intervals.Length0;
    if (row == 0)
    {
        return 0;
    }

    bubble_sort(intervals);
    
    var i := 1;
    count := 1;
    var end := intervals[0, 1];
    while (i < row)
        invariant 1 <= i <= row
        invariant 0 <= count <= i
        invariant forall k :: 0 <= k < i ==> intervals[k, 1] <= end || intervals[k, 0] >= end
        invariant forall k :: 0 <= k < i - 1 ==> intervals[k, 1] <= intervals[k + 1, 1]
    {
        if (intervals[i, 0] >= end)
        {
            count := count + 1;
            end := intervals[i, 1];
        }

        i := i + 1;
    }

    return row - count;
}


// Bubble Sort
method bubble_sort(a: array2<int>)
    modifies a
    requires a.Length1 == 2
    ensures sorted(a, 0, a.Length0 - 1)
{
    var i := a.Length0 - 1;
    while (i > 0)
        invariant 0 <= i < a.Length0
        invariant partitioned(a, i)
    {
        var j := 0;
        while (j < i)
            invariant 0 <= j <= i
            invariant forall k :: 0 <= k < j ==> a[k, 1] <= a[k + 1, 1]
        {
            if (a[j, 1] > a[j + 1, 1])
            {
                a[j, 0], a[j + 1, 0] := a[j + 1, 0], a[j, 0];
                a[j, 1], a[j + 1, 1] := a[j + 1, 1], a[j, 1];
            }
            j := j + 1;
        }
        i := i -1;
    }
}


// Predicates for Bubble Sort
predicate sorted(a: array2<int>, l: int, u: int)
    reads a
    requires a.Length1 == 2
{
    forall i, j :: 0 <= l <= i <= j <= u < a.Length0 ==> a[i, 1] <= a[j, 1]
}

predicate partitioned(a: array2<int>, i: int)
    reads a
    requires a.Length1 == 2
{
    forall k, k' :: 0 <= k <= i < k' < a.Length0 ==> a[k, 1] <= a[k', 1]
}