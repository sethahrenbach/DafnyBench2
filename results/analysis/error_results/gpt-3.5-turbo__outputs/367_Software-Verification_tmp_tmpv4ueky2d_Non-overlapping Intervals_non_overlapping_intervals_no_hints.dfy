
method non_overlapping_intervals(intervals: array2<int>) returns (count: int)
    modifies intervals
    requires 1 <= intervals.Length0 <= 100000
    requires intervals.Length1 == 2
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 0] <= 50000
    requires forall i :: 0 <= i < intervals.Length0 ==> -50000 <= intervals[i, 1] <= 50000
    ensures count >= 0
    ensures count == intervals.Length0 - count
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
        invariant 1 <= count <= i
        invariant forall k :: 0 <= k < i ==> intervals[k, 1] >= end
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
            invariant 0 <= j < i
            invariant partitioned(a, j)
        {
            if (a[j, 1] > a[j + 1, 1])
            {
                var temp := a[j, 1];
                a[j, 1] := a[j + 1, 1];
                a[j + 1, 1] := temp;
            }
            j := j + 1;
        }
        i := i - 1;
    }
}


// Predicates for Bubble Sort
predicate sorted(a: array2<int>, l: int, u: int)
    reads a
    requires a.Length1 == 2
{
    forall i, j :: l <= i < j <= u ==> a[i, 1] <= a[j, 1]
}

predicate partitioned(a: array2<int>, i: int)
    reads a
    requires a.Length1 == 2
{
    forall k :: 0 <= k < i < a.Length0 - 1 ==> a[k, 1] <= a[k + 1, 1]
}
