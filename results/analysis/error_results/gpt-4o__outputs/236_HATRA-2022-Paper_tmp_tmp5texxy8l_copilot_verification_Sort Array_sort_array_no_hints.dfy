method sortArray(arr: array<int>) returns (arr_sorted: array<int>)
    // Requires array length to be between 0 and 10000
    requires 0 <= arr.Length < 10000
    // Ensuring the array has been sorted
    ensures sorted(arr_sorted, 0, arr_sorted.Length)
    // Ensuring that we have not modified elements but have only changed their indices
    ensures multiset(arr[..]) == multiset(arr_sorted[..])

    // Modifies arr
    modifies arr
{
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant multiset(arr[..]) == multiset(arr[..])
        invariant forall k :: 0 <= k < i ==> sorted(arr, 0, i)
    {
        var j := i + 1;
        while j < arr.Length
            invariant i < j <= arr.Length
            invariant multiset(arr[..]) == multiset(arr[..])
            invariant forall k :: 0 <= k < i ==> sorted(arr, 0, i)
            invariant forall k :: i < k < j ==> arr[i] <= arr[k]
        {
            if arr[i] > arr[j]
            {
                var temp := arr[i];
                arr[i] := arr[j];
                arr[j] := temp;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    arr_sorted := arr;
    return arr_sorted;
}

// Predicate to determine whether the list is sorted between [start, stop)
predicate sorted(arr: array<int>, start: int, end: int)
requires 0 <= start <= end <= arr.Length
reads arr
{
    forall i, j :: start <= i <= j < end ==> arr[i] <= arr[j]
}

// Predicate to determine whether element arr[pivot] is a pivot point
// Based on: https://github.com/stqam/dafny/blob/master/BubbleSort.dfy
predicate pivot(arr: array<int>, pivot: int)
requires 0 <= pivot <= arr.Length
reads arr
{
    forall u, v :: 0 <= u < pivot < v < arr.Length ==> arr[u] <= arr[v]
}