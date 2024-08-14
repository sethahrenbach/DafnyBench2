method sortArray(arr: array<int>) returns (arr_sorted: array<int>)
    requires 0 <= arr.Length < 10000
    ensures sorted(arr_sorted, 0, arr_sorted.Length)
    ensures multiset(arr[..]) == multiset(arr_sorted[..])
    modifies arr
{
    var i := 0;
    while i < arr.Length
        invariant 0 <= i <= arr.Length
        invariant sorted(arr, 0, i)
        invariant multiset(arr[..]) == multiset(old(arr[..]))
    {
        var j := i + 1;
        while j < arr.Length
            invariant i + 1 <= j <= arr.Length
            invariant sorted(arr, 0, j)
            invariant multiset(arr[..]) == multiset(old(arr[..]))
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

predicate sorted(arr: array<int>, start: int, end: int)
    requires 0 <= start <= end <= arr.Length
    reads arr
{
    forall i, j :: start <= i <= j < end ==> arr[i] <= arr[j]
}