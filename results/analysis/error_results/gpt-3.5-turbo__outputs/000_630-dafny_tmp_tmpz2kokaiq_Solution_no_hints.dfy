function sorted(a: array<int>) : bool
    reads a
{
    forall i,j : int :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

method BinarySearch(a: array<int>, x: int) returns (index: int)
    requires sorted(a)
    ensures 0 <= index < a.Length ==> a[index] == x
    ensures index == -1 ==> forall i : int :: 0 <= i < a.Length ==> a[i] != x
{
    var low := 0;
    var high := a.Length;
    var mid := 0;
    
    while (low < high)
        invariant 0 <= low <= high <= a.Length
        invariant high >= low ==> a[high - 1] >= x
        invariant low <= high ==> a[low] <= x
        decreases high - low
    {
        mid := low + (high - low) / 2;
        if a[mid] < x {
            low := mid + 1;
        }
        else if a[mid] > x {
            high := mid;
        }
        else {
            assert a[mid] == x;
            assert 0 <= mid < a.Length;
            return mid;
        }
    }
    assert high == low;
    assert forall i: int :: 0 <= i < a.Length ==> a[i] != x;
    return -1;
}