
method binarySearch(a: array<int>, x: int) returns (index: int)
    requires isSorted(a)
    ensures -1 <= index < a.Length
    ensures if index != -1 then a[index] == x
        else x !in a[..] //forall i :: 0 <= i < a.Length ==> a[i] != x
{
    var low, high := 0, a.Length;
    // loop invariant: low <= high <= a.Length
    // loop variant: high - low
    while low < high
        x !in a[..low] && x !in a[high..]
    {
        var mid := low + (high - low) / 2;
        if {
            case a[mid]  < x => low := mid + 1;
            case a[mid]  > x => high := mid;
            case a[mid] == x => return mid;
        }
    }
    return -1;
}
