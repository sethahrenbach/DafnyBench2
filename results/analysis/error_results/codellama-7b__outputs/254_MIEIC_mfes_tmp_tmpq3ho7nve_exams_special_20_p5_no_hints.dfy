
method binarySearch(a: array<T>, x: T) returns (index: int)
    requires sorted(a, a.Length)
    ensures sorted(a, a.Length)
    ensures 0 <= index <= a.Length
    ensures forall i :: 0 <= i < index ==> a[i] <= x
    ensures forall i :: index <= i < a.Length ==> a[i] >= x
{
    var low, high := 0, a.Length;
    while low < high
    {
        var mid := low + (high - low) / 2;
        if a[mid] < x
        {
            low := mid + 1;
        }
        else if a[mid] > x
        {
            high := mid;
        }
        else
        {
            return mid;
        }
    }
    return low;
}
