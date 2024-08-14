
predicate sorted(a: array<int>, start: int, end: int)
requires a != null
requires 0 <= start <= end <= a.Length
reads a
{
    forall j, k :: start <= j < k < end ==> a[j] <= a[k]
}

method InsertionSort(a: array<int>)
requires a != null && a.Length > 1
ensures sorted(a, 0, a.Length)
modifies a
{
    var up := 1;
    
    while up < a.Length
    invariant 1 <= up <= a.Length
    invariant sorted(a, 0, up)
    {
        var down := up - 1;
        var temp := a[up];
        while down >= 0 && a[down] > temp
        invariant 0 <= down < up
        invariant sorted(a, 0, up)
        invariant forall i :: down <= i < up ==> a[i] <= a[i + 1]
        {
            a[down + 1] := a[down];
            down := down - 1;
        }
        a[down + 1] := temp;
        up := up + 1;
    }
}

method Main()
{
    var a := new int[5];
    a[0], a[1], a[2], a[3], a[4] := 3, 2, 5, 1, 8;
    InsertionSort(a);
    print a[..];
}
