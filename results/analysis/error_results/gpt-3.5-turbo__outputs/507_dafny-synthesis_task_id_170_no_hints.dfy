function sumTo( a:array<int>, start:int, end:int ) : int
    requires a != null;
    requires 0 <= start && start <= end && end <= a.Length;
    reads a;
    ensures result == (if start == end then 0 else sumTo(a, start, end-1) + a[end-1]);

    decreases end - start;

    if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]

method SumInRange(a: array<int>, start: int, end: int) returns (sum: int)
    requires a != null
    requires 0 <= start && start <= end && end <= a.Length
    ensures sum == sumTo(a, start, end)
{
    sum := 0;
    var i := start;
    while i <= end
        invariant start <= i <= end + 1
        invariant sum == sum + a[i-1]
        invariant i <= end + 1
    {
        assert sum == sumTo(a, start, i-1);
        sum := sum + a[i];
        i := i + 1;
    }
}