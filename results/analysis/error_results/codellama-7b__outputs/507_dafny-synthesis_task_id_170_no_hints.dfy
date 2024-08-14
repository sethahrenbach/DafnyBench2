  I apologize for the mistake in my previous answer. Here is the corrected version of the program:

function sumTo(a: array<int>, start: int, end: int): int
    requires a != null;
    requires 0 <= start && start <= end && end <= a.Length;
    reads a;
    loop invariant 0 <= start && start <= end && end <= a.Length;
    loop invariant sumTo(a, start, end-1) + a[end-1] == sumTo(a, start, end);
    {
        if (start == end) then 0 else sumTo(a, start, end-1) + a[end-1]
    }

    method SumInRange(a: array<int>, start: int, end: int) returns (sum: int)
    requires a != null;
    requires 0 <= start && start <= end && end <= a.Length;
    ensures sum == sumTo(a, start, end);
    loop invariant 0 <= start && start <= end && end <= a.Length;
    loop invariant sum == sumTo(a, start, end);
    {
        sum := 0;
        for i := start to end
        {
            sum := sum + a[i];
        }
    }

I hope this corrected version of the program passes the test.