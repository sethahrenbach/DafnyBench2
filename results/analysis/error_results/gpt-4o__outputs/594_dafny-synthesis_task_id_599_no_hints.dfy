method SumAndAverage(n: int) returns (sum: int, average: real)
    requires n > 0
    ensures sum == n * (n + 1) / 2
    ensures average == sum as real / n as real
{
    sum := 0;
    var i: int;
    // Loop invariant
    // 1. 0 <= i <= n
    // 2. sum == i * (i + 1) / 2
    // 3. sum is non-negative
    for i := 0 to n
        invariant 0 <= i <= n
        invariant sum == i * (i + 1) / 2
        invariant sum >= 0
    {
        sum := sum + (i + 1);
    }
    assert i == n + 1;
    assert sum == n * (n + 1) / 2;
    average := sum as real / n as real;
}