method SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
    requires n > 0
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n  - 14 * n + 7) / 15
{
    sum := 0;
    var i := 1;
    for k := 0 to n - 1
        invariant 1 <= i <= 2 * n - 1
        invariant sum == ((k * (k + 1) * (2 * k + 1) * (3 * k * k + 3 * k - 1)) / 3)
        invariant i == 1 + 2 * k
    {
        sum := sum + i * i * i * i;
        i := i + 2;
    }
}