
method SumOfFourthPowerOfOddNumbers(n: int) returns (sum: int)
    requires n > 0
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n  - 14 * n + 7) / 15
{
    var i := 1;
    var k := 0;
    sum := 0;

    for k := 0 to n
    {
        sum := sum + i * i * i * i;
        i := i + 2;
    }

    // postcondition: the sum of the first n odd numbers raised to the fourth power is returned
    ensures sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n  - 14 * n + 7) / 15;
}
