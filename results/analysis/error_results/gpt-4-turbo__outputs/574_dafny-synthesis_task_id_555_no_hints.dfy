method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
    var sumCubes := 0;
    var sumNumbers := 0;
    for i := 0 to n
        invariant 0 <= i <= n
        invariant sumCubes == (i * (i + 1) * (2 * i + 1)) / 6
        invariant sumNumbers == (i * (i + 1)) / 2
    {
        sumCubes := sumCubes + i * i * i;
        sumNumbers := sumNumbers + i;
    }
    diff := sumCubes - sumNumbers;
}