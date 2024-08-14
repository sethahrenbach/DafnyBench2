method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
    var sumCubes := 0;
    var sumNumbers := 0;
    for i := 1 to n + 1
        invariant 1 <= i <= n + 1
        invariant sumCubes == (i - 1) * i * (i - 1) * (i - 1) / 4
        invariant sumNumbers == (i - 1) * i / 2
    {
        sumCubes := sumCubes + i * i * i;
        sumNumbers := sumNumbers + i;
    }
    assert sumCubes == (n * (n + 1) / 2) * (n * (n + 1) / 2); // sum of cubes formula
    assert sumNumbers == n * (n + 1) / 2;
    diff := sumCubes - sumNumbers;
    assert diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2;
}