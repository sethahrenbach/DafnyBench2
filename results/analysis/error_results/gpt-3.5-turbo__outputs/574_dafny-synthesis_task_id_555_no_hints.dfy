
method DifferenceSumCubesAndSumNumbers(n: int) returns (diff: int)
    requires n >= 0
    ensures diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
{
    var sumCubes := 0;
    var sumNumbers := 0;
    var i := 1;
    while i <= n + 1
        invariant 1 <= i <= n + 1
        invariant sumCubes == i * i * (i - 1) * (2 * i - 1) / 6
        invariant sumNumbers == i * (i - 1) / 2
    {
        assert sumCubes == i * i * (i - 1) * (2 * i - 1) / 6;
        assert sumNumbers == i * (i - 1) / 2;
        
        sumCubes := sumCubes + i * i * i;
        sumNumbers := sumNumbers + i;
        i := i + 1;
    }
    diff := sumCubes - sumNumbers;
}
