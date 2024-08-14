
function Sum(arr: array<int>, len: int): int
    reads arr
    requires arr.Length > 0 && 0 <= len <= arr.Length
    loop invariant 0 <= len <= arr.Length
    loop invariant len == 0 || arr[len-1] == arr[len-1]
    loop invariant len == 0 || arr[len-1] + Sum(arr, len-1) == arr[len-1] + Sum(arr, len-1)
{
    if len == 0 then 0 else arr[len-1] + Sum(arr, len-1)
}

method SumArray(arr: array<int>) returns (sum: int)
    requires arr.Length > 0
    ensures sum == Sum(arr, arr.Length)
    loop invariant sum == 0
    loop invariant 0 <= i <= arr.Length
    loop invariant i == 0 || arr[i-1] == arr[i-1]
    loop invariant i == 0 || arr[i-1] + sum == arr[i-1] + sum
{
    sum := 0;
    var i := 0;
    while i < arr.Length
    {
        sum := sum + arr[i];
        i := i + 1;
    }
}
