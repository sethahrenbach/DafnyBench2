method longest_increasing_subsequence(nums: array<int>) returns (max: int)
    requires 1 <= nums.Length <= 2500
    requires forall i :: 0 <= i < nums.Length ==> -10000 <= nums[i] <= 10000
    ensures max == get_lis_length(nums, nums.Length)
{
    var length := nums.Length;
    if (length == 1)
    {
        return 1;
    }

    max := 1;
    var dp := new int[length](_ => 1);

    var i := 1;
    while (i < length)
        invariant 1 <= i <= length
        invariant forall j :: 0 <= j < i ==> dp[j] == get_lis_length(nums[..j+1], j+1)
        invariant max == get_max(dp[..i])
        modifies dp
    {
        var j := 0;
        while (j < i)
            invariant 0 <= j <= i
            invariant forall k :: 0 <= k < j ==> dp[k] == get_lis_length(nums[..k+1], k+1)
            invariant dp[i] == get_lis_length_prev(nums, i+1, j)
        {
            if (nums[j] < nums[i])
            {
                dp[i] := find_max(dp[i], dp[j] + 1);
            }

            j := j + 1;
        }
        assert dp[i] == get_lis_length(nums[..i+1], i+1);

        max := find_max(max, dp[i]);
        i := i + 1;
    }
    assert max == get_max(dp[..length]);
}


// Functions
function find_max(x: int, y: int): int
{
    if x > y then x
    else y
}

function get_lis_length(nums: array<int>, n: int): int
    requires 1 <= n <= nums.Length
{
    if n == 1 then 1
    else find_max(get_lis_length(nums[..n-1], n-1), get_lis_length(nums[..n-1], n-1) + (if nums[n-2] < nums[n-1] then 1 else 0))
}

function get_lis_length_prev(nums: array<int>, n: int, prev: int): int
    requires 1 <= n <= nums.Length
    requires 0 <= prev < n
{
    if prev == 0 then 1
    else find_max(get_lis_length_prev(nums, n, prev-1), get_lis_length(nums[..prev], prev) + (if nums[prev-1] < nums[n-1] then 1 else 0))
}

function get_max(arr: array<int>): int
    requires arr.Length > 0
{
    if arr.Length == 1 then arr[0]
    else find_max(arr[0], get_max(arr[1..]))
}