method longest_increasing_subsequence(nums: array<int>) returns (max: int)
    requires 1 <= nums.Length <= 2500
    requires forall i :: 0 <= i < nums.Length ==> -10000 <= nums[i] <= 10000
    ensures max >= 1
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
        modifies dp
        invariant 1 <= i <= length
        invariant forall k :: 0 <= k < i ==> dp[k] >= 1
        invariant forall k :: 0 <= k < i ==> dp[k] <= i
        invariant max >= 1 && max <= max_in_dp(i, dp)
    {
        var j := 0;
        while (j < i)
            invariant 0 <= j <= i
            invariant forall l :: 0 <= l < j ==> (nums[l] < nums[i] ==> dp[i] >= dp[l] + 1)
            invariant dp[i] >= 1
        {
            if (nums[j] < nums[i])
            {
                dp[i] := find_max(dp[i], dp[j] + 1);
            }
            j := j + 1;
        }

        max := find_max(max, dp[i]);
        i := i + 1;
    }
}

// Function
function find_max(x: int, y: int): int
{
    if x > y then x
    else y
}

// Helper function to find the maximum in dp array up to index i
function max_in_dp(i: int, dp: array<int>): int
    requires 0 <= i <= dp.Length
    requires dp.Length > 0
    reads dp
    decreases i
{
    var m := 1;
    for k in 0..i {
        m := find_max(m, dp[k]);
    }
    m
}