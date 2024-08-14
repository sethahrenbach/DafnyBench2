
method longest_increasing_subsequence(nums: array<int>) returns (max: int)
    requires 1 <= nums.Length <= 2500
    requires forall i :: 0 <= i < nums.Length ==> -10000 <= nums[i] <= 10000
    ensures max >= 1
    ensures exists seq :: increasing_subsequence(nums, seq) && seq.Length == max
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
        invariant forall k :: 0 <= k < i ==> dp[k] >= 1
        invariant forall k :: 0 <= k < i ==> exists seq :: increasing_subsequence(nums[..i], seq) && seq.Length == dp[k]
        modifies dp
    {
        var j := 0;
        while (j < i)
            invariant 0 <= j <= i
            invariant forall k :: 0 <= k < j ==> dp[k] >= 1
            invariant forall k :: 0 <= k < j ==> exists seq :: increasing_subsequence(nums[..j], seq) && seq.Length == dp[k]
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

function find_max(x: int, y: int): int
{
    if x > y then x
    else y
}

function increasing_subsequence(nums: array<int>, seq: array<int>): bool
    requires seq != null
    requires seq.Length <= nums.Length
    requires seq.Length > 0 ==> seq[0] == nums[0]
    requires forall i :: 0 <= i < seq.Length - 1 ==> seq[i] < seq[i + 1]
    requires forall i :: 0 <= i < seq.Length ==> exists j :: 0 <= j < nums.Length && nums[j] == seq[i]
{
    forall i :: 0 <= i < seq.Length - 1 ==> nums[..].IndexOf(seq[i]) < nums[..].IndexOf(seq[i + 1])
}
