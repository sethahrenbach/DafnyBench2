method longest_increasing_subsequence(nums: array<int>) returns (max: int)
    requires 1 <= nums.Length <= 2500
    requires forall i :: 0 <= i < nums.Length ==> -10000 <= nums[i] <= 10000
    ensures max == (var lis := new int[nums.Length]; 
                    forall i :: 0 <= i < nums.Length ==> 
                        (var len := 1; 
                         forall j :: 0 <= j < i ==> 
                             if nums[j] < nums[i] then len := find_max(len, lis[j] + 1); 
                         lis[i] == len); 
                    var result := 1; 
                    forall k :: 0 <= k < nums.Length ==> result := find_max(result, lis[k]); 
                    result)
{
    var length := nums.Length;
    if (length == 1)
    {
        return 1;
    }

    max := 1;
    var dp := new int[length](i => 1);

    var i := 1;
    while (i < length)
        modifies dp
        invariant 1 <= i <= length
        invariant forall k :: 0 <= k < i ==> 1 <= dp[k] <= i
        invariant max == (var result := 1; forall m :: 0 <= m < i ==> result := find_max(result, dp[m]); result)
    {
        var j := 0;
        while (j < i)
            invariant 0 <= j <= i
            invariant forall k :: 0 <= k < j ==> if nums[k] < nums[i] then dp[i] >= dp[k] + 1 else true
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