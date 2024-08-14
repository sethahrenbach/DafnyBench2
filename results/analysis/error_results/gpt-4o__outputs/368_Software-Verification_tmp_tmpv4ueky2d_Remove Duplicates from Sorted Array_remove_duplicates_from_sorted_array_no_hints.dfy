method remove_duplicates_from_sorted_array(nums: seq<int>) returns (result: seq<int>) 
    requires is_sorted(nums)
    requires 1 <= |nums| <= 30000
    requires forall i :: 0 <= i < |nums| ==> -100 <= nums[i] <= 100
    ensures is_sorted_and_distinct(result)
    ensures forall i :: i in nums <==> i in result
{
    var previous := nums[0];
    result := [nums[0]];

    var i := 1;
    while (i < |nums|)
        invariant 1 <= i <= |nums|
        invariant is_sorted(nums[..i])
        invariant is_sorted_and_distinct(result)
        invariant forall j :: 0 <= j < i ==> nums[j] in result || nums[j] == previous
        invariant forall j :: 0 <= j < |result| ==> result[j] in nums
        invariant previous in nums[..i]
        invariant forall j :: 0 <= j < |result| - 1 ==> result[j] < result[j + 1]
        invariant forall j :: 0 <= j < i ==> nums[j] <= previous
        invariant |result| <= i
        invariant forall j :: 0 <= j < |result| ==> nums[0] <= result[j]
        decreases |nums| - i
    {
        if (previous != nums[i])
        { 
            result := result + [nums[i]];
            previous := nums[i];
        }

        i := i + 1;
    }
}

// Helper predicate
predicate is_sorted(nums: seq<int>)
{
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] <= nums[j]
}

predicate is_sorted_and_distinct(nums: seq<int>)
{
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] < nums[j]
}