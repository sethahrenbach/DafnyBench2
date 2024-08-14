method contains_duplicate(nums: seq<int>) returns (result: bool)
    requires 1 <= |nums| <= 100000
    requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
    ensures result <==> distinct(nums)
{  
    var i := 0;
    var s: set<int> := {};
    while (i < |nums|)
        invariant 0 <= i <= |nums|
        invariant s == set nums[..i]
        invariant forall j, k :: 0 <= j < k < i ==> nums[j] != nums[k]
    {
        var num := nums[i];
        if (num in s)
        {
            assert !distinct(nums[..i+1]);
            return false;
        }

        s := s + {num};
        i := i + 1;
    }

    assert distinct(nums);
    return true;
}

predicate distinct(nums: seq<int>) {
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}