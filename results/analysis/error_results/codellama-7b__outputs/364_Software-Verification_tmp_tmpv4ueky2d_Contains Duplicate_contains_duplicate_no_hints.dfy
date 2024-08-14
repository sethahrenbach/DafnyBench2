
method contains_duplicate(nums: seq<int>) returns (result: bool)
    requires 1 <= |nums| <= 100000
    requires forall i :: 0 <= i < |nums| ==> -1000000000 <= nums[i] <= 1000000000
    ensures result <==> distinct(nums)
{
    var i := 0;
    var s: set<int> := {};
    while (i < |nums|)
    {
        var num := nums[i];
        // Loop invariant: s contains all the elements of nums[0..i]
        // and nums[i] is not in s
        assert distinct(nums[0..i]) by {
            assert num not in s;
        };

        s := s + {num};
        i := i + 1;
    }

    // Postcondition: s contains all the elements of nums
    assert distinct(nums) by {
        assert nums[i] in s;
    };

    return true;
}

predicate distinct(nums: seq<int>) {
    forall i, j :: 0 <= i < j < |nums| ==> nums[i] != nums[j]
}
