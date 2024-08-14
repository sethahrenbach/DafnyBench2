
method FindPivotIndex(nums: seq<int>) returns (index: int)
    requires |nums| > 0
    ensures index == -1 ==> forall k: nat | 0 <= k < |nums| ==> sumUp(nums[(|nums|-k)..]) == sum(nums[(|nums|-k)..])
    ensures 0 <= index < |nums| ==> sum(nums[0..index]) == sum(nums[(index+1)..])
{
    var leftsums: seq<int> := [0];
    var rightsums: seq<int> := [0];
    var i := 1;
    while i < |nums|+1
    {
        leftsums := leftsums + [leftsums[i-1]+nums[i-1]]; 
        rightsums := rightsums + [nums[|nums|-i]+rightsums[i-1]];
        i := i + 1;
    }

    i :=0;
    while i < |nums| 
    {
        var x := |nums|-(i+1);
        if leftsums[i] == rightsums[x] {
            return i;
        }
        i := i + 1;
    }
    return -1;
}
