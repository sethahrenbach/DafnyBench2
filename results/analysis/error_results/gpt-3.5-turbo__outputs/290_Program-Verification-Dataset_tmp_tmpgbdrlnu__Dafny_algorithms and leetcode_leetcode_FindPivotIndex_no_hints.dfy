TypeScript
function sum(nums: seq<int>): int
    requires |nums| >= 0
{
    if |nums| == 0 then 0 else sum(nums[0..(|nums|-1)]) + nums[|nums-1]
}

function sumUp(nums: seq<int>): int
    requires |nums| >= 0
{
    if |nums| == 0 then 0 else nums[0] + sumUp(nums[1..])
}

lemma sumUpLemma(a: seq<int>, b: seq<int>)
    requires |a| > 0
    ensures sumUp(a + b) == sumUp(a) + sumUp(b)
{
    if a == [] {
    } else {
        sumUpLemma(a[1..], b);
        calc {
            sumUp(a + b);
            a[0] + sumUp(a[1..] + b);
            a[0] + sumUp(a[1..]) + sumUp(b);
        }
    }
}

lemma sumsEqual(nums: seq<int>)
    requires |nums| >= 0
    ensures sum(nums) == sumUp(nums)
{
    if nums == [] {
    } else {
        var ln := |nums| - 1;
        calc {
            sumUp(nums[..]);
            sumUpLemma(nums[0..ln], [nums[ln]]);
            sumUp(nums[0..ln]) + sumUp([nums[ln]]);
            sumUp(nums[0..ln]) + nums[ln];
            sumsEqual(nums[0..ln]);
            sum(nums[0..ln]) + nums[ln];
        }
    }
}

method FindPivotIndex(nums: seq<int>) returns (index: int)
    requires |nums| != null && |nums| > 0
    ensures index == -1 ==> forall k: nat :: k < |nums| ==> sum(nums[0..k]) != sum(nums[(k+1)..])
    ensures 0 <= index < |nums| ==> sum(nums[0..index]) == sum(nums[(index+1)..])
{
    var leftsums: seq<int> := [0];
    var rightsums: seq<int> := [0];
    var i := 1;
    while i < |nums| + 1
        invariant 1 <= i <= |nums| + 1
        invariant |leftsums| == i
        invariant |rightsums| == i
        invariant forall j: int | 0 <= j < i :: leftsums[j] == sum(nums[0..j])
        invariant forall j: int | 0 <= j < i :: rightsums[j] == sumUp(nums[(|nums| - j)..])
    {
        leftsums := leftsums + [leftsums[i - 1] + nums[i - 1]]; 
        rightsums := rightsums + [nums[|nums| - i] + rightsums[i - 1]];
        i := i + 1;
    }

    i := 0;
    while i < |nums|
        invariant 0 <= i <= |nums|
        invariant forall j: int | 0 <= j < i :: leftsums[j] == sum(nums[0..j])
        invariant forall j: int | 0 <= j < |nums| - i :: rightsums[j] == sumUp(nums[(|nums| - j)..])
    {
        var x := |nums| - (i + 1);
        if leftsums[i] == rightsums[x] {
            assert rightsums[i + 1] == sum(nums[(|nums| - (i + 1))..]);
            return i;
        }
        i := i + 1;
    }
    return -1;
}
