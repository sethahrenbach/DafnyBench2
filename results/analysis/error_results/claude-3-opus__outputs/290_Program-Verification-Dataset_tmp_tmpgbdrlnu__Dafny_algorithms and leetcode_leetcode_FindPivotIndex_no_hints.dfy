function sum(nums: seq<int>): int {
    if |nums| == 0 then 0 else sum(nums[0..(|nums|-1)])+nums[|nums|-1]
}

function sumUp(nums: seq<int>): int {
    if |nums| == 0 then 0 else nums[0]+sumUp(nums[1..])
}

lemma sumUpLemma(a: seq<int>, b: seq<int>)
  ensures sumUp(a + b) == sumUp(a) + sumUp(b)
{
  if a == [] {
  }
  else {
    sumUpLemma(a[1..], b);
    calc {
      sumUp(a + b);
      a[0] + sumUp(a[1..] + b);
      { assert sumUp(a[1..] + b) == sumUp(a[1..]) + sumUp(b); }
      a[0] + sumUp(a[1..]) + sumUp(b);
    }
  }
}

lemma sumsEqual(nums: seq<int>)
  ensures sum(nums) == sumUp(nums)
{
  if nums == [] {}
  else {
    var ln := |nums|-1;
    sumsEqual(nums[0..ln]);
    calc {
      sumUp(nums[..]);
      sumUp(nums[0..ln] + [nums[ln]]);
      { sumUpLemma(nums[0..ln], [nums[ln]]); }
      sumUp(nums[0..ln]) + sumUp([nums[ln]]);
      { assert sumUp([nums[ln]]) == nums[ln]; }
      sumUp(nums[0..ln]) + nums[ln];
      { assert sumUp(nums[0..ln]) == sum(nums[0..ln]); }
      sum(nums[0..ln]) + nums[ln];
      sum(nums);
    }
  }
}

method FindPivotIndex(nums: seq<int>) returns (index: int)
    requires |nums| > 0
    ensures index == -1 ==> forall k: nat :: k < |nums| ==> sum(nums[0..k]) != sum(nums[(k+1)..])
    ensures 0 <= index < |nums| ==> sum(nums[0..index]) == sum(nums[(index+1)..])
{
    var leftsums: seq<int> := [0];
    var rightsums: seq<int> := [0];
    var i := 1;
    
    while i < |nums|+1
        invariant 1 <= i <= |nums|+1
        invariant |leftsums| == i && |rightsums| == i
        invariant forall k: nat | 0 <= k < i :: leftsums[k] == sum(nums[0..k])
        invariant forall k: nat | 0 <= k < i :: rightsums[k] == sum(nums[(|nums|-k)..])
    {
        leftsums := leftsums + [sum(nums[0..i])];
        rightsums := rightsums + [sum(nums[(|nums|-i)..])];
        i := i + 1;
    }

    i := 0;
    while i < |nums| 
        invariant 0 <= i <= |nums|
        invariant forall k: nat | 0 <= k < i :: leftsums[k] != rightsums[|nums|-(k+1)]
    {
        if leftsums[i] == rightsums[|nums|-(i+1)] {
            sumsEqual(nums[0..i]);
            assert sum(nums[0..i]) == leftsums[i];
            sumsEqual(nums[(i+1)..]);
            assert sum(nums[(i+1)..]) == rightsums[|nums|-(i+1)];
            return i;
        }
        i := i + 1;
    }
    assert forall k: nat :: k < |nums| ==> leftsums[k] != rightsums[|nums|-(k+1)];
    assert forall k: nat :: k < |nums| ==> sum(nums[0..k]) == leftsums[k] && sum(nums[(k+1)..]) == rightsums[|nums|-(k+1)];
    assert forall k: nat :: k < |nums| ==> sum(nums[0..k]) != sum(nums[(k+1)..]);
    return -1;
}