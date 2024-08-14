
module Sets
{
  lemma ProperSubsetImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
    loop invariant |a| <= |b|
    loop assigns |a|, |b|
  {
    if |a| < |b| {
      assert |a| < |b|;
    } else {
      assert |a| == |b|;
    }
  }

  lemma SetInclusionImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a <= b
    ensures |a| <= |b|
    loop invariant |a| <= |b|
    loop assigns |a|, |b|
  {
    if |a| < |b| {
      assert |a| < |b|;
    } else {
      assert |a| == |b|;
    }
  }

  lemma SetInclusionImpliesStrictlySmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
    loop invariant |a| < |b|
    loop assigns |a|, |b|
  {
    if |a| < |b| {
      assert |a| < |b|;
    } else {
      assert |a| == |b|;
    }
  }

  lemma SetInclusionAndEqualCardinalityImpliesSetEquality<T>(a: set<T>, b: set<T>)
    requires a <= b
    requires |a| == |b|
    ensures a == b
    loop invariant |a| == |b|
    loop assigns |a|, |b|
  {
    if |a| < |b| {
      assert |a| < |b|;
    } else {
      assert |a| == |b|;
    }
  }

  function SetRange(n: int) : set<int>
  {
    set i | 0 <= i < n
    loop invariant |i| <= n
    loop assigns |i|, |n|
  {
    if |i| < |n| {
      assert |i| < |n|;
    } else {
      assert |i| == |n|;
    }
  }

  lemma CardinalitySetRange(n: int)
  requires n >= 0
  ensures |SetRange(n)| == n
  {
    if n == 0 {
    } else {
      CardinalitySetRange(n-1);
          == SetRange(n-1) + {n-1};
    }
  }
}
