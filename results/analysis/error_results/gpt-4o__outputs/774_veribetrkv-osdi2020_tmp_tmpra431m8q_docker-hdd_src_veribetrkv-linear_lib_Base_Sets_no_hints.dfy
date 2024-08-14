module Sets {

  lemma {:opaque} ProperSubsetImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
  {
    assert a <= b;
    assert a != b;
    SetInclusionImpliesSmallerCardinality(a, b);
    assert |a| <= |b|;
    if |a| == |b| {
      assert false;
    }
  }

  lemma {:opaque} SetInclusionImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a <= b
    ensures |a| <= |b|
  {
    if a == b {
      assert |a| == |b|;
    } else {
      ProperSubsetImpliesSmallerCardinality(a, b);
      assert |a| < |b|;
    }
  }

  lemma {:opaque} SetInclusionImpliesStrictlySmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
  {
    ProperSubsetImpliesSmallerCardinality(a, b);
  }

  lemma {:opaque} SetInclusionAndEqualCardinalityImpliesSetEquality<T>(a: set<T>, b: set<T>)
    requires a <= b
    requires |a| == |b|
    ensures a == b
  {
    if a != b {
      assert a < b;
      ProperSubsetImpliesSmallerCardinality(a, b);
      assert |a| < |b|;
      assert false;
    }
  }

  function SetRange(n: int) : set<int>
  {
    set i | 0 <= i < n
  }

  lemma CardinalitySetRange(n: int)
  requires n >= 0
  ensures |SetRange(n)| == n
  {
    if n == 0 {
      assert SetRange(n) == {};
      assert |SetRange(n)| == 0;
    } else {
      CardinalitySetRange(n-1);
      assert SetRange(n) == SetRange(n-1) + {n-1};
      assert |SetRange(n)| == |SetRange(n-1)| + 1;
      assert |SetRange(n-1)| == n-1 by CardinalitySetRange(n-1);
      assert |SetRange(n)| == n;
    }
  }
}