module Sets {

  lemma {:opaque} ProperSubsetImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
  {
    assert a <= b; // a is a proper subset of b
    SetInclusionImpliesStrictlySmallerCardinality(a, b);
  }

  lemma {:opaque} SetInclusionImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a <= b
    ensures |a| <= |b|
  {
    // Induction on |b| - |a|
    if a == b {
      // |a| == |b|, so |a| <= |b|
    } else {
      // a is a proper subset of b
      var x :| x in b && x !in a;
      assert a <= b - {x};
      SetInclusionImpliesSmallerCardinality(a, b - {x});
      assert |a| <= |b - {x}|;
      assert |b - {x}| == |b| - 1;
      assert |a| <= |b| - 1;
      assert |a| <= |b|;
    }
  }

  lemma {:opaque} SetInclusionImpliesStrictlySmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
  {
    SetInclusionImpliesSmallerCardinality(a, b);
    assert a != b; // a is a proper subset of b
    assert |a| <= |b|;
    if |a| == |b| {
      SetInclusionAndEqualCardinalityImpliesSetEquality(a, b);
      assert a == b; // contradicts a < b
      assert false;
    }
  }

  lemma {:opaque} SetInclusionAndEqualCardinalityImpliesSetEquality<T>(a: set<T>, b: set<T>)
    requires a <= b
    requires |a| == |b|
    ensures a == b
  {
    // Proof by contradiction  
    if a != b {
      assert exists x :: x in b && x !in a;
      var x :| x in b && x !in a;
      assert a <= b - {x};
      SetInclusionImpliesSmallerCardinality(a, b - {x});
      assert |a| <= |b - {x}|;
      assert |b - {x}| == |b| - 1;
      assert |a| <= |b| - 1;
      assert |a| < |b|; // contradicts |a| == |b|
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
      assert SetRange(0) == {};
      assert |SetRange(0)| == |{}| == 0;
    } else {
      CardinalitySetRange(n-1);
      assert SetRange(n) == SetRange(n-1) + {n-1};
      assert |SetRange(n)| == |SetRange(n-1)| + |{n-1}|;
      assert |{n-1}| == 1;
      assert |SetRange(n-1)| == n-1;
      assert |SetRange(n)| == (n-1) + 1 == n;
    }
  }
}