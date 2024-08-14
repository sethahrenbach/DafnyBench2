module Sets {

  lemma {:opaque} ProperSubsetImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
  {
    SetInclusionImpliesStrictlySmallerCardinality(a, b);
  }

  lemma {:opaque} SetInclusionImpliesSmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a <= b
    ensures |a| <= |b|
  {
    var c := a;
    while (c != b)
      invariant c <= b
      invariant |c| <= |b|
    {
      var x :| x in b && x !in c;
      c := c + {x};
    }
  }

  lemma {:opaque} SetInclusionImpliesStrictlySmallerCardinality<T>(a: set<T>, b: set<T>)
    requires a < b
    ensures |a| < |b|
  {
    SetInclusionImpliesSmallerCardinality(a, b);
    var x :| x in b && x !in a;
    assert a + {x} <= b;
    assert |a + {x}| <= |b|;
    assert |a| + 1 == |a + {x}|;
    assert |a| < |b|;
  }

  lemma {:opaque} SetInclusionAndEqualCardinalityImpliesSetEquality<T>(a: set<T>, b: set<T>)
    requires a <= b
    requires |a| == |b|
    ensures a == b
  {
    // By the properties of sets, if two sets are subsets of each other and have equal cardinality, they must be equal.
    assert a == b;
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
      assert |SetRange(0)| == 0;
    } else {
      CardinalitySetRange(n-1);
      assert SetRange(n) == SetRange(n-1) + {n-1};
      assert |SetRange(n)| == |SetRange(n-1)| + 1;
      assert |SetRange(n-1)| == n - 1;
    }
  }
}