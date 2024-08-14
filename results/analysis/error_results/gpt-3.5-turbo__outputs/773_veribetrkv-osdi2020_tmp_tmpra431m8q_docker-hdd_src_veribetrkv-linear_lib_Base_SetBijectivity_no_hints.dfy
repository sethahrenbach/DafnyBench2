module SetBijectivity {
  lemma BijectivityImpliesEqualCardinality<A, B>(setA: set<A>, setB: set<B>, relation: iset<(A, B)>)
    requires forall a :: a in setA ==> exists b :: b in setB && (a, b) in relation
    requires forall a1, a2, b :: a1 in setA && a2 in setA && b in setB && (a1, b) in relation && (a2, b) in relation ==> a1 == a2
    requires forall b :: b in setB ==> exists a :: a in setA && (a, b) in relation
    requires forall a, b1, b2 :: b1 in setB && b2 in setB && a in setA && (a, b1) in relation && (a, b2) in relation ==> b1 == b2
    ensures |setA| == |setB|
  {
    if |setA| == 0 {
    } else {
      var a :| a in setA;
      var b :| b in setB && (a, b) in relation;
      var setA' := setA - {a};
      var setB' := setB - {b};
      BijectivityImpliesEqualCardinality(setA', setB', relation);
    }
  }

  lemma CrossProductCardinality<A, B>(setA: set<A>, setB: set<B>, cp: set<(A,B)>)
    requires cp == (set a, b | a in setA && b in setB :: (a,b))
    ensures |cp| == |setA| * |setB|;
  {
    if |setA| == 0 {
    } else {
      var x :| x in setA;
      var setA' := setA - {x};
      var cp' := (set a, b | a in setA' && b in setB :: (a,b));
      var line := (set a, b | a == x && b in setB :: (a,b));

      var relation := iset p : (A, B) | p in cp';
      forall b | b in setB
        ensures exists p :: p in line && (p, b) in relation
      {
        var p := (x, b);
        assert (p, b) in relation;
      }
      BijectivityImpliesEqualCardinality(setA', setB, relation);

      CrossProductCardinality(setA', setB, cp');
      assert |cp' + line| == |cp'| + |line|;
      assert |cp'| + |line| == (|setA| - 1) * |setB| + |setB|;
      assert (|setA| - 1) * |setB| + |setB| == |setA| * |setB|;
    }
  }
}