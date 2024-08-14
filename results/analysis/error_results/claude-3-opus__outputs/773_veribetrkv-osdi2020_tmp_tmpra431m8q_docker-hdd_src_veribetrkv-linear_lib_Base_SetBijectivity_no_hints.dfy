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
      
      forall a' | a' in setA'
      ensures exists b' :: b' in setB' && (a', b') in relation
      {
        var b' :| b' in setB && (a', b') in relation; // Follows from the first precondition
        assert b' != b; // Follows from the second precondition
        assert b' in setB'; // Follows from the definition of setB'
      }
      
      forall a1', a2', b' | a1' in setA' && a2' in setA' && b' in setB' && (a1', b') in relation && (a2', b') in relation
      ensures a1' == a2'
      {
        assert a1' == a2'; // Follows from the second precondition
      }
      
      forall b' | b' in setB' 
      ensures exists a' :: a' in setA' && (a', b') in relation
      {
        var a' :| a' in setA && (a', b') in relation; // Follows from the third precondition
        assert a' != a; // Follows from the fourth precondition
        assert a' in setA'; // Follows from the definition of setA'
      }
      
      forall a', b1', b2' | b1' in setB' && b2' in setB' && a' in setA' && (a', b1') in relation && (a', b2') in relation
      ensures b1' == b2'
      {
        assert b1' == b2'; // Follows from the fourth precondition
      }
      
      BijectivityImpliesEqualCardinality(setA', setB', relation);
      assert |setA'| == |setB'|; // Follows from the postcondition of the recursive call
      assert |setA| == |setA'| + 1; // Follows from the definition of setA'
      assert |setB| == |setB'| + 1; // Follows from the definition of setB'
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

      assert cp == cp' + line; // Follows from the definition of cp, cp', and line
      assert forall p :: p in cp' ==> p.0 in setA' && p.1 in setB; // Follows from the definition of cp'
      assert forall p :: p in line ==> p.0 == x && p.1 in setB; // Follows from the definition of line
      assert forall p1, p2 :: p1 in cp' && p2 in line ==> p1 != p2; // Follows from the definitions of cp' and line

      var relation := iset p : ((A, B), B) | p.0.1 == p.1;
      forall b | b in setB
      ensures exists p :: p in line && (p, b) in relation
      {
        var p := (x, b);
        assert p in line; // Follows from the definition of line
        assert (p, b) in relation; // Follows from the definition of relation
      }
      BijectivityImpliesEqualCardinality(line, setB, relation);
      assert |line| == |setB|; // Follows from the postcondition of BijectivityImpliesEqualCardinality

      CrossProductCardinality(setA', setB, cp');
      assert |cp'| == |setA'| * |setB|; // Follows from the postcondition of the recursive call
      calc == {
        |cp|;
        |cp' + line|;
        |cp'| + |line|;
        |setA'| * |setB| + |line|;
        |setA'| * |setB| + |setB|;
        (|setA| - 1) * |setB| + |setB|;
        |setA| * |setB| - |setB| + |setB|;
        |setA| * |setB|;
      }
    }
  }
}