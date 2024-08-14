
module SetHelpers {

    lemma interSmallest<T>(x : set<T>, y : set<T>) 
        requires x <= y 
        ensures x * y == x
    {
    }

    lemma unionCardBound(x : set<nat>, y : set<nat>, k : nat) 
        requires forall e :: e in x ==> e < k
        requires forall e :: e in y ==> e < k
        ensures  forall e :: e in x + y ==> e < k
        ensures |x + y| <= k 
    {
        natSetCardBound(x + y, k);
    }

    lemma natSetCardBound(x : set<nat>, k : nat) 
        requires forall e :: e in x ==> e < k
        ensures |x| <= k 
    {
        if k == 0 {
            assert x == {};
        } else {
            natSetCardBound(x - { k - 1}, k - 1);
        }
    }

    lemma {:induction k} successiveNatSetCardBound(x : set<nat>, k : nat) 
        requires x == set x: nat | 0 <= x < k :: x
        ensures |x| == k
    {
        if k == 0 {
            assert x == {};
        } else {
            successiveNatSetCardBound(x - {k - 1}, k - 1);
        }
    }
    
    lemma cardIsMonotonic<T>(x : set<T>, y : set<T>) 
        requires x <= y 
        ensures |x| <= |y|
    {
        if |y| == 0 {
            assert x == {};
        } else {
            var e :| e in y;
            var y' := y - { e };
            cardIsMonotonic(if e in x then x - {e} else x, y');
        }
    }

    lemma pigeonHolePrinciple<T>(x: set<T>, y : set<T>, z : set<T>)
        requires  x <= z 
        requires y <= z
        requires |x| >= 2 * |z| / 3 + 1
        requires |y| >= 2 * |z| / 3 + 1
        ensures |x * y| >= |z| / 3 + 1
    {
        // Using the properties of set union and intersection
        assert |x + y| <= |z|;
        assert |x + y| == |x| + |y| - |x * y|;
        assert |x * y| >= |x| + |y| - |z|;
        assert |x * y| >= (4 * |z| / 3 + 2) - |z|;
        assert |x * y| >= |z| / 3 + 1;
    } 
}
