predicate IsSubset(A: set, B: set) // <=
{
	forall n :: n in A ==> n in B
}

lemma subsetIsTransitive(A: set, B: set, C: set)
    requires Pre1 : IsSubset(A, B)
    requires Pre2 : IsSubset(B, C)
    ensures IsSubset(A, C)
{
    forall x | x in A 
        ensures x in C
    {
        assert x in B by {
            assert forall n :: n in A ==> n in B;
            assert x in A;
        };
        assert x in C by {
            assert forall n :: n in B ==> n in C;
            assert x in B;
        };
    }
}