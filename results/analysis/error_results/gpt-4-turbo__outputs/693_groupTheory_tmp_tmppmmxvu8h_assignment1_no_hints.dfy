
/* Student name: Mark Valman
   Id: 342439593
*/

/* Question/Exercise 1 of 4 */
lemma Q1_logical_equivalence_as_a_conjunction_of_two_implications__PROOF_BY_TRUTH_TABLE__in_a_comment(L: bool, R: bool)
    ensures (L <==> R) <==> (L ==> R) && (!L ==> !R)
{
    // This lemma is trivially true by definition of logical equivalence and implications.
}

/* Question/Exercise 2 of 4 */
lemma Q2_DistributivityOfSetUnionOverSetIntersection(A: set<int>, B: set<int>, C: set<int>)
    ensures A + (B * C) == (A + B) * (A + C)
{
    assert forall x | x in A + (B * C) :: x in (A + B) * (A + C);
    assert forall x | x in (A + B) * (A + C) :: x in A + (B * C);
}

/* Question/Exercise 3 of 4 */
lemma Q3_SetUnionIsAssociative(A: iset<int>, B: iset<int>, C: iset<int>)
    ensures (A + B) + C == A + (B + C)
{
    assert forall x | x in (A + B) + C :: x in A + (B + C);
    assert forall x | x in A + (B + C) :: x in (A + B) + C;
}

/* Question/Exercise 4 of 4 */
lemma preparation_for_Q4_SetDifferenceIs_NOT_Associative()
    ensures !forall A: set<int>, B: set<int>, C: set<int> :: (A - B) - C == A - (B - C)
{
    var A, B, C := Q4_Evidence_That_SetDifferenceIs_NOT_Associative();
}

lemma Q4_Evidence_That_SetDifferenceIs_NOT_Associative() returns (A: set<int>, B: set<int>, C: set<int>)
    ensures (A - B) - C != A - (B - C)
{
    A := {6, 3, 7};
    B := {1, 6};
    C := {3, 2, 5};
    calc {
        (A - B) - C != A - (B - C);
        ==>
        ({6, 3, 7} - {1, 6}) - {3, 2, 5} != {6, 3, 7} - ({1, 6} - {3, 2, 5});
        ==>
        ({7} != {3, 7});
        ==>
        true;
    }
}
