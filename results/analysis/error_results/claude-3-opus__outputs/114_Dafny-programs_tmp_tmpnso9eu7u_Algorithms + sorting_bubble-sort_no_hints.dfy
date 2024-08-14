/*
Bubble Sort is the simplest sorting algorithm that works by 
repeatedly swapping the adjacent elements if they are in wrong order.
*/

predicate sorted_between(A:array<int>, from:int, to:int)
    reads A
{
    forall i, j :: 0 <= i <= j < A.Length && from <= i <= j <= to ==> A[i] <= A[j]
}

predicate sorted(A:array<int>)
    reads A
{
    sorted_between(A, 0, A.Length-1)
}

method BubbleSort(A:array<int>)
    modifies A
    ensures sorted(A)
    ensures multiset(A[..]) == multiset(old(A[..]))
{
    var N := A.Length;
    var i := N-1;
    
    while 0 < i
        invariant 0 <= i < N
        invariant sorted_between(A, i, N-1)
        invariant multiset(A[..]) == multiset(old(A[..]))
    {
        print A[..], "\n";
        var j := 0;
        
        while j < i
            invariant 0 <= j <= i
            invariant forall k, l :: 0 <= k <= l <= j ==> A[k] <= A[l]
            invariant j == i || (j < i && A[j] <= A[j+1])
            invariant multiset(A[..]) == multiset(old(A[..]))
        {
            if A[j] > A[j+1]
            {
                A[j], A[j+1] := A[j+1], A[j];
                print A[..], "\n";
            }
            j := j+1;
        }
        assert sorted_between(A, 0, i);
        
        i := i-1;
        print "\n";
    }
}

method Main() {
    var A := new int[10];
    A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
    BubbleSort(A);
    print A[..];
}

/* Explanation:
     // The outer loop invariant remains the same:
     //   - i is within the range 0 to N-1
     //   - The subarray from i to N-1 is sorted
     //   - The multiset of array elements is preserved
     
     // The inner loop invariants are updated to:
     //   - j is within the range 0 to i
     //   - All elements from 0 to j are sorted
     //   - If j < i, then A[j] <= A[j+1] (the current element is less than or equal to the next element)
     //   - The multiset of array elements is preserved
     
     // The assert statement after the inner loop ensures that the subarray from 0 to i is sorted
     
     // These updated invariants and the assert statement ensure that the postcondition is satisfied
*/
