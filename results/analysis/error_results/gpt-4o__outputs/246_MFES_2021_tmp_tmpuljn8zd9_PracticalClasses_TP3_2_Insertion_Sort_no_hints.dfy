// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>) 
    modifies a
    ensures isSorted(a, 0, a.Length)
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    var i := 0;
    while i < a.Length 
        invariant 0 <= i <= a.Length
        invariant isSorted(a, 0, i)
        invariant multiset(a[..i]) == multiset(old(a[..i]))
    {
        var j := i;
        while j > 0 && a[j-1] > a[j] 
            invariant 0 <= j <= i
            invariant 1 <= j <= a.Length
            invariant isSorted(a, 0, j) && isSorted(a, j, i+1)
            invariant multiset(a[..i+1]) == multiset(old(a[..i+1]))
        {
            a[j-1], a[j] := a[j], a[j-1];
            assert multiset(a[..i+1]) == multiset(old(a[..i+1]));
            j := j - 1;
        }
        assert isSorted(a, 0, i+1);
        i := i + 1;
    }
    assert isSorted(a, 0, a.Length);
    assert multiset(a[..]) == multiset(old(a[..]));
}

// Checks if array 'a' is sorted.
predicate isSorted(a: array<int>, from: nat, to: nat)
  reads a
  requires 0 <= from <= to <= a.Length
{
    forall i, j :: from <= i < j < to ==> a[i] <= a[j]
}

// Simple test case to check the postcondition
method testInsertionSort() {
  var a := new int[] [ 9, 4, 3, 6, 8];
  insertionSort(a);
}