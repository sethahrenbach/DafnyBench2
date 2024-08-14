// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>) 
    modifies a
    ensures isSorted(a, 0, a.Length)
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    var i := 1;
    while i < a.Length
        invariant 1 <= i <= a.Length
        invariant isSorted(a, 0, i)
        invariant multiset(a[..]) == multiset(old(a[..]))
    {
        var j := i;
        var temp := a[j];
        ghost var left := a[..j];
        ghost var right := a[j..i];
        assert isSorted(a, 0, j) && isSorted(a, j, i);
        assert forall k :: j <= k < i ==> a[k] >= temp;
        while j > 0 && a[j-1] > temp
            invariant 0 <= j <= i
            invariant forall k :: j <= k < i ==> a[k] >= temp
            invariant multiset(a[..j]) + multiset{temp} + multiset(right) == multiset(left) + multiset{temp}
        {
            a[j] := a[j-1];
            j := j - 1;
        }
        a[j] := temp;
        assert isSorted(a, 0, i+1);
        i := i + 1;
    }
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
  assert a[..] == [3, 4, 6, 8, 9];
}