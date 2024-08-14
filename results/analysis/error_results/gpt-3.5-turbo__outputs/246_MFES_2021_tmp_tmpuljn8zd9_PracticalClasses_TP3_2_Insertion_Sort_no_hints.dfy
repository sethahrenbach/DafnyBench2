// Sorts array 'a' using the insertion sort algorithm.
method insertionSort(a: array<int>) 
    modifies a
    ensures isSorted(a, 0, a.Length)
    ensures multiset(a[..]) == multiset(old(a[..]))
{
    var i := 1;
    while i < a.Length 
      invariant 1 <= i <= a.Length
      invariant forall k :: 1 <= k < i ==> isSorted(a, 0, k+1)
      invariant multiset(a[..i]) == multiset(old(a[..i]))
    {
        var j := i;
        while j > 0 && a[j-1] > a[j] 
          invariant 0 <= j < i
          invariant a[j-1] <= a[j]
          invariant forall k :: j <= k < i ==> a[k] <= a[k+1]
        {
            a[j-1], a[j] := a[j], a[j-1];
            j := j - 1;
        }
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
}