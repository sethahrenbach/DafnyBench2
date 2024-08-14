
method insertionSort(a: array<int>)
  modifies a
  ensures isSorted(a, 0, a.Length)
  ensures multiset(a[..]) == multiset(old(a[..]))
{
  var i := 0;
  while i < a.Length {
    var j := i;
    while j > 0 && a[j-1] > a[j] {
      a[j-1], a[j] := a[j], a[j-1];
      j := j - 1;
    }
    // Loop invariant: a[0..i] is sorted
    assert isSorted(a, 0, i);
    i := i + 1;
  }
  // Postcondition: a[0..a.Length] is sorted
  assert isSorted(a, 0, a.Length);
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