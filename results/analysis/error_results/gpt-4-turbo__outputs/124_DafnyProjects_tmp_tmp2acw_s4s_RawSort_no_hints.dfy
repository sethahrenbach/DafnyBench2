
/**
 * Proves the correctness of a "raw" array sorting algorithm that swaps elements out of order, chosen randomly.
 * FEUP, MFES, 2020/21.
 */

// Type of each array element; can be any type supporting comparison operators.
type T = int 

// Checks if array 'a' is sorted by non-descending order.
ghost predicate sorted(a: array<T>)
  reads a
{ forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j] }

// Obtains the set of all inversions in an array 'a', i.e., 
// the pairs of indices i, j such that i < j and a[i] > a[j]. 
ghost function inversions(a: array<T>): set<(nat, nat)>
  reads a
{ set i, j | 0 <= i < j < a.Length && a[i] > a[j] :: (i, j) }

// Sorts an array by simply swapping elements out of order, chosen randomly.
method rawsort(a: array<T>)
   modifies a
   ensures sorted(a) && multiset(a[..]) == multiset(old(a[..]))
{
   var i, j: int;
   while (inversions(a) != {})
     decreases |inversions(a)|
   {
      // Find a pair (i, j) such that i < j and a[i] > a[j]
      i, j := findSwapPair(a);
      if (i != -1 && j != -1) {
        // Perform the swap
        a[i], a[j] := a[j], a[i];
        // Assert that the number of inversions has decreased
        assert |inversions(a)| < |inversions(old(a))|;
      }
   }
}

// Helper method to find a pair (i, j) such that i < j and a[i] > a[j]
method findSwapPair(a: array<T>) returns (i: int, j: int)
  requires a != null
  ensures (i == -1 && j == -1) || (0 <= i < j < a.Length && a[i] > a[j])
{
  i, j := -1, -1;
  for k := 0 to a.Length - 2 {
    for l := k + 1 to a.Length - 1 {
      if a[k] > a[l] {
        return k, l;
      }
    }
  }
}

method testRawsort() {
   var a : array<T> := new T[3];
   a[0], a[1], a[2] := 3, 5, 1;
   rawsort(a);
   assert sorted(a);
}
