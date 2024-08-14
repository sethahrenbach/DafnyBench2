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
   var sortedBefore := sorted(a);
   while !sortedBefore
     invariant sorted(a)
     invariant multiset(a[..]) == multiset(old(a[..]))
   {
      var swapped := false;
      var i := 0;
      while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall j :: 0 <= j < i ==> a[j] <= a[j+1]
        decreases a.Length - i
      {
         var j := i + 1;
         while j < a.Length
           invariant i < j <= a.Length
           invariant forall k :: i <= k < j ==> a[i] <= a[j]
           decreases a.Length - j
         {
            if a[i] > a[j] {
               var temp := a[i];
               var temp2 := a[j];
               a[j] := temp;
               a[i] := temp2;
               swapped := true;
            }
            j := j + 1;
         }
         i := i + 1;
      }
      sortedBefore := !swapped;
   }
}

// States and proves (by induction) the following property: given sets 'a' and 'b' and an injective
// and non-surjective mapping 'm' from elements in 'a' to elements in 'b', then |a| < |b>.
// To facilitate the proof, it is given an element 'k' in 'b' that is not an image of elements in 'a'.   
lemma mappingProp<T1, T2>(a: set<T1>, b: set<T2>, k: T2, m: map<T1, T2>)
  requires k in b
  requires forall x :: x in a ==> x in m && m[x] in b - {k} 
  requires forall x, y :: x in a && y in a && x != y ==> m[x] != m[y] 
  ensures |a| < |b|
{
   if x :| x in a {
      mappingProp(a - {x}, b - {m[x]}, k, m);
   }
}

method testRawsort() {
   var a : array<T> := new T[] [3, 5, 1]; 
   rawsort(a);
}
