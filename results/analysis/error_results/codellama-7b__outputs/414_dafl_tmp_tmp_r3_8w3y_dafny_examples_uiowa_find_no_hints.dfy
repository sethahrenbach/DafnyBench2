
method Find(a: array<int>, key: int) returns (i: int)
   requires a != null;
   ensures 0 <= i ==> (// (1) i is smaller than the length of a
                       i < a.Length && 
                       // (2) key is at position i in a
                       a[i] == key && 
                       // (3) i is the smallest position where key appears
                       forall k :: 0 <= k < i ==> a[k] != key
                      );
   ensures i < 0 ==> 
           // a does not contain key
           forall k :: 0 <= k < a.Length ==> a[k] != key;
{
   i := 0;
   while (i < a.Length)
     // key is at none of the positions seen so far
     invariant 0 <= i ==> a[i] != key;
     // i is smaller than the length of a
     invariant i < a.Length;
     // i is the smallest position where key appears
     invariant forall k :: 0 <= k < i ==> a[k] != key;
     // a does not contain key
     invariant forall k :: 0 <= k < a.Length ==> a[k] != key;
     // key is at none of the positions seen so far
     assert a[i] != key;
     i := i + 1;
   }
}
