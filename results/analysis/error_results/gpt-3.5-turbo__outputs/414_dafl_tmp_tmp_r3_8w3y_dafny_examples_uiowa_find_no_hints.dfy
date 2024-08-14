
/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2017
   The University of Iowa
   
   Instructor: Cesare Tinelli

   Credits: Example adapted from Dafny tutorial
*/

method Find(a: array<int>, key: int) returns (i: int)
   requires a != null;
   ensures 0 <= i ==> (
                       i < a.Length && 
                       a[i] == key && 
                       forall k :: 0 <= k < i ==> a[k] != key
                      );
   ensures i < 0 ==> 
           forall k :: 0 <= k < a.Length ==> a[k] != key;
{
   var j := 0;
   while (j < a.Length)
     invariant 0 <= j <= a.Length &&
               forall k :: 0 <= k < j ==> a[k] != key;
     decreases a.Length - j;
   {
      assert 0 <= j < a.Length;
      assert forall k :: 0 <= k < j ==> a[k] != key;
      
      if (a[j] == key) { return j; }
      j := j + 1;
   }
   return -1;
}
