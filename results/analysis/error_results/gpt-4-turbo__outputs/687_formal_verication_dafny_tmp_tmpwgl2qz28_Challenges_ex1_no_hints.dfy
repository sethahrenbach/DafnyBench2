method PalVerify(a: array<char>) returns (yn: bool)
  ensures yn == true ==> forall i :: 0 <= i < a.Length/2 ==> a[i] == a[a.Length - i -1]
  ensures yn == false ==> exists i :: 0 <= i < a.Length/2 && a[i] != a[a.Length - i -1]
  ensures forall j :: 0<=j<a.Length ==> a[j] == old(a[j]) 
{
   var i:int := 0;
   while i < a.Length/2
     invariant 0 <= i <= a.Length/2
     invariant forall k :: 0 <= k < i ==> a[k] == a[a.Length - k - 1]
   {                                      
      if a[i] != a[a.Length-i-1]          
      {                                   
         return false;                    
      }                                   
      i := i+1;                           
   }                                      
   return true;                           
}     

method TEST()
{
   var a:array<char> := new char[]['r','e','f','e','r'];
   var r:bool := PalVerify(a);
   assert r; // true expected, simplified assertion

   var b:array<char> := new char[]['z'];
   r := PalVerify(b);
   assert r; // true expected, simplified assertion

   var c:array<char> := new char[][];
   r := PalVerify(c);
   assert r; // true expected, simplified assertion

   var d:array<char> := new char[]['x', 'y'];
   r := PalVerify(d);
   assert !r; // false expected, simplified assertion

   var e:array<char> := new char[]['1', '2', '3', '4', '2', '1'];
   r := PalVerify(e);
   assert !r; // false expected, simplified assertion, corrected to match non-palindrome condition
}