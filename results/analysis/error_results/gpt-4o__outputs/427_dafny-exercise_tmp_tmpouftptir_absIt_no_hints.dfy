method AbsIt(s: array<int>) 
modifies s
ensures forall i :: 0 <= i < s.Length ==> if old(s)[i] < 0 then s[i] == -old(s)[i] else s[i] == old(s)[i]
ensures s.Length == old(s).Length
{
	var oldS := new int[s.Length];
	var i: int := 0;

	while i < s.Length
		// Invariant: 0 <= i <= s.Length
		// Invariant: forall j :: 0 <= j < i ==> oldS[j] == old(s)[j]
	{
		oldS[i] := s[i];
		i := i + 1;
	}

	i := 0;
	while i < s.Length
		// Invariant: 0 <= i <= s.Length
		// Invariant: forall j :: 0 <= j < i ==> if oldS[j] < 0 then s[j] == -oldS[j] else s[j] == oldS[j]
		// Invariant: s.Length == oldS.Length
	{
		if (s[i] < 0) {
			s[i] := -s[i];
		}
		i := i + 1;
	}

	assert forall i :: 0 <= i < s.Length ==> if oldS[i] < 0 then s[i] == -oldS[i] else s[i] == oldS[i];
}

method Tester()
{
   var a := new int[][-1,2,-3,4,-5,6,-7,8,-9];                 
   // testcase 1
   AbsIt(a);

   var b:array<int> := new int[][-42,-2,-42,-2,-42,-2];        
   // testcase 2
   AbsIt(b);

   var c:array<int> := new int[][-1];                          
   // testcase 3
   AbsIt(c);

   var d:array<int> := new int[][42];                          
   // testcase 4
   AbsIt(d);

   var e:array<int> := new int[][];                            
   // testcase 5
   AbsIt(e);
}