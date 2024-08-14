method AbsIt(s: array<int>) 
modifies s
ensures forall i :: 0 <= i < s.Length ==> if old(s[i]) < 0 then s[i] == -old(s[i]) else s[i] == old(s[i])
ensures s.Length == old(s).Length
{
	var i: int := 0;
	
	while i < s.Length
	invariant 0 <= i <= s.Length
	invariant forall j :: 0 <= j < i ==> if old(s[j]) < 0 then s[j] == -old(s[j]) else s[j] == old(s[j])
	{	
		if (s[i] < 0) {
			s[i] := -s[i];
		}
		i := i + 1;
	}
}

method Tester()
{
   var a: array<int> := new int[9]([-1, 2, -3, 4, -5, 6, -7, 8, -9]);                 
   AbsIt(a);

   var b: array<int> := new int[6]([-42, -2, -42, -2, -42, -2]);        
   AbsIt(b);

   var c: array<int> := new int[1]([-1]);                          
   AbsIt(c);

   var d: array<int> := new int[1]([42]);                          
   AbsIt(d);

   var e: array<int> := new int[0]();                            
   AbsIt(e);
}