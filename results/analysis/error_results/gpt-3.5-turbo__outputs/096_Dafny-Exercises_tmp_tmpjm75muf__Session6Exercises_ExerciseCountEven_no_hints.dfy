predicate positive(s:seq<int>)
{forall u::0<=u<|s| ==> s[u]>=0}

predicate isEven(i:int)
requires i>=0
{i%2==0}

function CountEven(s:seq<int>):int
requires positive(s)
{if s==[] then 0
 else (if (s[|s|-1]%2==0) then 1 else 0)+CountEven(s[..|s|-1])
 }

lemma ArrayFacts<T>()
	ensures forall v : array<T>  :: v[..v.Length] == v[..];
	ensures forall v : array<T>  :: v[0..] == v[..];
    ensures forall v : array<T>  :: v[0..v.Length] == v[..];

	ensures forall v : array<T>  ::|v[0..v.Length]|==v.Length;
    ensures forall v : array<T> | v.Length>=1 ::|v[1..v.Length]|==v.Length-1;
    
	ensures forall v : array<T>  ::forall k : nat | k < v.Length :: v[..k+1][..k] == v[..k]
  {}

method mcountEven(v:array<int>) returns (n:int)
requires positive(v[..])
ensures  n==CountEven(v[..])
{   ArrayFacts<int>(); 

 n:=0;
 var i:int;
 i:=0;
 while (i<v.Length)
 {
   assert 0<=i<=v.Length;
   assert positive(v[..]);
   assert forall j::0<=j<i ==> isEven(v[j]);
   assert n==CountEven(v[..i]);
   if (v[i]%2==0) {n:=n+1;}
   i:=i+1;
 }
 assert 0<=i<=v.Length;
 assert positive(v[..]);
 assert forall j::0<=j<i ==> isEven(v[j]);
 assert n==CountEven(v[..i]);
 assert n==CountEven(v[..i]);
 }