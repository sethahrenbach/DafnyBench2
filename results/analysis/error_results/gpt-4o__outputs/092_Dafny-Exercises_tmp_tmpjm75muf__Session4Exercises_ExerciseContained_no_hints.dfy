predicate strictSorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}


method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
//Specify and implement an O(m+n) algorithm that returns b
//v and w are strictly increasing ordered arrays
//b is true iff the first n elements of v are contained in the first m elements of w
requires n<=m && n>=0
requires strictSorted(v[..])
requires strictSorted(w[..])
requires v.Length >= n && w.Length >= m
ensures b==forall k:: 0<= k< n ==> v[k] in w[..m]//exists j :: 0 <= j < m && v[k] == w[j]
{
	var i:=0;
	var j:=0;
	while(i<n && j<m)
		// Invariant: All elements of v[0..i) are in w[0..j)
		// Invariant: 0 <= i <= n
		// Invariant: 0 <= j <= m
		// Invariant: forall k :: 0 <= k < i ==> exists l :: 0 <= l < j && v[k] == w[l]
		invariant 0 <= i <= n
		invariant 0 <= j <= m
		invariant forall k :: 0 <= k < i ==> exists l :: 0 <= l < j && v[k] == w[l]
		invariant forall k :: 0 <= k < i ==> v[k] in w[..j]
	{	
		if(v[i] == w[j]){
			i:=i+1;
		} else {
			j:=j+1;
		}
	}
	b := i==n;
	assert b ==> forall k :: 0 <= k < n ==> v[k] in w[..m];
	assert !b ==> exists k :: 0 <= k < n && v[k] !in w[..m];
}