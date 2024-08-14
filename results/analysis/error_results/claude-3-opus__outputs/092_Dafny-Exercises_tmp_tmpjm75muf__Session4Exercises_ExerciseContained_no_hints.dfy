predicate strictSorted(s : seq<int>) {
	forall u, w :: 0 <= u < w < |s| ==> s[u] < s[w]
}

method mcontained(v:array<int>,w:array<int>,n:int,m:int) returns (b:bool)
requires n<=m && n>=0
requires strictSorted(v[..])
requires strictSorted(w[..])
requires v.Length >= n && w.Length >= m
ensures b==forall k:: 0<= k< n ==> v[k] in w[..m]
{
	var i:=0;
	var j:=0;

	// Loop invariant:
	// - i and j are within bounds
	// - All elements of v[..i] are contained in w[..m]
	// - If i < n, then either j == m or v[i] >= w[j] (since arrays are strictly sorted)
	while(i < n && j < m)
		invariant 0 <= i <= n
		invariant 0 <= j <= m
		invariant forall k :: 0 <= k < i ==> exists l :: 0 <= l < m && v[k] == w[l]
		invariant i < n ==> j == m || (j < m && v[i] >= w[j])
	{	
		if(v[i] == w[j]){
			i := i + 1;
		} else {
			// If v[i] != w[j], then v[i] > w[j] (since arrays are strictly sorted)
			// So we can increment j without missing any potential match for v[i]
			assert i < n && j < m ==> v[i] > w[j];
			j := j + 1;
		}
	}

	// i == n iff all elements of v are found in w
	// If i < n, then v[i] is not in w[..m] since:
	//   - either j == m (loop invariant before exiting), so v[i] > w[m-1]
	//   - or j < m and v[i] >= w[j] > w[m-1] (loop invariant and arrays are strictly sorted)
	assert i < n ==> j == m && (m == 0 || v[i] > w[m-1]);
	b := i == n;
}
