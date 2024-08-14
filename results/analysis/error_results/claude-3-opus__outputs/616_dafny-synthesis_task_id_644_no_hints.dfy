method Reverse(a: array<int>)
	modifies a;
	ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
{
	var l := a.Length - 1;
	var i := 0;
	while (i <= l/2)
	invariant 0 <= i <= l/2
	invariant forall k :: 0 <= k < i ==> a[k] == old(a[l-k])
	invariant forall k :: i <= k <= l-i ==> a[k] == old(a[k])
	invariant forall k :: l-i < k <= l ==> a[k] == old(a[l-k])
	{
		a[i], a[l-i] := a[l-i], a[i];
		i := i + 1;
	}
	assert forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
}

method ReverseUptoK(s: array<int>, k: int)
    modifies s
    requires 2 <= k <= s.Length
    ensures forall i :: 0 <= i < k ==> s[i] == old(s[k - 1 - i])
    ensures forall i :: k <= i < s.Length ==> s[i] == old(s[i])
{
	var l := k - 1;
	var i := 0;
	while (i <= l/2)
	invariant 0 <= i <= l/2
	invariant forall j :: 0 <= j < i ==> s[j] == old(s[l-j])
	invariant forall j :: i <= j <= l-i ==> s[j] == old(s[j])
	invariant forall j :: l-i < j <= l ==> s[j] == old(s[l-j])
	invariant forall j :: l < j < k ==> s[j] == old(s[j])
	invariant forall j :: k <= j < s.Length ==> s[j] == old(s[j])
	{
		s[i], s[l-i] := s[l-i], s[i];
		i := i + 1;
	}
	assert forall i :: 0 <= i < k ==> s[i] == old(s[k - 1 - i]);
	assert forall i :: k <= i < s.Length ==> s[i] == old(s[i]);
}