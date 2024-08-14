
method Reverse(a: array<int>): array<int>
  modifies a;
  ensures forall k :: 0 <= k < a.Length ==> a[k] == old(a[(a.Length-1) - k]);
{
  var l := a.Length - 1;
  var i := 0;
  while (i < l-i)
  {
    // Loop invariant: a[0..i] is the original array, and a[i+1..l] is the reversed array
    // Assertion: a[i] == old(a[(a.Length-1) - i])
    assert a[i] == old(a[(a.Length-1) - i]);
    a[i], a[l-i] := a[l-i], a[i];
    i := i + 1;
  }
  return a;
}
