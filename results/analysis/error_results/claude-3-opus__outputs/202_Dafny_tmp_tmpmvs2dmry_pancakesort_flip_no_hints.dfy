// flips (i.e., reverses) array elements in the range [0..num]
method flip (a: array<int>, num: int)
requires a.Length > 0;
requires 0 <= num < a.Length;
modifies a;
ensures forall k :: 0 <= k <= num ==> a[k] == old(a[num-k])
ensures forall k :: num < k < a.Length ==> a[k] == old(a[k])
// ensures multiset(a[..]) == old(multiset(a[..]))
{
  var tmp:int;
  var i := 0;
  var j := num;
  while (i < j)
  invariant 0 <= i <= j <= num
  invariant forall k :: 0 <= k < i ==> a[k] == old(a[num-k])
  invariant forall k :: j <= k <= num ==> a[k] == old(a[k])
  invariant forall k :: i <= k < j ==> a[k] == old(a[k]) || a[k] == old(a[num-k])
  invariant forall k :: num < k < a.Length ==> a[k] == old(a[k])
  {
    tmp := a[i];
    a[i] := a[j];
    a[j] := tmp;
    i := i + 1;
    j := j - 1;
  }
  // assert i == j && 0 <= i <= num ==> a[i] == old(a[num-i]);
}