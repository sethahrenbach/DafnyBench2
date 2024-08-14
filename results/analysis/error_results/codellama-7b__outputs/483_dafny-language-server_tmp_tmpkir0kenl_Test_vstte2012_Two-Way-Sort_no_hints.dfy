
method two_way_sort(a: array<bool>)
  modifies a
  ensures forall m,n :: 0 <= m < n < a.Length ==> (!a[m] || a[n])
  ensures multiset(a[..]) == old(multiset(a[..]))
{
  var i := 0;
  var j := a.Length - 1;
  while (i <= j)
  {
    // Loop invariant: a[..i] is sorted and a[j..] is sorted
    // and a[i] and a[j] are swapped
    loop invariant 0 <= i <= j < a.Length
    loop invariant forall m :: 0 <= m < i ==> a[m] == old(a[m])
    loop invariant forall m :: i <= m < j ==> a[m] == old(a[m])
    loop invariant forall m :: j <= m < a.Length ==> a[m] == old(a[m])
    loop invariant multiset(a[..]) == old(multiset(a[..]))

    // Precondition: a[i] and a[j] are not both true
    // or false
    requires !(a[i] && a[j]) || !(a[i] || a[j])

    // Postcondition: a[i] and a[j] are swapped
    ensures a[i] == old(a[j])
    ensures a[j] == old(a[i])

    // Postcondition: a[..i] and a[j..] are sorted
    ensures forall m :: 0 <= m < i ==> a[m] == old(a[m])
    ensures forall m :: i <= m < j ==> a[m] == old(a[m])
    ensures forall m :: j <= m < a.Length ==> a[m] == old(a[m])

    // Postcondition: a is a permutation of the pre-state
    // array
    ensures multiset(a[..]) == old(multiset(a[..]))

    if (!a[i]) {
      i := i+1;
    } else if (a[j]) {
      j := j-1;
    } else {
      swap(a, i, j);
      i := i+1;
      j := j-1;
    }
  }
}
