// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


/*
Rustan Leino, 5 Oct 2011

COST Verification Competition, Challenge 3: Two equal elements
http://foveoos2011.cost-ic0701.org/verification-competition

Given: An integer array a of length n+2 with n>=2. It is known that at
least two values stored in the array appear twice (i.e., there are at
least two duplets).

Implement and verify a program finding such two values.

You may assume that the array contains values between 0 and n-1.
*/

ghost predicate IsDuplicate(a: array<int>, p: int)
  reads a
{
  IsPrefixDuplicate(a, a.Length, p)
}

ghost predicate IsPrefixDuplicate(a: array<int>, k: int, p: int)
  requires 0 <= k <= a.Length;
  reads a;
{
  exists i,j :: 0 <= i < j < k && a[i] == a[j] == p
}

method Search(a: array<int>) returns (p: int, q: int)
  requires 4 <= a.Length;
  requires exists p,q :: p != q && IsDuplicate(a, p) && IsDuplicate(a, q);  // two distinct duplicates exist
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i] < a.Length - 2;  // the elements of "a" in the range [0.. a.Length-2]
  ensures p != q && IsDuplicate(a, p) && IsDuplicate(a, q);
{
  // allocate an array "d" and initialize its elements to -1.
  var d := new int[a.Length-2];
  var i := 0;
  while (i < d.Length)
    invariant 0 <= i <= d.Length;
    invariant forall j :: 0 <= j < i ==> d[j] == -1;
  {
    d[i], i := -1, i+1;
  }

  i, p, q := 0, 0, 1;
  while (i < a.Length)
    invariant 0 <= i <= a.Length;
    invariant p != q ==> !IsPrefixDuplicate(a, i, p);
    invariant p == q ==> IsPrefixDuplicate(a, i, p);
    invariant forall j :: 0 <= j < a.Length-2 ==>
                (d[j] == -1 && forall k :: 0 <= k < i ==> a[k] != j) ||
                (0 <= d[j] < i && a[d[j]] == j);
  {
    var k := d[a[i]];
    if (k == -1) {
      // a[i] does not exist in a[..i]
      d[a[i]] := i;
    } else {
      // we have encountered a duplicate
      if (p != q) {
        // this is the first duplicate encountered
        p, q := a[i], a[i];
        assert IsPrefixDuplicate(a, i+1, p);
      } else if (p == a[i]) {
        // this is another copy of the same duplicate we have seen before
        assert IsPrefixDuplicate(a, i+1, p);
      } else {
        // this is the second duplicate
        q := a[i];
        assert IsPrefixDuplicate(a, i+1, p);
        assert IsPrefixDuplicate(a, i+1, q);
        assert p != q;  // the two duplicates are distinct
        return;
      }
    }
    i := i + 1;
  }
  assert exists p,q :: p != q && IsDuplicate(a, p) && IsDuplicate(a, q);
}
