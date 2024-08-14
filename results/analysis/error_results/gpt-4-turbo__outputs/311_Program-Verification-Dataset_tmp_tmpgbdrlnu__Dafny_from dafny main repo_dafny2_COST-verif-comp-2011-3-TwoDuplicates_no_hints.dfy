// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false

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
    invariant 0 <= i <= d.Length
    invariant forall j :: 0 <= j < i ==> d[j] == -1
  {
    d[i], i := -1, i+1;
  }

  i, p, q := 0, 0, 1;
  while (i < a.Length)
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < a.Length - 2 ==> 
                ((d[j] == -1 && forall k :: 0 <= k < i ==> a[k] != j) ||
                (0 <= d[j] < i && a[d[j]] == j))
    invariant p == q ==> IsDuplicate(a, p)
    invariant p != q ==> (p == 0 && q == 1) || (IsDuplicate(a, p) && IsDuplicate(a, q))
    decreases a.Length - i  // Ensuring termination by decreasing the distance to the end of the array
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
      } else if (p == a[i]) {
        // this is another copy of the same duplicate we have seen before
      } else {
        // this is the second duplicate
        q := a[i];
        assert IsDuplicate(a, q);  // Assert to ensure the postcondition can be proved
        assert IsDuplicate(a, p);  // Assert to ensure the postcondition can be proved
        assert p != q;             // Assert to ensure the postcondition can be proved
        return;
      }
    }
    i := i + 1;
  }
  assert false;  // This should be unreachable due to the problem constraints and loop logic
}