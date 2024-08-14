method GenericMax<A>(cmp: (A, A) -> bool, a: array<A>) returns (max: A)
  requires a != null && a.Length > 0
  requires forall x, y :: cmp.requires(x, y)
  requires forall x, y :: cmp(x, y) || cmp(y, x);
  requires forall x, y, z :: cmp(x, y) && cmp(y, z) ==> cmp(x, z);

  ensures forall x :: 0 <= x < a.Length ==>
    // uncommenting the following line causes the program to verify
    // assume cmp.requires(a[x], max);
    cmp(a[x], max)
{
  max := a[0];
  var i := 1;

  // Loop invariant: max is the maximum element in a[0..i]
  while i < a.Length
    invariant 1 <= i <= a.Length
    invariant forall x :: 0 <= x < i ==> cmp(a[x], max)
    invariant forall x, y :: 0 <= x < i && 0 <= y < i ==> cmp.requires(a[x], a[y])
  {
    // Prove cmp.requires(max, a[i]) before calling cmp
    assert cmp.requires(max, a[i]);

    if !cmp(max, a[i]) {
      max := a[i];
    }
    i := i + 1;
  }
}