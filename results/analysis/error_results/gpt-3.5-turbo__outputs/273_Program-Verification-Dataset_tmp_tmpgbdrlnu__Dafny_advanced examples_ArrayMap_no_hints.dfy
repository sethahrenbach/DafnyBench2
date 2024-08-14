// RUN: /print:log.bpl

method ArrayMap<A>(f: int -> A, a: array<A>)
  requires a != null
  requires forall j :: 0 <= j < a.Length ==> f.requires(j)
  requires forall j :: 0 <= j < a.Length ==> a !in f.reads(j)
  modifies a
  ensures forall j :: 0 <= j < a.Length ==> a[j] == f(j)
{
  var i := 0;
  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> a[k] == f(k)
    invariant forall k :: i <= k < a.Length ==> a[k] == f(k)
  {
    a[i] := f(i);
    i := i + 1;
  }
}


method GenericSort<A>(cmp: (A, A) -> bool, a: array<A>)
  requires a != null
  requires forall x, y :: a !in cmp.reads(x, y)
  requires forall x, y :: cmp.requires(x, y)
  modifies a
  ensures forall x, y :: cmp.requires(x, y)
  ensures forall x, y :: 0 <= x < y < a.Length ==> cmp(a[x], a[y])
{
  var i := 0;

  while i < a.Length
    invariant 0 <= i <= a.Length
    invariant forall k :: 0 <= k < i ==> forall x, y :: cmp.requires(x, y) ==> cmp(a[x], a[y])
    invariant forall k :: i <= k < a.Length ==> forall x, y :: cmp.requires(x, y) ==> cmp(a[x], a[y])
  {
    var j := i - 1;
    while j >= 0 && !cmp(a[j], a[i])
      invariant 0 <= j < a.Length
      invariant forall k :: 0 <= k <= j ==> forall x, y :: cmp.requires(x, y) ==> cmp(a[k], a[y])
      invariant forall k :: j < k < i ==> cmp(a[k], a[j])
      invariant forall k :: i <= k < a.Length ==> forall x, y :: cmp.requires(x, y) ==> cmp(a[x], a[y])
    {
      a[i], a[j] := a[j], a[i];
      j := j - 1;
    }

    i := i + 1;
  }
}