method LinearSearch3<T>(a: array<T>, P: T -> bool) returns (n: int)
  requires exists i :: 0 <= i < a.Length && P(a[i])
  ensures 0 <= n < a.Length && P(a[n])
  ensures forall k :: 0 <= k < n ==> !P(a[k])
{
  n := 0;
  while n < a.Length && !P(a[n])
    invariant 0 <= n <= a.Length
    invariant forall k :: 0 <= k < n ==> !P(a[k])
  {
    n := n + 1;
  }
  assert n < a.Length; // This assertion is needed to prove the postcondition
}