// RUN: %dafny /compile:3 /print:"%t.print" /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// /autoTriggers:1 added to suppress instabilities

method Main() { }

method H(a: array<int>, c: array<int>, n: nat, j: nat)
  requires j < n == a.Length == c.Length
{
  var A := a[..];
  var C := c[..];

  if {
    case A[j] == C[j] =>
      // The assertion below holds for indices less than j
      assert forall i :: 0 <= i < j ==> A[i] == C[i];
      // If j < n and A[j] == C[j], then A[i] == C[i] for all i < n
      if j < n && A[j] == C[j] {
        assert A[..j+1] == C[..j+1]; // Prove equality up to index j
        assert forall i :: j+1 <= i < n ==> A[i] == C[i]; // Prove remaining indices
        assert A == C; // Deduce full equality
      }
    case forall i :: 0 <= i < n ==> A[i] == C[i] =>
      assert A[..n] == C[..n];
      assert A == C;
    case forall i :: 0 <= i < n ==> A[i] == C[i] =>
      assert A[..n] == C[..n];
      assert A == C;
    case A == C =>
      assert A[..n] == C[..n];
      assert forall i :: 0 <= i < n ==> A[i] == C[i];
    case A == C =>
      assert A[..n] == C[..n];
      assert forall i :: 0 <= i < n ==> A[i] == C[i];
    case true =>
  }
}

method K(a: array<int>, c: array<int>, n: nat)
  requires n <= a.Length && n <= c.Length
{
  var A := a[..n];
  var C := c[..n];
  if {
    case A == C =>
      assert forall i :: 0 <= i < n ==> a[i] == c[i];
    case A == C =>
      assert forall i :: 0 <= i < n ==> a[i] == c[i];
    case true =>
  }
}

method L(a: array<int>, c: array<int>, n: nat)
  requires n <= a.Length == c.Length
{
  var A := a[n..];
  var C := c[n..];
  var h := a.Length - n;
  if {
    case A == C =>
      assert forall i :: n <= i < a.Length ==> a[i] == c[i];
    case A == C =>
      assert forall i :: n <= i < a.Length ==> a[i] == c[i];
    case true =>
  }
}

method M(a: array<int>, c: array<int>, m: nat, n: nat, k: nat, l: nat)
  requires k + m <= a.Length
  requires l + n <= c.Length
{
  var A := a[k..k+m];
  var C := c[l..l+n];
  if A == C && m == n {
    assert forall i :: 0 <= i < m ==> a[k+i] == c[l+i];
  }
}

method M'(a: array<int>, c: array<int>, m: nat, n: nat, k: nat, l: nat)
  requires k + m <= a.Length
  requires l + n <= c.Length
{
  if {
    case l+m <= c.Length && forall i :: 0 <= i < m ==> a[i] == c[l+i] =>
      assert forall i :: 0 <= i < m ==> a[i] == c[l+i];
    case l+a.Length <= c.Length && forall i :: k <= i < a.Length ==> a[i] == c[l+i] =>
      assert forall i :: k <= i < a.Length ==> a[i] == c[l+i];
    case l+k+m <= c.Length && forall i :: k <= i < k+m ==> a[i] == c[l+i] =>
      assert forall i :: k <= i < k+m ==> a[i] == c[l+i];
    case true =>
  }
}