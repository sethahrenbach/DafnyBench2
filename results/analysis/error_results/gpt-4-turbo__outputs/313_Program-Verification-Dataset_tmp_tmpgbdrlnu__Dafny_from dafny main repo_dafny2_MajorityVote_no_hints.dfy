
// RUN: %testDafnyForEachResolver "%s"

function Count<T(==)>(a: seq<T>, s: int, t: int, x: T): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else
  Count(a, s, t-1, x) + if a[t-1] == x then 1 else 0
}

ghost predicate HasMajority<T>(a: seq<T>, s: int, t: int, x: T)
  requires 0 <= s <= t <= |a|
{
  2 * Count(a, s, t, x) > t - s
}

method FindWinner<Candidate(==)>(a: seq<Candidate>, ghost K: Candidate) returns (k: Candidate)
  requires HasMajority(a, 0, |a|, K) // K has a (strict) majority of the votes
  ensures k == K  // find K
{
  k := a[0];
  var n, c, s := 1, 1, 0;
  while n < |a|
    invariant 0 <= s <= n <= |a|
    invariant 1 <= c <= n - s + 1
    invariant HasMajority(a, s, n, k) || c == 1
    invariant forall j :: s <= j < n ==> (a[j] == k) || (2 * Count(a, s, j, k) <= j - s)
  {
    if a[n] == k {
      n, c := n + 1, c + 1;
    } else if 2 * c > n + 1 - s {
      n := n + 1;
    } else {
      n := n + 1;
      Lemma_Unique(a, s, n, K, k);
      Lemma_Split(a, s, n, |a|, K);
      k, n, c, s := a[n], n + 1, 1, n;
    }
  }
  Lemma_Unique(a, s, |a|, K, k);  // both k and K have a majority, so K == k
}

datatype Result<Candidate> = NoWinner | Winner(cand: Candidate)

method DetermineElection<Candidate(==,0,!new)>(a: seq<Candidate>) returns (result: Result<Candidate>)
  ensures result.Winner? ==> 2 * Count(a, 0, |a|, result.cand) > |a|
  ensures result.NoWinner? ==> forall c :: 2 * Count(a, 0, |a|, c) <= |a|
{
  if |a| == 0 { return NoWinner; }
  ghost var b := exists c :: 2 * Count(a, 0, |a|, c) > |a|;
  ghost var w :| b ==> 2 * Count(a, 0, |a|, w) > |a|;
  var cand := SearchForWinner(a, b, w);
  return if 2 * Count(a, 0, |a|, cand) > |a| then Winner(cand) else NoWinner;
}

method SearchForWinner<Candidate(==)>(a: seq<Candidate>, ghost hasWinner: bool, ghost K: Candidate) returns (k: Candidate)
  requires |a| != 0
  requires hasWinner ==> 2 * Count(a, 0, |a|, K) > |a|  // K has a (strict) majority of the votes
  ensures hasWinner ==> k == K  // find K
{
  k := a[0];
  var n, c, s := 1, 1, 0;
  while n < |a|
    invariant 0 <= s <= n <= |a|
    invariant 1 <= c <= n - s + 1
    invariant HasMajority(a, s, n, k) || c == 1
    invariant forall j :: s <= j < n ==> (a[j] == k) || (2 * Count(a, s, j, k) <= j - s)
  {
    if a[n] == k {
      n, c := n + 1, c + 1;
    } else if 2 * c > n + 1 - s {
      n := n + 1;
    } else {
      n := n + 1;
      Lemma_Unique(a, s, n, K, k);
      Lemma_Split(a, s, n, |a|, K);
      if |a| == n { return; }
      k, n, c, s := a[n], n + 1, 1, n;
    }
  }
  Lemma_Unique(a, s, |a|, K, k);  // both k and K have a majority, so K == k
}

lemma Lemma_Split<T>(a: seq<T>, s: int, t: int, u: int, x: T)
  requires 0 <= s <= t <= u <= |a|
  ensures Count(a, s, t, x) + Count(a, t, u, x) == Count(a, s, u, x)
{
  // Proof by induction automatically handled by Dafny.
}

lemma Lemma_Unique<T>(a: seq<T>, s: int, t: int, x: T, y: T)
  requires 0 <= s <= t <= |a|
  ensures x != y ==> Count(a, s, t, x) + Count(a, s, t, y) <= t - s
{
  // Proof by induction automatically handled by Dafny.
}
