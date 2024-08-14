
function sum(a: array<int>, i: int, j: int): int
  requires 0 <= i <= j <= a.Length
  ensures 0 <= i <= j <= a.Length ==> sum(a, i, j) == a[j-1] + sum(a, i, j-1)
{
  if i == j then
    0
  else
    a[j-1] + sum(a, i, j-1)
}

method query(a: array<int>, i: int, j: int): int
  requires 0 <= i <= j <= a.Length
  ensures query(a, i, j) == sum(a, i, j)
  loop invariant 0 <= i <= j <= a.Length ==> query(a, i, j) == sum(a, i, j)
{
  var s := 0;
  var aux := i;

  while aux < j do
  {
    s := s + a[aux];
    aux := aux + 1;
  }

  return s;
}

lemma queryLemma(a: array<int>, i: int, j: int, k: int)
  requires 0 <= i <= k <= j <= a.Length
  ensures queryLemma(a, i, j, k) == sum(a, i, j) + sum(a, k, j)
  loop invariant 0 <= i <= k <= j <= a.Length ==> queryLemma(a, i, j, k) == sum(a, i, j) + sum(a, k, j)
{
}

method queryFast(a: array<int>, c: array<int>, i: int, j: int): int
  requires is_prefix_sum_for(a, c) && 0 <= i <= j <= a.Length < c.Length
  ensures queryFast(a, c, i, j) == sum(a, i, j)
  loop invariant 0 <= i <= j <= a.Length ==> queryFast(a, c, i, j) == sum(a, i, j)
{
  var r := c[j] - c[i];
  queryLemma(a, 0, j, i);

  return r;
}

predicate is_prefix_sum_for(a: array<int>, c: array<int>):
  a.Length + 1 == c.Length
  c[0] == 0
  forall j :: 1 <= j <= a.Length ==> c[j] == sum(a, 0, j)
  forall k :: 1 <= k <= a.Length ==> c[k] == sum(a, k, a.Length)
  forall i :: 0 <= i < a.Length ==> c[i] == sum(a, i, a.Length)
