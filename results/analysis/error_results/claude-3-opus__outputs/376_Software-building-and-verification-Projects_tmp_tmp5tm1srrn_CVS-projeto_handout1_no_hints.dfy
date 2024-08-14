// 1 a)

// [ai, aj[
function sum(a: array<int>, i: int, j: int) : int
  requires 0 <= i <= j <= a.Length
  reads a
{
  if i == j then 0
  else a[j-1] + sum(a, i, j-1)
}

// 1 b)
method query(a: array<int>, i: int, j: int) returns (res : int)
  requires 0 <= i <= j <= a.Length
  ensures res == sum(a, i, j)
{
  res := 0;
  var ind := j;

  while ind > i
    invariant i <= ind <= j
    invariant res == sum(a, ind, j)
  {
    ind := ind - 1;
    res := res + a[ind];
  }
  assert ind == i;
}

// 1 c)
// a -> [1, 10, 3, −4, 5]
// c -> [0, 1, 11, 14, 10, 15]
method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
  requires 0 <= i <= j <= a.Length
  requires is_prefix_sum_for(a,c)
  ensures r == sum(a, i, j)
{
  var k := i;
  proof(a, 0, j, k);
  assert sum(a, 0, i) + sum(a, i, j) == sum(a, 0, j);
  assert c[i] == sum(a, 0, i);
  assert c[j] == sum(a, 0, j);
  r := c[j] - c[i];
}

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
  reads c, a
{
  a.Length + 1 == c.Length && forall i: int :: 0 <= i <= a.Length ==> c[i] == sum(a, 0, i)
}

lemma proof(a: array<int>, i: int, j: int, k:int)
  requires 0 <= i <= k <= j <= a.Length
  ensures sum(a, i, k) + sum(a, k, j) == sum(a, i, j)
{
  if k == j {
    assert sum(a, k, j) == 0;
  } else {
    calc == {
      sum(a, i, k) + sum(a, k, j);
      sum(a, i, k) + a[j-1] + sum(a, k, j-1);
      { proof(a, i, j-1, k); }
      sum(a, i, j-1) + a[j-1];
      sum(a, i, j);
    }
  }
}

// 2

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

method from_array<T>(a: array<T>) returns (l: List<T>)
  ensures forall i: int :: 0 <= i < a.Length ==> mem(a[i], l)
  ensures forall x: T :: mem(x, l) ==> exists y: int :: 0 <= y < a.Length && a[y] == x
{
  l := Nil;
  var i := a.Length - 1;
  while i >= 0
    invariant 0 <= i+1 <= a.Length
    invariant forall j: int :: i+1 <= j < a.Length ==> mem(a[j], l)
    invariant forall x: T :: mem(x, l) ==> exists y: int :: i+1 <= y < a.Length && a[y] == x
  {
    var prev_l := l;
    l := Cons(a[i], l);
    forall j | i+1 <= j < a.Length 
      ensures mem(a[j], l)
    {
      assert mem(a[j], prev_l);
    }
    i := i - 1;
  }
  assert i == -1;
  assert forall j: int :: 0 <= j < a.Length ==> mem(a[j], l);
}

function mem<T(==)> (x: T, l: List<T>) : bool
{
  match l
  case Nil => false
  case Cons(h, t) => h == x || mem(x, t)
}