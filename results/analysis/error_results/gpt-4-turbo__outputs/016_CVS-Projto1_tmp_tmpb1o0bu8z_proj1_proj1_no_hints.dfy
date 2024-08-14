
//Exercicio 1.a)
function sum (a:array<int>, i:int, j:int) :int
  reads a
  requires 0 <= i <= j <= a.Length
{
  if i == j then
    0
  else
    a[j-1] + sum(a, i, j-1)
}

//Exercicio 1.b)
method query (a:array<int>, i:int, j:int) returns (s:int)
  requires 0 <= i <= j <= a.Length
  ensures s == sum(a, i, j)
{
  s := 0;
  var aux := i;

  while (aux < j)
    invariant i <= aux <= j
    invariant s == sum(a, i, aux)
  {
    s := s + a[aux];
    aux := aux + 1;
  }
}

//Exercicio 1.c)
lemma queryLemma(a:array<int>, i:int, j:int, k:int)
  requires 0 <= i <= k <= j <= a.Length
  ensures sum(a, i, k) + sum(a, k, j) == sum(a, i, j)
{
  if (k == j) {
    assert sum(a, k, j) == 0;
  } else {
    queryLemma(a, i, k, k+1);
    queryLemma(a, k+1, j, k+1);
    assert sum(a, i, k) + sum(a, k+1, j) == sum(a, i, j);
  }
}

method queryFast (a:array<int>, c:array<int>, i:int, j:int) returns (r:int)
  requires is_prefix_sum_for(a,c) && 0 <= i <= j <= a.Length < c.Length
  ensures r == sum(a, i, j)
{
  if (i == j) {
    r := 0;
  } else {
    r := c[j] - c[i];
  }
  queryLemma(a, 0, j, i); // Corrected the call to queryLemma to use valid indices.
}

predicate is_prefix_sum_for (a:array<int>, c:array<int>)
  reads c, a
{
  a.Length + 1 == c.Length &&
  c[0] == 0 &&
  forall j :: 1 <= j <= a.Length ==> c[j] == sum(a, 0, j)
}

///Exercicio 2.
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

method from_array<T>(a: array<T>) returns (l: List<T>)
  requires a.Length > 0
  ensures forall j::0 <= j < a.Length ==> mem(a[j], l)
{
  var i := a.Length-1;
  l := Nil;

  while (i >= 0)
    decreases i
    invariant 0 <= i <= a.Length
    invariant forall k :: i < k < a.Length ==> mem(a[k], l)
  {
    l := Cons(a[i], l);
    i := i - 1;
  }
}

function mem<T(==)> (x: T, l:List<T>) : bool
{
  match l
  case Nil => false
  case Cons(y, r) => if (x == y) then true else mem(x, r)
}
