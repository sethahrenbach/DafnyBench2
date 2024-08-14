
function fib(n: nat): nat
{
  if n == 0 || n == 1 {
    return 1;
  } else {
    return fib(n-1) + fib(n-2);
  }
}

method Fib(n: nat) returns (r: nat)
  ensures r == fib(n)
{
  if (n == 0) {
    return 1;
  }

  var next := 1;
  var current := 1;
  var i := 2;

  while i <= n
    invariant 1 <= current <= fib(i)
    invariant 1 <= next <= fib(i+1)
    invariant 2 <= i <= n+1
    invariant current == fib(i-1) && next == fib(i)
  {
    var tmp := next;
    next := next + current;
    current := tmp;
    i := i + 1;
  }
  return current;
}

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function add(l: List<int>): int
{
  match l
  case Nil => 0
  case Cons(x, xs) => x + add(xs)
}

method addImp(l: List<int>) returns (r: int)
  ensures r == add(l)
{
  r := 0;
  var ll := l;
  while ll != Nil
    invariant r == add(ll)
  {
    r := r + ll.head;
    ll := ll.tail;
  }
}

method maxArray(arr: array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x :: 0 <= x < arr.Length && arr[x] == max
{
  max := arr[0];
  var index := 1;
  while index < arr.Length
    invariant forall i: int :: 0 <= i < index ==> arr[i] <= max
    invariant exists x :: 0 <= x < index && arr[x] == max
  {
    if arr[index] > max {
      max := arr[index];
    }
    index := index + 1;
  }
}

method maxArrayReverse(arr: array<int>) returns (max: int)
  requires arr.Length > 0
  ensures forall i: int :: 0 <= i < arr.Length ==> arr[i] <= max
  ensures exists x :: 0 <= x < arr.Length && arr[x] == max
{
  var ind := arr.Length - 1;
  max := arr[ind];

  while ind >= 0
    invariant forall i: int :: ind <= i < arr.Length ==> arr[i] <= max
    invariant exists x :: ind <= x < arr.Length && arr[x] == max
  {
    if arr[ind] > max {
      max := arr[ind];
    }
    ind := ind - 1;
  }
}

function sum(n: nat): nat
{
  if n == 0 {
    return 0;
  } else {
    return n + sum(n-1);
  }
}

method sumBackwards(n: nat) returns (r: nat)
  ensures r == sum(n)
{
  var i := n;
  r := 0;

  while i >= 0
    invariant 0 <= r <= sum(i)
    invariant 0 <= i <= n
  {
    r := r + i;
    i := i - 1;
  }
}
