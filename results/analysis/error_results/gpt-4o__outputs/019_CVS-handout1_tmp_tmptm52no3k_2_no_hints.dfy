/*                                      Functional Lists and Imperative Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes        57854
*/

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function length<T>(l: List<T>): nat
{
  match l
  case Nil => 0
  case Cons(_, t) => 1 + length(t)
}

predicate mem<T(==)> (l: List<T>, x: T)
{
  match l
  case Nil => false
  case Cons(h, t) => if(h == x) then true else mem(t, x)
}

function at<T>(l: List<T>, i: nat): T
  requires i < length(l)
{
  if i == 0 then l.head else at(l.tail, i - 1)
}

method from_array<T>(a: array<T>) returns (l: List<T>)
  requires a.Length >= 0
  ensures length(l) == a.Length
  ensures forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[i]
  ensures forall x :: mem(l, x) ==> exists i: int :: 0 <= i < length(l) && a[i] == x
{
  l := Nil;
  var i: int := a.Length - 1;
  while(i >= 0)
    invariant 0 <= i + 1 <= a.Length
    invariant length(l) == a.Length - (i + 1)
    invariant forall j: int :: 0 <= j < length(l) ==> at(l, j) == a[j + i + 1]
    invariant forall x :: mem(l, x) ==> exists j: int {:trigger mem(l, x), :trigger a[j + i + 1]} :: 0 <= j < length(l) && a[j + i + 1] == x
  {
    l := Cons(a[i], l);
    i := i-1;
  }
}

method Main() {
  var l: List<int> := List.Cons(1, List.Cons(2, List.Cons(3, Nil)));
  var arr: array<int> := new int [3](i => i + 1);
  var t: List<int> := from_array(arr);
  print l;
  print "\n";
  print t;
  print "\n";
  print t == l;
}