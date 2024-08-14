
method from_array<T>(a: array<T>) returns (l: list<T>)
  requires a.Length >= 0
  ensures length(l) == a.Length
  ensures forall i: int :: 0 <= i < length(l) ==> at(l, i) == a[i]
  ensures forall x :: mem(l, x) ==> exists i: int :: 0 <= i < length(l) && a[i] == x
{
  l := Nil;
  var i: int := a.Length - 1;
  while(i >= 0)
  {
    l := Cons(a[i], l);
    i := i-1;
  }
}
