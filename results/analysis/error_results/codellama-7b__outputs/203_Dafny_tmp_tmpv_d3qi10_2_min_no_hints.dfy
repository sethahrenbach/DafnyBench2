
function min(a: int, b: int): int
  ensures min(a, b) <= a && min(a, b) <= b
  ensures min(a, b) == a || min(a, b) == b
{
  if a < b then a else b
}

method minMethod(a: int, b: int) returns (c: int)
  ensures c <= a && c <= b
  ensures c == a || c == b
{
  if a < b then
    c := a;
  else
    c := b;
}

ghost function minFunction(a: int, b: int): int
  ensures minFunction(a, b) <= a && minFunction(a, b) <= b
  ensures minFunction(a, b) == a || minFunction(a, b) == b
{
  if a < b then a else b
}

// Return a minimum of a.
method minArray(a: array<int>) returns (m: int)
  requires a!= null  && a.Length > 0 ;
  loop invariant forall k | 0 <= k < a.Length :: m <= a[k]
  loop invariant exists k | 0 <= k < a.Length :: m == a[k]
{
  /* TODO */
  m := a[0]; // Initialise m avec le premier élément du tableau
  var i := 1;
  while i < a.Length
  {
    /* TODO */
    if a[i] < m then
      m := a[i];
    i := i + 1;
  }
}

method Main(){
  var integer:= min(1,2);
  print(integer);
}
