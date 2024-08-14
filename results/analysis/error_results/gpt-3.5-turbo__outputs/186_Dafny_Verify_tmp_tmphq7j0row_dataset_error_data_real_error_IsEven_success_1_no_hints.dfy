
function even(n: int): bool
  requires n >= 0;
{
  if n == 0 then true else !even(n-1)
}

method is_even(n: int) returns (r: bool)
  requires n >= 0;
  ensures r <==> even(n);
{
  var i: int := 0;
  r := true;

  while i < n
    invariant 0 <= i <= n && (i % 2 == 0 <==> r)
    invariant even(i) <==> r
  {
    assert even(i) <==> r;
    r := !r;
    i := i + 1;
  }
}
