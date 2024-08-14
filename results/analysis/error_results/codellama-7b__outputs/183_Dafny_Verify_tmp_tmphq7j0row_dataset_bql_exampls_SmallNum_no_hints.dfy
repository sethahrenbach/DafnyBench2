
method add_small_numbers (a: array<int>, n: int, max: int) returns (r: int)
  requires n > 0;
  requires n <= a.Length;
  requires (forall i: int :: 0 <= i && i < n ==> a[i] <= max);
  ensures r <= max * n;
{
  var i: int;

  i := 0;
  r := 0;

  while (i < n)
  {
    // Loop invariant: r is the sum of the first i elements of a
    // and the first i elements of a are all less than or equal to max
    assert (forall j: int :: 0 <= j && j < i ==> r <= max * j);

    r := r + a[i];
    i := i + 1;
  }

  // Postcondition: r is the sum of all elements of a
  ensures r == sum(a);
}
