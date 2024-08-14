
predicate sorted_seg(a:array<int>, i:int, j:int)
  requires 0 <= i <= j+1 <= a.Length
{
  // Loop invariant: a[0..i-1] is sorted
  // Loop variant: a[i..j] is sorted
  for(var k:int = i; k <= j; k++)
  {
    // Check that a[k] is greater than or equal to a[k-1]
    assert a[k] >= a[k-1];
  }
}
