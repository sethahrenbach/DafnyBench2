method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |set i | i in numbers && i < threshold|
{
  count := 0;
  var shrink := numbers;
  var grow := {};

  while |shrink| > 0
    invariant grow + shrink == numbers // Ensures all elements are accounted for
    invariant grow * shrink == {} // Ensures no overlap between grow and shrink
    invariant count == |set i | i in grow && i < threshold| // Correctly tracks the count of elements less than threshold in grow
    invariant forall i :: i in grow ==> i < threshold ==> i in numbers // Ensures elements in grow were originally in numbers and meet the condition
    decreases |shrink| // Ensures termination by reducing the size of shrink
  {
    var i: int :| i in shrink; // Choose an arbitrary element from shrink
    shrink := shrink - {i}; // Remove the chosen element from shrink
    grow := grow + {i}; // Add the chosen element to grow
    if i < threshold {
      count := count + 1; // Increment count if the element is less than the threshold
    }
  }
}