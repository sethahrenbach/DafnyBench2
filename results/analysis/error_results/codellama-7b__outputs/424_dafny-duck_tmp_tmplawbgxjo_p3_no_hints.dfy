
method max(x: array<nat>) returns (y: nat)
  // for index loop problems
  requires x.Length > 0
  // ensuring that we maintain y as greater than the elements in the array 
  ensures forall j :: 0 <= j < x.Length ==> y >= x[j]
  // ensuring that the return value is in the array
  ensures y in x[..]
{
  // loop invariant: y is the maximum value seen so far
  // loop variant: i is the index of the current element being considered
  loop invariant y >= x[i]
  loop variant i < x.Length
  {
    // precondition: the array is non-empty and the first element is the maximum value seen so far
    // precondition: i is the index of the current element being considered
    requires x.Length > 0 && y >= x[0]
    requires 0 <= i < x.Length
    {
      // postcondition: the return value is the maximum value seen so far
      // postcondition: the return value is in the array
      ensures y == max(x)
      ensures y in x[..]
      {
        // code body
        if(i < x.Length)
        {
          if(y <= x[i]){
            y := x[i];
          }
        }
        i := i + 1;
      }
    }
  }
}
