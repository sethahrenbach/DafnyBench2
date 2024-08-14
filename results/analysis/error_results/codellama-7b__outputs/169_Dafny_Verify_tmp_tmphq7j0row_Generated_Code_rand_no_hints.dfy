
method Main(xInit: int, y: int) returns (z: int)
  requires xInit >= 0
  requires y >= 0
  ensures z == 0
{
  var x := xInit;
  z := x * y;
  
  while x > 0
  {
    // Loop Invariant: x > 0
    // Precondition: x > 0
    // Postcondition: x > 0
    x := x - 1;
    // Loop Invariant: x > 0
    // Precondition: x > 0
    // Postcondition: x > 0
    z := z - y;
  }
}
