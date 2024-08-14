  I apologize for the confusion. It seems that the previous answer was not correct. Here is the corrected answer:

type bitvector = int;

method Add(x: bitvector, y: bitvector) returns (z: bitvector)
  requires x >= 0 && y >= 0
  ensures z == x + y
{
  z := x + y;
}

method Subtract(x: bitvector, y: bitvector) returns (z: bitvector)
  requires x >= 0 && y >= 0
  ensures z == x - y
{
  z := x - y;
}

method Multiply(x: bitvector, y: bitvector) returns (z: bitvector)
  requires x >= 0 && y >= 0
  ensures z == x * y
{
  z := x * y;
}

method Divide(x: bitvector, y: bitvector) returns (z: bitvector)
  requires x >= 0 && y >= 0 && y != 0
  ensures z == x / y
{
  z := x / y;
}

method Modulus(x: bitvector, y: bitvector) returns (z: bitvector)
  requires x >= 0 && y >= 0 && y != 0
  ensures z == x % y
{
  z := x % y;
}

method Power(x: bitvector, y: bitvector) returns (z: bitvector)
  requires x >= 0 && y >= 0
  ensures z == x ^ y
{
  z := x ^ y;
}