
function f(): nat
  ensures f() == 0
{
  var x := 0;
  x
}

// Annotations

// Loop Invariant
// The loop invariant is that x is always 0
ensures f() == 0

// Postcondition
// The postcondition is that the function returns 0
ensures f() == 0

// Assertion
// The assertion is that x is always 0
assert(x == 0)
