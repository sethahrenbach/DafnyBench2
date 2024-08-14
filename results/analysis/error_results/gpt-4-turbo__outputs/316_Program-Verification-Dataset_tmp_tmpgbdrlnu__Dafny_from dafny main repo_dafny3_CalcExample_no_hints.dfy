
// RUN: %testDafnyForEachResolver "%s"

// Here is a function "f" and three axioms (that is, unproved lemmas) about "f":

ghost function f(x: int, y: int): int

lemma Associativity(x: int, y: int, z: int)
  ensures f(x, f(y, z)) == f(f(x, y), z)
{
}

lemma Monotonicity(y: int, z: int)
  requires y <= z
  ensures forall x :: f(x, y) <= f(x, z)
{
}

lemma DiagonalIdentity(x: int)
  ensures f(x, x) == x
{
}

// From these axioms, we can prove a lemma about "f":

method CalculationalStyleProof(a: int, b: int, c: int, x: int)
  requires c <= x == f(a, b)
  ensures f(a, f(b, c)) <= x
{
  calc {
    f(a, f(b, c));
  ==  { Associativity(a, b, c); }
    f(f(a, b), c);
  ==  { assert f(a, b) == x; }
    f(x, c);
  <=  { assert c <= x; Monotonicity(c, x); }
    f(x, x);
  ==  { DiagonalIdentity(x); }
    x;
  }
}

// Here's the same lemma, but with a proof written in a different style.

method DifferentStyleProof(a: int, b: int, c: int, x: int)
  requires c <= x == f(a, b)
  ensures f(a, f(b, c)) <= x
{
  Associativity(a, b, c);
  assert f(a, f(b, c)) == f(f(a, b), c);
  assert f(f(a, b), c) == f(x, c);
  Monotonicity(c, x);
  assert f(x, c) <= f(x, x);
  DiagonalIdentity(x);
  assert f(x, x) == x;
}
