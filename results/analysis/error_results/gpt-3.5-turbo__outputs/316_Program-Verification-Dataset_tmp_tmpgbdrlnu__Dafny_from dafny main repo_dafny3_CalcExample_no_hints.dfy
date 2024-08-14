
// RUN: %testDafnyForEachResolver "%s"

ghost function f(x: int, y: int): int

lemma Associativity(x: int, y: int, z: int)
  ensures f(x, f(y, z)) == f(f(x, y), z)

lemma Monotonicity(y: int, z: int)
  requires y <= z
  ensures forall x :: f(x, y) <= f(x, z)

lemma DiagonalIdentity(x: int)
  ensures f(x, x) == x

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

method DifferentStyleProof(a: int, b: int, c: int, x: int)
  requires c <= x
  requires x == f(a, b)
  ensures f(a, f(b, c)) <= x
{
  assert L1: c <= x;
  assert L2: x == f(a, b);
  Associativity(a, b, c);
  assert L3: f(a, b) == x by { L2 };
  Monotonicity(b, c);
  assert L4: c <= x by { L1 };
  DiagonalIdentity(x);
  assert L5: f(x, x) == x;
  reveal L1, L2, L3, L4, L5;
}
