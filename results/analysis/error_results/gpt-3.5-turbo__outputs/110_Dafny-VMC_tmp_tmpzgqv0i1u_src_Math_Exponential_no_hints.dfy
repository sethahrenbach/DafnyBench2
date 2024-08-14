
module Exponential {
  ghost function {:axiom} Exp(x: real): real

  lemma {:axiom} FunctionalEquation(x: real, y: real)
    ensures Exp(x + y) == Exp(x) * Exp(y)

  lemma {:axiom} Increasing(x: real, y: real)
    requires x < y
    ensures Exp(x) < Exp(y)

  lemma {:axiom} EvalOne()
    ensures 2.718281828 <= Exp(1.0) <= 2.718281829

  lemma Positive(x: real)
    ensures Exp(x) > 0.0
  {
    var sqrt := Exp(x / 2.0);
    assert sqrt >= 0.0;
    if Exp(x) == 0.0 {
      assert Exp(x + 1.0) == 0.0;
    }
  }

  lemma EvalZero()
    ensures Exp(0.0) == 1.0
  {
    var one := Exp(0.0);
    Positive(0.0);
    assert Exp(0.0) == 1.0;
    assert Exp(0.0) > 0.0;
    assert Exp(0.0) * Exp(0.0) == 1.0;
    assert Exp(0.0) * Exp(0.0) == Exp(0.0);
    assert Exp(0.0) * 1.0 == Exp(0.0);
  }
}
