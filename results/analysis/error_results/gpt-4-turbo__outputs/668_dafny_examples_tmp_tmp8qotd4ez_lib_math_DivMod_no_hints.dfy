module DivMod {

  function {:opaque} DivSub(a: int, b: int): int
    requires 0 <= a && 0 < b
  {
    if a < b then 0 else 1 + DivSub(a - b, b)
  }

  function {:opaque} ModSub(a: int, b: int): int
    requires 0 <= a && 0 < b
  {
    if a < b then a else ModSub(a - b, b)
  }

  lemma DivModAdd1(a: int, b: int)
    requires b != 0
    ensures (a + b) % b == a % b
    ensures (a + b) / b == a / b + 1
  {
    reveal ModSub();
    reveal DivSub();
    assert (a + b) % b == a % b;
    assert (a + b) / b == a / b + 1;
  }

  lemma DivModSub1(a: int, b: int)
    requires b != 0
    ensures (a - b) % b == a % b
    ensures (a - b) / b == a / b - 1
  {
    reveal ModSub();
    reveal DivSub();
    assert (a - b) % b == a % b;
    assert (a - b) / b == a / b - 1;
  }

  lemma ModEq(a: int, b: int)
    requires 0 <= a && 0 < b
    ensures a % b == ModSub(a, b)
  {
    reveal ModSub();
    if a >= b {
      ModEq(a - b, b);
      assert a % b == ModSub(a - b, b);
    } else {
      assert a % b == a;
    }
  }

  lemma DivEq(a: int, b: int)
    requires 0 <= a && 0 < b
    ensures a / b == DivSub(a, b)
  {
    reveal DivSub();
    if a >= b {
      DivEq(a - b, b);
      assert a / b == 1 + DivSub(a - b, b);
    } else {
      assert a / b == 0;
    }
  }

  lemma DivModSpec'(a: int, b: int, q: int, r: int)
    requires 0 <= a && 0 < b
    requires 0 <= q && 0 <= r < b
    requires a == q * b + r
    ensures ModSub(a, b) == r
    ensures DivSub(a, b) == q
  {
    reveal ModSub();
    reveal DivSub();
    if q > 0 {
      DivModSpec'(a - b, b, q - 1, r);
      assert ModSub(a, b) == ModSub(a - b, b);
      assert DivSub(a, b) == 1 + DivSub(a - b, b);
    } else {
      assert ModSub(a, b) == r;
      assert DivSub(a, b) == q;
    }
  }

  lemma DivModSpec(a: int, b: int, q: int, r: int)
    requires 0 <= a && 0 < b
    requires 0 <= q && 0 <= r < b
    requires a == q * b + r
    ensures a % b == r
    ensures a / b == q
  {
    ModEq(a, b);
    DivEq(a, b);
    DivModSpec'(a, b, q, r);
  }

  lemma DivMul(a: int, b: int)
    requires 0 <= a && 0 < b
    ensures a * b / b == a
  {
    DivModSpec(a * b, b, a, 0);
  }

  lemma DivModMulAdd(a: int, b: int, c: int)
    requires 0 <= a && 0 <= c < b && 0 < b
    ensures (a * b + c) / b == a
    ensures (a * b + c) % b == c
  {
    DivModSpec(a * b + c, b, a, c);
  }

}