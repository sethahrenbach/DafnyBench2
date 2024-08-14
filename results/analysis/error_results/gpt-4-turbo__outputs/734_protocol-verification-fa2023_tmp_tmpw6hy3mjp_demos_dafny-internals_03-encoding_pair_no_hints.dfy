
module DafnyVersion {
  datatype Pair = Pair(x: int, y: int)

  function pair_x(p: Pair): int {
    p.x
  }

  function pair_y(p: Pair): int {
    p.y
  }

  lemma UsePair() {
    var p := Pair(1, 2);
    assert pair_x(p) == 1;
    assert pair_y(p) == 2;
  }
}

module Encoding {
  type Pair

  function pair(x: int, y: int): Pair
  function pair_x(p: Pair): int
  function pair_y(p: Pair): int

  lemma {:axiom} x_defn()
    ensures forall x: int, y: int :: pair_x(pair(x, y)) == x
  {}

  lemma {:axiom} y_defn()
    ensures forall x: int, y: int :: pair_y(pair(x, y)) == y
  {}

  lemma {:axiom} bijection()
    ensures forall p: Pair :: pair(pair_x(p), pair_y(p)) == p
  {}

  lemma UseEncoding() {
    var p1 := pair(1, 2);
    var p2 := pair(1, 2);

    x_defn();
    y_defn();
    bijection();

    assert pair_x(p1) == 1;
    assert pair_y(p1) == 2;
    assert pair_x(p2) == 1;
    assert pair_y(p2) == 2;

    assert p1 == p2 by {
      x_defn();
      y_defn();
      bijection();
    };
  }
}
