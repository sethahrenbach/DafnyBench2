module DafnyVersion {
  datatype Pair = Pair(x: int, y: int)

  function pair_x(p: Pair): int
    reads p
    ensures result == p.x
  {
    p.x
  }

  function pair_y(p: Pair): int
    reads p
    ensures result == p.y
  {
    p.y
  }

  lemma UsePair() {
    var p := Pair(1, 2);
  }
}

module Encoding {

  type Pair(==)

  function pair(x: int, y: int): Pair
    ensures pair_x(result) == x && pair_y(result) == y
  {
    Pair(x, y)
  }

  function pair_x(p: Pair): int
    reads p
    ensures result == p.x
  {
    p.x
  }

  function pair_y(p: Pair): int
    reads p
    ensures result == p.y
  {
    p.y
  }

  lemma {:axiom} x_defn()
    ensures forall x, y :: pair_x(pair(x, y)) == x

  lemma {:axiom} y_defn()
    ensures forall x, y :: pair_y(pair(x, y)) == y

  lemma {:axiom} bijection()
    ensures forall p:Pair :: pair(pair_x(p), pair_y(p)) == p

  lemma UseEncoding() 
    ensures true
  {
    x_defn();
    y_defn();
    bijection();

    assert forall p1, p2 :: pair_x(p1) == pair_x(p2) && pair_y(p1) == pair_y(p2) ==> p1 == p2;
    {
      bijection();
    }
  }

}
