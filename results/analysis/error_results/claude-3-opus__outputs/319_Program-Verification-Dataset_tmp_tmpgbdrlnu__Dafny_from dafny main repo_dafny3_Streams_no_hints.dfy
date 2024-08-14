// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false


// ----- Stream

codatatype Stream<T> = Nil | Cons(head: T, tail: Stream)

ghost function append(M: Stream, N: Stream): Stream
{
  match M
  case Nil => N
  case Cons(t, M') => Cons(t, append(M', N))
}

// ----- f, g, and maps

type X

ghost function f(x: X): X
ghost function g(x: X): X

ghost function map_f(M: Stream<X>): Stream<X>
{
  match M
  case Nil => Nil
  case Cons(x, N) => Cons(f(x), map_f(N))
}

ghost function map_g(M: Stream<X>): Stream<X>
{
  match M
  case Nil => Nil
  case Cons(x, N) => Cons(g(x), map_g(N))
}

ghost function map_fg(M: Stream<X>): Stream<X>
{
  match M
  case Nil => Nil
  case Cons(x, N) => Cons(f(g(x)), map_fg(N))
}

// ----- Theorems

// map (f * g) M = map f (map g M)
greatest lemma Theorem0(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M));
{
  match (M) {
    case Nil =>
    case Cons(x, N) =>
      assert map_fg(M) == Cons(f(g(x)), map_fg(N));
      assert map_g(M) == Cons(g(x), map_g(N));
      assert map_f(map_g(M)) == Cons(f(g(x)), map_f(map_g(N)));
      Theorem0(N);
  }
}
greatest lemma Theorem0_Alt(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M));
{
  if (M.Cons?) {
    assert map_fg(M) == Cons(f(g(M.head)), map_fg(M.tail));
    assert map_g(M) == Cons(g(M.head), map_g(M.tail));
    assert map_f(map_g(M)) == Cons(f(g(M.head)), map_f(map_g(M.tail)));
    Theorem0_Alt(M.tail);
  }
}
lemma Theorem0_Par(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M));
{
  forall k: nat 
    ensures map_fg(M) ==#[k] map_f(map_g(M));
  {
    Theorem0_Ind(k, M);
  }
}
lemma Theorem0_Ind(k: nat, M: Stream<X>)
  ensures map_fg(M) ==#[k] map_f(map_g(M));
{
  if (k != 0) {
    match (M) {
      case Nil =>
      case Cons(x, N) =>
        assert map_fg(M) ==#[k] Cons(f(g(x)), map_fg(N));
        assert map_g(M) ==#[k] Cons(g(x), map_g(N));
        assert map_f(map_g(M)) ==#[k] Cons(f(g(x)), map_f(map_g(N)));
        Theorem0_Ind(k-1, N);
    }
  }
}
lemma Theorem0_AutoInd(k: nat, M: Stream<X>)
  ensures map_fg(M) ==#[k] map_f(map_g(M));
{
  if (k != 0 && M.Cons?) {
    Theorem0_AutoInd(k-1, M.tail);
  }
}

// map f (append M N) = append (map f M) (map f N)
greatest lemma Theorem1(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N));
{
  match (M) {
    case Nil =>
      assert map_f(append(M, N)) == map_f(N);
      assert append(map_f(M), map_f(N)) == map_f(N);
    case Cons(x, M') =>
      assert map_f(append(M, N)) == Cons(f(x), map_f(append(M', N)));
      assert append(map_f(M), map_f(N)) == Cons(f(x), append(map_f(M'), map_f(N)));
      Theorem1(M', N);
  }
}
greatest lemma Theorem1_Alt(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N));
{
  if (M.Cons?) {
    assert map_f(append(M, N)) == Cons(f(M.head), map_f(append(M.tail, N)));
    assert append(map_f(M), map_f(N)) == Cons(f(M.head), append(map_f(M.tail), map_f(N)));
    Theorem1_Alt(M.tail, N);
  }
}
lemma Theorem1_Par(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N));
{
  forall k: nat
    ensures map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N));
  {
    Theorem1_Ind(k, M, N);
  }
}
lemma Theorem1_Ind(k: nat, M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N));
{
  match (M) {
    case Nil =>
      assert map_f(append(M, N)) ==#[k] map_f(N);
      assert append(map_f(M), map_f(N)) ==#[k] map_f(N);
    case Cons(x, M') =>
      if (k != 0) {
        assert map_f(append(M, N)) ==#[k] Cons(f(x), map_f(append(M', N)));
        assert append(map_f(M), map_f(N)) ==#[k] Cons(f(x), append(map_f(M'), map_f(N)));
        Theorem1_Ind(k-1, M', N);
      }
  }
}
lemma Theorem1_AutoInd(k: nat, M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) ==#[k] append(map_f(M), map_f(N));
{
  if (k != 0 && M.Cons?) {
    Theorem1_AutoInd(k-1, M.tail, N);
  }
}

// append NIL M = M
lemma Theorem2(M: Stream<X>)
  ensures append(Nil, M) == M;
{
  // trivial
}

// append M NIL = M
greatest lemma Theorem3(M: Stream<X>)
  ensures append(M, Nil) == M;
{
  match (M) {
    case Nil =>
    case Cons(x, N) =>
      assert append(M, Nil) == Cons(x, append(N, Nil));
      Theorem3(N);
  }
}
greatest lemma Theorem3_Alt(M: Stream<X>)
  ensures append(M, Nil) == M;
{
  if (M.Cons?) {
    assert append(M, Nil) == Cons(M.head, append(M.tail, Nil));
    Theorem3_Alt(M.tail);
  }
}

// append M (append N P) = append (append M N) P
greatest lemma Theorem4(M: Stream<X>, N: Stream<X>, P: Stream<X>)
  ensures append(M, append(N, P)) == append(append(M, N), P);
{
  match (M) {
    case Nil =>
      assert append(M, append(N, P)) == append(N, P);
      assert append(append(M, N), P) == append(N, P);
    case Cons(x, M') =>
      assert append(M, append(N, P)) == Cons(x, append(M', append(N, P)));
      assert append(append(M, N), P) == Cons(x, append(append(M', N), P));
      Theorem4(M', N, P);
  }
}
greatest lemma Theorem4_Alt(M: Stream<X>, N: Stream<X>, P: Stream<X>)
  ensures append(M, append(N, P)) == append(append(M, N), P);
{
  if (M.Cons?) {
    assert append(M, append(N, P)) == Cons(M.head, append(M.tail, append(N, P)));
    assert append(append(M, N), P) == Cons(M.head, append(append(M.tail, N), P));
    Theorem4_Alt(M.tail, N, P);
  }
}

// ----- Flatten

greatest predicate StreamOfNonEmpties(M: Stream<Stream>)
{
  match M
  case Nil => true
  case Cons(s, N) => s.Cons? && StreamOfNonEmpties(N)
}

ghost function FlattenStartMarker<T>(M: Stream<Stream>, startMarker: T): Stream
{
  PrependThenFlattenStartMarker(Nil, M, startMarker)
}

ghost function PrependThenFlattenStartMarker<T>(prefix: Stream, M: Stream<Stream>, startMarker: T): Stream
{
  match prefix
  case Cons(hd, tl) =>
    Cons(hd, PrependThenFlattenStartMarker(tl, M, startMarker))
  case Nil =>
    match M
    case Nil => Nil
    case Cons(s, N) => Cons(startMarker, PrependThenFlattenStartMarker(s, N, startMarker))
}

ghost function FlattenNonEmpties(M: Stream<Stream>): Stream
  requires StreamOfNonEmpties(M);
{
  PrependThenFlattenNonEmpties(Nil, M)
}

ghost function PrependThenFlattenNonEmpties(prefix: Stream, M: Stream<Stream>): Stream
  requires StreamOfNonEmpties(M);
{
  match prefix
  case Cons(hd, tl) =>
    Cons(hd, PrependThenFlattenNonEmpties(tl, M))
  case Nil =>
    match M
    case Nil => Nil
    case Cons(s, N) => Cons(s.head, PrependThenFlattenNonEmpties(s.tail, N))
}

ghost function Prepend<T>(x: T, M: Stream<Stream>): Stream<Stream>
{
  match M
  case Nil => Nil
  case Cons(s, N) => Cons(Cons(x, s), Prepend(x, N))
}

greatest lemma Prepend_Lemma<T>(x: T, M: Stream<Stream>)
  ensures StreamOfNonEmpties(Prepend(x, M));
{
  match M {
    case Nil =>
    case Cons(s, N) =>
      assert Prepend(x, M).head == Cons(x, s);
      assert Prepend(x, M).tail == Prepend(x, N);
      Prepend_Lemma(x, N);
  }
}

lemma Theorem_Flatten<T>(M: Stream<Stream>, startMarker: T)
  ensures
    StreamOfNonEmpties(Prepend(startMarker, M)) ==> // always holds, on account of Prepend_Lemma;
                                          // but until (co-)method can be called from functions,
                                          // this condition is used as an antecedent here
    FlattenStartMarker(M, startMarker) == FlattenNonEmpties(Prepend(startMarker, M));
{
  Prepend_Lemma(startMarker, M);
  Lemma_Flatten(Nil, M, startMarker);
}

greatest lemma Lemma_Flatten<T>(prefix: Stream, M: Stream<Stream>, startMarker: T)
  ensures
    StreamOfNonEmpties(Prepend(startMarker, M)) ==> // always holds, on account of Prepend_Lemma;
                                          // but until (co-)method can be called from functions,
                                          // this condition is used as an antecedent here
    PrependThenFlattenStartMarker(prefix, M, startMarker) == PrependThenFlattenNonEmpties(prefix, Prepend(startMarker, M));
{
  Prepend_Lemma(startMarker, M);
  match (prefix) {
    case Cons(hd, tl) =>
      assert PrependThenFlattenStartMarker(prefix, M, startMarker) == Cons(hd, PrependThenFlattenStartMarker(tl, M, startMarker));
      assert PrependThenFlattenNonEmpties(prefix, Prepend(startMarker, M)) == Cons(hd, PrependThenFlattenNonEmpties(tl, Prepend(startMarker, M)));
      Lemma_Flatten(tl, M, startMarker);
    case Nil =>
      match (M) {
        case Nil =>
        case Cons(s, N) =>
          assert PrependThenFlattenStartMarker(prefix, M, startMarker) == Cons(startMarker, PrependThenFlattenStartMarker(s, N, startMarker));
          assert PrependThenFlattenNonEmpties(prefix, Prepend(startMarker, M)) == Cons(startMarker, PrependThenFlattenNonEmpties(s, Prepend(startMarker, N)));
          Lemma_Flatten(s, N, startMarker);
      }
  }
}

greatest lemma Lemma_FlattenAppend0<T>(s: Stream, M: Stream<Stream>, startMarker: T)
  ensures PrependThenFlattenStartMarker(s, M, startMarker) == append(s, PrependThenFlattenStartMarker(Nil, M, startMarker));
{
  match (s) {
    case Nil =>
    case Cons(hd, tl) =>
      assert PrependThenFlattenStartMarker(s, M, startMarker) == Cons(hd, PrependThenFlattenStartMarker(tl, M, startMarker));
      assert append(s, PrependThenFlattenStartMarker(Nil, M, startMarker)) == Cons(hd, append(tl, PrependThenFlattenStartMarker(Nil, M, startMarker)));
      Lemma_FlattenAppend0(tl, M, startMarker);
  }
}

greatest lemma Lemma_FlattenAppend1<T>(s: Stream, M: Stream<Stream>)
  requires StreamOfNonEmpties(M);
  ensures PrependThenFlattenNonEmpties(s, M) == append(s, PrependThenFlattenNonEmpties(Nil, M));
{