
// RUN: %testDafnyForEachResolver "%s" -- --warn-deprecation:false

// ----- Stream

codatatype Stream<T> = Nil | Cons(head: T, tail: Stream<T>);

ghost function append<T>(M: Stream<T>, N: Stream<T>): Stream<T>
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
lemma Theorem0(M: Stream<X>)
  ensures map_fg(M) == map_f(map_g(M))
{
  match M {
    case Nil =>
    case Cons(x, N) =>
      Theorem0(N);
  }
}

// map f (append M N) = append (map f M) (map f N)
lemma Theorem1(M: Stream<X>, N: Stream<X>)
  ensures map_f(append(M, N)) == append(map_f(M), map_f(N))
{
  match M {
    case Nil =>
    case Cons(x, M') =>
      Theorem1(M', N);
  }
}

// append Nil M = M
lemma Theorem2(M: Stream<X>)
  ensures append(Nil, M) == M
{
}

// append M Nil = M
lemma Theorem3(M: Stream<X>)
  ensures append(M, Nil) == M
{
  match M {
    case Nil =>
    case Cons(x, N) =>
      Theorem3(N);
  }
}

// append M (append N P) = append (append M N) P
lemma Theorem4(M: Stream<X>, N: Stream<X>, P: Stream<X>)
  ensures append(M, append(N, P)) == append(append(M, N), P)
{
  match M {
    case Nil =>
    case Cons(x, M') =>
      Theorem4(M', N, P);
  }
}
