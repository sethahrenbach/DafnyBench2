// RUN: %dafny /compile:0 /rprint:"%t.rprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Monadic Laws
// Niki Vazou and Rustan Leino
// 28 March 2016

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function append<T>(xs: List<T>, ys: List<T>): List<T>
{
  match xs
  case Nil => ys
  case Cons(x, xs') => Cons(x, append(xs', ys))
}

lemma AppendNil<T>(xs: List<T>)
  ensures append(xs, Nil) == xs
{
  match xs
  case Nil =>
  case Cons(x, xs') =>
    AppendNil(xs');
}

lemma AppendAssoc<T>(xs: List<T>, ys: List<T>, zs: List<T>)
  ensures append(append(xs, ys), zs) == append(xs, append(ys, zs))
{
  match xs
  case Nil =>
  case Cons(x, xs') =>
    AppendAssoc(xs', ys, zs);
}

function Return<T>(a: T): List<T>
{
  Cons(a, Nil)
}

function Bind<T,U>(xs: List<T>, f: T -> List<U>): List<U>
{
  match xs
  case Nil => Nil
  case Cons(x, xs') => append(f(x), Bind(xs', f))
}

lemma LeftIdentity<T>(a: T, f: T -> List<T>)
  ensures Bind(Return(a), f) == f(a)
{
  AppendNil(f(a));
}

lemma RightIdentity<T>(m: List<T>)
  ensures Bind(m, Return) == m
{
  match m
  case Nil =>
  case Cons(x, m') =>
    RightIdentity(m');
    assert Bind(m', Return) == m';
    calc {
      Bind(Cons(x, m'), Return);
      append(Return(x), Bind(m', Return));
      append(Return(x), m');
      Cons(x, m');
    }
}

lemma Associativity<T>(m: List<T>, f: T -> List<T>, g: T -> List<T>)
  ensures Bind(Bind(m, f), g) == Bind(m, x => Bind(f(x), g))
{
  match m
  case Nil =>
  case Cons(x, xs) =>
    Associativity(xs, f, g);
    match f(x)
    case Nil =>
      calc {
        Bind(Bind(Cons(x, xs), f), g);
        Bind(append(f(x), Bind(xs, f)), g);
        Bind(append(Nil, Bind(xs, f)), g);
        Bind(Bind(xs, f), g);
        Bind(xs, y => Bind(f(y), g));
        Bind(Cons(x, xs), y => Bind(f(y), g));
      }
    case Cons(y, ys) =>
      BindOverAppend(ys, Bind(xs, f), g);
      AppendAssoc(g(y), Bind(ys, g), Bind(Bind(xs, f), g));
      calc {
        Bind(Bind(Cons(x, xs), f), g);
        Bind(append(f(x), Bind(xs, f)), g);
        Bind(append(Cons(y, ys), Bind(xs, f)), g);
        append(g(y), Bind(append(ys, Bind(xs, f)), g));
        append(g(y), append(Bind(ys, g), Bind(Bind(xs, f), g)));
        append(append(g(y), Bind(ys, g)), Bind(Bind(xs, f), g));
        Bind(Cons(x, xs), z => Bind(f(z), g));
      }
}

lemma BindOverAppend<T>(xs: List<T>, ys: List<T>, g: T -> List<T>)
  ensures Bind(append(xs, ys), g) == append(Bind(xs, g), Bind(ys, g))
{
  match xs
  case Nil =>
    calc {
      Bind(append(Nil, ys), g);
      Bind(ys, g);
      append(Bind(Nil, g), Bind(ys, g));
      append(Nil, Bind(ys, g));
      Bind(ys, g);
    }
  case Cons(x, xs') =>
    BindOverAppend(xs', ys, g);
    assert Bind(append(xs', ys), g) == append(Bind(xs', g), Bind(ys, g));
    AppendAssoc(g(x), Bind(xs', g), Bind(ys, g));
    calc {
      Bind(append(Cons(x, xs'), ys), g);
      Bind(Cons(x, append(xs', ys)), g);
      append(g(x), Bind(append(xs', ys), g));
      append(g(x), append(Bind(xs', g), Bind(ys, g)));
      append(append(g(x), Bind(xs', g)), Bind(ys, g));
      append(Bind(Cons(x, xs'), g), Bind(ys, g));
    }
}