
// RUN: %dafny /compile:0 /deprecation:0 /proverOpt:O:smt.qi.eager_threshold=30 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// This is the Extractor Problem from section 11.8 of the ACL2 book,
// "Computer-Aided Reasoning: An Approach" by Kaufmann, Manolios, and
// Moore (2011 edition).

datatype List<T> = Nil | Cons(head: T, tail: List<T>)

ghost function length<T>(xs: List<T>): nat
{
  match xs
  case Nil => 0
  case Cons(_, rest) => 1 + length(rest)
}

// If "0 <= n < length(xs)", then return the element of "xs" that is preceded by
// "n" elements; otherwise, return an arbitrary value.
ghost opaque function nth<T>(n: int, xs: List<T>): T
{
  if 0 <= n < length(xs) then
    nthWorker(n, xs)
  else
    var t :| true; t
}

ghost function nthWorker<T>(n: int, xs: List<T>): T
  requires 0 <= n < length(xs);
{
  if n == 0 then xs.head else nthWorker(n-1, xs.tail)
}

ghost function append<T>(xs: List<T>, ys: List<T>): List<T>
{
  match xs
  case Nil => ys
  case Cons(x, rest) => Cons(x, append(rest, ys))
}

ghost function rev<T>(xs: List<T>): List<T>
{
  match xs
  case Nil => Nil
  case Cons(x, rest) => append(rev(rest), Cons(x, Nil))
}

ghost function nats(n: nat): List<int>
{
  if n == 0 then Nil else Cons(n-1, nats(n-1))
}

ghost function xtr<T>(mp: List<int>, lst: List<T>): List<T>
{
  match mp
  case Nil => Nil
  case Cons(n, rest) => Cons(nth(n, lst), xtr(rest, lst))
}

lemma ExtractorTheorem<T>(xs: List<T>)
  ensures xtr(nats(length(xs)), xs) == rev(xs);
{
  var a := xtr(nats(length(xs)), xs);
  var b := rev(xs);
  assert length(a) == length(b) by {
    XtrLength(nats(length(xs)), xs);
    RevLength(xs);
  };
  forall i | 0 <= i < length(xs)
    ensures nth(i, a) == nth(i, b)
  {
    ExtractorLemma(i, xs);
  }
}

// auxiliary lemmas and proofs follow

lemma XtrLength<T>(mp: List<int>, lst: List<T>)
  ensures length(xtr(mp, lst)) == length(mp);
{
}

lemma NatsLength(n: nat)
  ensures length(nats(n)) == n;
{
}

lemma AppendLength<T>(xs: List<T>, ys: List<T>)
  ensures length(append(xs, ys)) == length(xs) + length(ys);
{
}

lemma RevLength<T>(xs: List<T>)
  ensures length(rev(xs)) == length(xs);
{
  match xs {
    case Nil =>
    case Cons(x, rest) =>
      RevLength(rest);
      AppendLength(rev(rest), Cons(x, Nil));
  }
}

lemma EqualElementsMakeEqualLists<T>(xs: List<T>, ys: List<T>)
  requires length(xs) == length(ys)
  requires forall i :: 0 <= i < length(xs) ==> nth(i, xs) == nth(i, ys)
  ensures xs == ys
{
}

lemma ExtractorLemma<T>(i: int, xs: List<T>)
  requires 0 <= i < length(xs);
  ensures nth(i, xtr(nats(length(xs)), xs)) == nth(i, rev(xs));
{
  var natList := nats(length(xs));
  var xtrList := xtr(natList, xs);
  var revList := rev(xs);
  var indexInNatList := nth(i, natList);
  var elementInXtrList := nth(i, xtrList);
  var elementInRevList := nth(i, revList);
  assert elementInXtrList == nth(indexInNatList, xs);
  assert elementInRevList == nth(length(xs) - 1 - i, xs);
  assert indexInNatList == length(xs) - 1 - i;
}
