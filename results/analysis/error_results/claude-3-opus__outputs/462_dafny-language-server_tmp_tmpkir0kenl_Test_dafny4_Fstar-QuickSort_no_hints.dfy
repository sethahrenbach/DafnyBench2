// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// A Dafny rendition of an F* version of QuickSort (included at the bottom of this file).
// Unlike the F* version, Dafny also proves termination and does not use any axioms.  However,
// Dafny needs help with a couple of lemmas in places where F* does not need them.
// Comments below show differences between the F* and Dafny versions.

datatype List<T> = Nil | Cons(T, List)

function length(list: List): nat  // for termination proof
{
  match list
  case Nil => 0
  case Cons(_, tl) => 1 + length(tl)
}

// In(x, list) returns the number of occurrences of x in list
function In(x: int, list: List<int>): nat
{
  match list
  case Nil => 0
  case Cons(y, tl) => (if x == y then 1 else 0) + In(x, tl)
}

predicate SortedRange(m: int, n: int, list: List<int>)
{
  match list
  case Nil => m <= n
  case Cons(hd, tl) => m <= hd <= n && SortedRange(hd, n, tl)
}

function append(n0: int, n1: int, n2: int, n3: int, i: List<int>, j: List<int>): List<int>
  requires n0 <= n1 <= n2 <= n3
  requires SortedRange(n0, n1, i) && SortedRange(n2, n3, j)
  ensures SortedRange(n0, n3, append(n0, n1, n2, n3, i, j))
  ensures forall x :: In(x, append(n0, n1, n2, n3, i, j)) == In(x, i) + In(x, j)
  decreases length(i)
{
  match i
  case Nil => 
    assert SortedRange(n2, n3, j);
    j
  case Cons(hd, tl) => 
    assert n0 <= hd <= n1;
    assert SortedRange(hd, n1, tl);
    assert SortedRange(n2, n3, j);
    Cons(hd, append(hd, n1, n2, n3, tl, j))
}

function partition(x: int, l: List<int>): (List<int>, List<int>)
  ensures var (lo, hi) := partition(x, l);
    (forall y :: In(y, lo) == if y <= x then In(y, l) else 0) &&
    (forall y :: In(y, hi) == if x < y then In(y, l) else 0) &&
    length(l) == length(lo) + length(hi)  // for termination proof
  decreases length(l)
{
  match l
  case Nil => (Nil, Nil)
  case Cons(hd, tl) =>
    var (lo, hi) := partition(x, tl);
    if hd <= x then
      (Cons(hd, lo), hi)
    else
      (lo, Cons(hd, hi))
}

lemma in_bounds_lemma(min: int, max: int, i: List<int>)
  requires forall x :: In(x, i) != 0 ==> min <= x <= max
  ensures forall x :: In(x, i) != 0 ==> min <= x < max
{
}

function sort(min: int, max: int, i: List<int>): List<int>
  requires min <= max
  requires forall x :: In(x, i) != 0 ==> min <= x <= max
  ensures SortedRange(min, max, sort(min, max, i))
  ensures forall x :: In(x, i) == In(x, sort(min, max, i))
  decreases length(i), max - min
{
  match i
  case Nil => Nil
  case Cons(hd, tl) =>
    var (lo, hi) := partition(hd, tl);
    assert forall y :: In(y, lo) == if y <= hd then In(y, tl) else 0;
    assert forall y :: In(y, hi) == if hd < y then In(y, tl) else 0;
    assert length(tl) == length(lo) + length(hi);
    
    assert forall x :: In(x, lo) != 0 ==> min <= x <= hd;
    var i' := sort(min, hd, lo);
    assert SortedRange(min, hd, i');
    assert forall x :: In(x, lo) == In(x, i');
    
    assert forall x :: In(x, hi) != 0 ==> hd < x <= max;
    var j' := sort(hd+1, max, hi);
    assert SortedRange(hd+1, max, j');
    assert forall x :: In(x, hi) == In(x, j');
    
    assert SortedRange(min, hd, i');
    assert SortedRange(hd, max, Cons(hd, j'));
    assert forall x :: In(x, i') + In(x, Cons(hd, j')) == In(x, lo) + (if x == hd then 1 else 0) + In(x, hi);
    assert forall x :: In(x, lo) + (if x == hd then 1 else 0) + In(x, hi) == In(x, i);
    append(min, hd, hd, max, i', Cons(hd, j'))
}
