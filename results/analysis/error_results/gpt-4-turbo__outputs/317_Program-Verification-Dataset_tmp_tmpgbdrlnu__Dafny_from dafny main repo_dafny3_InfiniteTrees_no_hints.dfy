// RUN: %dafny /compile:0 /deprecation:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

// Here is the usual definition of possibly infinite lists, along with a function Tail(s, n), which drops
// n heads from s, and two lemmas that prove properties of Tail.

codatatype Stream<T> = Nil | Cons(head: T, tail: Stream<T>)

ghost function Tail<T>(s: Stream<T>, n: nat): Stream<T>
{
  if n == 0 then s else
    var t := Tail(s, n-1);
    if t == Nil then t else t.tail
}

lemma Tail_Lemma0<T>(s: Stream<T>, n: nat)
  requires s.Cons? && Tail(s, n).Cons?;
  ensures Tail(s, n).tail == Tail(s.tail, n);
{
}

lemma Tail_Lemma1<T>(s: Stream<T>, k: nat, n: nat)
  requires k <= n;
  ensures Tail(s, n).Cons? ==> Tail(s, k).Cons?;
{
  if k < n && Tail(s, n).Cons? {
    Tail_Lemma1(s, k+1, n);
  }
}

lemma Tail_Lemma2<T>(s: Stream<T>, n: nat)
  requires s.Cons? && Tail(s.tail, n).Cons?;
  ensures Tail(s, n).Cons?;
{
  if n != 0 {
    Tail_Lemma0(s, n-1);
    Tail_Lemma2(s.tail, n-1);
  }
}

// Co-predicate IsNeverEndingStream(s) answers whether or not s ever contains Nil.

greatest predicate IsNeverEndingStream<T>(s: Stream<T>)
{
  match s
  case Nil => false
  case Cons(_, tail) => IsNeverEndingStream(tail)
}

// Here is an example of an infinite stream.

ghost function AnInfiniteStream(): Stream<int>
{
  Cons(0, AnInfiniteStream())
}
greatest lemma Proposition0()
  ensures IsNeverEndingStream(AnInfiniteStream());
{
}

// Now, consider a Tree definition, where each node can have a possibly infinite number of children.

datatype Tree = Node(children: Stream<Tree>)

// Such a tree might have not just infinite width but also infinite height.  The following predicate
// holds if there is, for every path down from the root, a common bound on the height of each such path.
// Note that the definition needs a co-predicate in order to say something about all of a node's children.

ghost predicate HasBoundedHeight(t: Tree)
{
  exists n :: 0 <= n && LowerThan(t.children, n)
}
greatest predicate LowerThan(s: Stream<Tree>, n: nat)
{
  match s
  case Nil => true
  case Cons(t, tail) =>
    1 <= n && LowerThan(t.children, n-1) && LowerThan(tail, n)
}

// Co-predicate LowerThan(s, n) recurses on LowerThan(s.tail, n).  Thus, a property of LowerThan is that
// LowerThan(s, h) implies LowerThan(s', h) for any suffix s' of s.

lemma LowerThan_Lemma(s: Stream<Tree>, n: nat, h: nat)
  ensures LowerThan(s, h) ==> LowerThan(Tail(s, n), h);
{
  if n == 0 {
    assert LowerThan(s, h);
  } else {
    match s {
      case Nil =>
        assert LowerThan(Tail(s, n), h);
      case Cons(t, tail) =>
        assert LowerThan(tail, h);
        LowerThan_Lemma(tail, n-1, h);
        assert LowerThan(Tail(tail, n-1), h);
        assert Tail(s, n) == Tail(tail, n-1);
        assert LowerThan(Tail(s, n), h);
    }
  }
}

// A tree t where every node has an infinite number of children satisfies InfiniteEverywhere(t.children).
// Otherwise, IsFiniteSomewhere(t) holds.  That is, IsFiniteSomewhere says that the tree has some node
// with less than infinite width.  Such a tree may or may not be of finite height, as we'll see in an
// example below.

ghost predicate IsFiniteSomewhere(t: Tree)
{
  !InfiniteEverywhere(t.children)
}
greatest predicate InfiniteEverywhere(s: Stream<Tree>)
{
  match s
  case Nil => false
  case Cons(t, tail) => InfiniteEverywhere(t.children) && InfiniteEverywhere(tail)
}

// Here is a tree where every node has exactly 1 child.  Such a tree is finite in width (which implies
// it is finite somewhere) and infinite in height (which implies there is no bound on its height).

ghost function SkinnyTree(): Tree
{
  Node(Cons(SkinnyTree(), Nil))
}
lemma Proposition1()
  ensures IsFiniteSomewhere(SkinnyTree()) && !HasBoundedHeight(SkinnyTree());
{
}

// Any tree where all paths have bounded height are finite somewhere.

lemma Theorem0(t: Tree)
  requires HasBoundedHeight(t);
  ensures IsFiniteSomewhere(t);
{
  var n :| 0 <= n && LowerThan(t.children, n);
  var k: nat;
  FindNil(t.children, n, out k);
  assert !InfiniteEverywhere(Tail(t.children, k));
}

lemma FindNil(s: Stream<Tree>, n: nat, out k: nat)
  requires LowerThan(s, n);
  ensures !InfiniteEverywhere(Tail(s, k));
{
  if s == Nil {
    k := 0;
  } else {
    match s {
      case Nil => k := 0;
      case Cons(t, tail) =>
        if n == 0 {
          k := 0;
        } else {
          FindNil(tail, n-1, out k);
          k := k + 1;
        }
    }
  }
}