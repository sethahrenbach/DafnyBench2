// RUN: %testDafnyForEachCompiler --refresh-exit-code=0 "%s" -- --relax-definite-assignment

class List<T> {
  ghost var Contents: seq<T>
  ghost var Repr: set<object>

  var a: array<T>
  var n: nat

  ghost predicate Valid()
    reads this, Repr
    ensures Valid() ==> this in Repr
  {
    this in Repr &&
    a in Repr &&
    n <= a.Length &&
    Contents == a[..n]
  }

  constructor Init()
    ensures Valid() && fresh(Repr)
    ensures Contents == []
  {
    Contents, n := [], 0;
    a := new T[0];
    Repr := {this, a};
  }

  method Add(t: T)
    requires Valid()
    modifies Repr
    ensures Valid() && fresh(Repr - old(Repr))
    ensures Contents == old(Contents) + [t]
  {
    if (n == a.Length) {
      var b := new T[2 * a.Length + 1](i requires 0 <= i < a.Length => a[i]);
      a, Repr := b, Repr + {b};
    }
    a[n], n, Contents := t, n + 1, Contents + [t];
  }
}

class Cell { var data: int }

iterator M<T(0)>(l: List<T>, c: Cell) yields (x: T)
  requires l.Valid()
  reads l.Repr
  modifies c
  yield requires true
  yield ensures xs <= l.Contents  // this is needed in order for the next line to be well-formed
  yield ensures x == l.Contents[|xs|-1]
  ensures xs == l.Contents
{
  var i := 0;
  while i < l.n
    invariant 0 <= i <= l.n
    invariant forall j | 0 <= j < i :: l.a[j] == l.Contents[j]
    invariant xs == l.Contents[..i]
  {
    if (true) { assert l.Valid(); }  // this property is maintained, due to the reads clause
    if (i < l.n) {
      x := l.a[i]; yield;  // or, equivalently, 'yield l.a[i]'
      i := i + 1;
    } else {
      x, i := l.a[i], i + 1;
      yield;
    }
  }
}

method Client<T(==,0)>(l: List, stop: T) returns (s: seq<T>)
  requires l.Valid()
{
  var c := new Cell;
  var iter := new M(l, c);
  s := [];
  while true
    invariant s == iter.xs
    decreases l.n
  {
    var more := iter.MoveNext();
    if (!more) { break; }
    s := s + [iter.x];
    if (iter.x == stop) { return s; }  // if we ever see 'stop', then just end
  }
}

method PrintSequence<T>(s: seq<T>)
{
  var i := 0;
  while i < |s|
  {
    print s[i], " ";
    i := i + 1;
  }
  print "\n";
}

method Main()
{
  var myList := new List.Init();
  var i := 0;
  while i < 100
    invariant myList.Valid()
  {
    myList.Add(i);
    i := i + 2;
  }
  var s := Client(myList, 89);
  PrintSequence(s);
  s := Client(myList, 14);
  PrintSequence(s);
}