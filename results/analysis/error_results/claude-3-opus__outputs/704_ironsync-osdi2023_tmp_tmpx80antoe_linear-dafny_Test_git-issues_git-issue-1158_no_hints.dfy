// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Id(==)

function F(s: set<Id>): int

lemma Test(x: Id)
{
  var X := {x};
  var a := map i | i <= X :: F(i);
  var b := map[{} := F({}), X := F(X)];

  forall i
    ensures i in a.Keys <==> i in b.Keys
  {
    calc {
      i in a.Keys;
    ==  // definition of a
      i <= X;
    ==  { SubsetProperties(i, X); }
      i == {} || i == X;
    ==  { SetEquivalence(i, b); }
      i in b.Keys;
    }
  }
}

lemma SubsetProperties(i: set<Id>, X: set<Id>)
  ensures i <= X <==> i == {} || i == X
{
  if i <= X {
    if i != {} && i != X {
      assert i < X;
      assert i != X;  // contradiction
    }
  }
}

lemma SetEquivalence(i: set<Id>, b: map<set<Id>, int>)
  requires i == {} || i == b.Keys[1]
  ensures i in b.Keys
{
  if i == {} {
    assert {} in b.Keys;
  } else {
    assert b.Keys[1] in b.Keys;
  }
}