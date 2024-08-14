// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

type Id(==)

function F(s: set<Id>): int

lemma Test(x: Id)
{
  var X := {x};
  var a := map i | i in {{}, X} :: F(i);
  var b := map[{} := F({}), X := F(X)];

  forall i
    ensures i in a.Keys <==> i in b.Keys
  {
    assert i in a.Keys <==> i in {{}, X};
    assert i in b.Keys <==> i in {{}, X};
    assert (i in a.Keys) == (i in b.Keys);
  }
}