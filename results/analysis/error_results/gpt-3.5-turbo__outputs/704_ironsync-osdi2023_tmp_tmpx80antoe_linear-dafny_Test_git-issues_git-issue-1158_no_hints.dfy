type Id(==)

function F(s: set<Id>): int
  requires s != {};
  ensures F(s) >= 0;

lemma Test(x: Id)
{
  var X := {x};
  var a := map i | i <= X :: F(i);
  var b := map[{} := F({}), X := F(X)];

  forall i :: i in a.Keys <==> i in b.Keys
  {
    assert i <= X <==> i == {} || i == X;
  }
}