
method M(P: (int -> int) -> bool, g: int -> int)
  requires P.requires(g)
  requires P(g)
{
  assert forall f: int -> int :: P.requires(f);
  assert forall f: int -> int :: P(f) ==> f.requires(10) && f(10) == 0;
  
  var f: int -> int;
  var x: int;
  assert (forall x :: f.requires(x) && g.requires(x) ==> f(x) == g(x)) ==>
         f.requires(10) ==>
         f(10) == 0;
}
