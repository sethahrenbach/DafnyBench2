
method test_generic_syntax_error()
  requires 1 < 2
  ensures false
{
  var x := 1;
  var y := 2;
  if x < y then
    x := x + 1;
  else
    x := x - 1;
  endif;
}
