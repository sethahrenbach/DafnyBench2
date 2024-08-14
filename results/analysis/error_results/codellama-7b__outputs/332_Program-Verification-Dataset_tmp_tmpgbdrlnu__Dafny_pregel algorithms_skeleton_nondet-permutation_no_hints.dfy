
module Foo
{
  pre
    x: int
  post
    x: int
  {
    if x > 0
    {
      print "x is positive";
    }
    else
    {
      print "x is not positive";
    }
  }
}
