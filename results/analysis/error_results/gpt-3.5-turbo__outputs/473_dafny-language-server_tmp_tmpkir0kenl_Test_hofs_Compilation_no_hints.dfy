
class Ref<A> {
  var val : A
    constructor (a : A)
      ensures val == a
    {
      val := a;
    }
}

method Main() {
  // simple
  print "1 = ", (x => x)(1), "\n";
  print "3 = ", (x => y => x + y)(1)(2), "\n";
  print "3 = ", ((x,y) => y + x)(1,2), "\n";
  print "0 = ", (() => 0)(), "\n";

  // local variable
  var y1 := 1;
  var f := x => x + y1;
  print "3 = ", f(2), "\n";
  print "4 = ", f(3), "\n";
  y1 := 2;
  print "3 = ", f(2), "\n";
  print "4 = ", f(3), "\n";

  // reference
  var z := new Ref(1);
  f := x reads z => x + z.val;
  print "3 = ", f(2), "\n";
  print "4 = ", f(3), "\n";
  z.val := 2;
  print "4 = ", f(2), "\n";
  print "5 = ", f(3), "\n";

  // loop
  f := x => x;
  var y2 := 10;
  while y2 > 0
    invariant y2 >= 0 && y2 <= 10
    invariant forall k :: 0 <= k < y2 ==> f(0) == f(k)
    decreases y2
  {
    f := x => f(x+y2);
    y2 := y2 - 1;
  }
  print "55 = ", f(0), "\n";

  // substitution test
  print "0 = ", (x => var y3:=x;y3)(0), "\n";
  print "1 = ", (y4 => (x => var y5:=x;y5))(0)(1), "\n";
}
