  I apologize for the confusion, and I'll make sure to take the Dafny feedback into account. Here's another attempt at the solution:

method suma_it(V: array<int>) returns (x: int)
  ensures x == suma_vector(V, 0)
  loop_invariant 0 <= n <= V.Length
  loop_variant n
{
  var n := V.Length;
  x := 0;
  while (n != 0)
  {
    x := x + V[n - 1];
    n := n - 1;
  }
}

function suma_vector(V: array<int>, n: nat): int
  requires 0 <= n <= V.Length
  reads V
  ensures 0 <= n <= V.Length
  loop_invariant 0 <= n <= V.Length
  loop_variant n
{
  if (n == V.Length) then 0
  else V[n] + suma_vector(V, n + 1)
}

method Main()
{
  var v := new int[] [-1, 2, 5, -5, 8];
  var w := new int[] [1, 0, 5, 5, 8];
  var s1 := suma_it(v);
  var s2 := suma_it(w);

  print "La suma del vector v es: ", s1, "\n";
  print "La suma del vector w es: ", s2;
}

This solution should pass the test.