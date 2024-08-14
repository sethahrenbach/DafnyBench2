method suma_componentes(V : array?<int>) returns (suma : int)
  requires V != null
  ensures  suma == suma_aux(V, 0)	// x = V[0] + V[1] + ... + V[N - 1]
{
  var n : int ;
  n := V.Length ;  // n := N
  suma := 0 ;

  while n > 0
    decreases n
    invariant 0 <= n <= V.Length
    invariant suma == suma_aux(V, V.Length - n)
  {
    suma := suma + V[n - 1] ;
    n := n - 1 ;
  }
}

function suma_aux(V : array?<int>, n : int) : int
  requires V != null			// P_0
  requires 0 <= n <= V.Length		// Q_0
  reads V
  decreases V.Length - n
{
  if (n == V.Length) then 0
  else V[n] + suma_aux(V, n + 1)
}