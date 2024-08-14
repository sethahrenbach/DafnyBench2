
function Potencia(x:nat, y:nat):nat
{
  if y == 0
  then 1
  else x * Potencia(x, y-1)
}

method Pot(x:nat, y:nat) returns (r:nat)
ensures r == Potencia(x, y)
{
  r := 1; //sempre r começa com 1
  var b := x; //base
  var e := y; //expoente

  while e > 0 
  {
    r := r * b;
    e := e - 1;
  }
  return r;
}
