// line contém uma string de tamanho l
// remover p caracteres a partir da posição at
method Delete(line:array<char>, l:nat, at:nat, p:nat)
  requires l <= line.Length
  requires at+p <= l
  modifies line
  ensures line[..at] == old(line[..at])
  ensures line[at..l-p] == old(line[at+p..l])
{
    var i:nat := 0;
    while i < l-(at+p)
      invariant 0 <= i <= l-(at+p)
      invariant at+i <= l
      invariant at+p+i <= l
      invariant line[..at] == old(line[..at])
      invariant line[at..at+i] == old(line[at..at+i])
      invariant line[at+i..l-p+i] == old(line[at+p..l])
      invariant line[l-p+i..l] == old(line[l-p+i..l])
    { 
        line[at+i] := line[at+p+i];
        i := i+1;
    }
}
