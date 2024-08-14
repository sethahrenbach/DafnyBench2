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
      invariant line[..at] == old(line[..at])
      invariant forall j :: at <= j < at + i ==> line[j] == old(line[j + p])
      invariant forall j :: at + i <= j < l - p ==> line[j] == old(line[j + p])
      invariant line[l-p..l] == old(line[l-p..l])
    { 
        line[at+i] := line[at+p+i];
        i := i+1;
    }
    assert line[at..l-p] == old(line[at+p..l]);
}