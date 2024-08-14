class {:autocontracts} Fila {
  var a: array<int>;
  var cauda: nat;
  const defaultSize: nat;

  ghost var Conteudo: seq<int>;

  predicate Valid() reads this {
    defaultSize > 0 &&
    a.Length >= defaultSize &&
    0 <= cauda <= a.Length &&
    Conteudo == a[0..cauda]
  }

  constructor ()
    ensures Conteudo == []
    ensures defaultSize == 3
    ensures a.Length == 3
    ensures fresh(a)
  {
    defaultSize := 3;
    a := new int[3];
    cauda := 0;
    Conteudo := [];
  }

  function tamanho(): nat
    ensures tamanho() == |Conteudo|
  {
    cauda
  }

  function estaVazia(): bool
    ensures estaVazia() <==> |Conteudo| == 0
  {
    cauda == 0
  }

  method enfileira(e: int)
    ensures Conteudo == old(Conteudo) + [e]
  {
    if (cauda == a.Length) {
      var novoArray := new int[cauda + defaultSize];
      var i := 0;
      while i < a.Length
        invariant 0 <= i <= a.Length
        invariant forall k | 0 <= k < i :: novoArray[k] == a[k]
      {
        novoArray[i] := a[i];
        i := i + 1;
      }
      a := novoArray;
    }

    a[cauda] := e;
    cauda := cauda + 1;
    Conteudo := Conteudo + [e];
  }

  method desenfileira() returns (e: int)
    requires |Conteudo| > 0
    ensures e == old(Conteudo)[0]
    ensures Conteudo == old(Conteudo)[1..]
  {
    e := a[0];
    cauda := cauda - 1;
    var i := 0;
    while i < cauda
      invariant 0 <= i <= cauda
      invariant forall k | 0 <= k < i :: a[k] == a[k + 1]
    {
      a[i] := a[i + 1];
      i := i + 1;
    }
    Conteudo := a[0..cauda];
  }

  method contem(e: int) returns (r: bool)
    ensures r <==> exists i :: 0 <= i < cauda && e == a[i]
  {
    var i := 0;
    r := false;
    while i < cauda
      invariant 0 <= i <= cauda
      invariant !r ==> forall k | 0 <= k < i :: a[k] != e
    {
      if (a[i] == e) {
        r := true;
        break;
      }
      i := i + 1;
    }
  }

  method concat(f2: Fila) returns (r: Fila)
    requires Valid()
    requires f2.Valid()
    ensures r.Conteudo == Conteudo + f2.Conteudo
  {
    r := new Fila();
    var i := 0;
    while i < cauda
      invariant 0 <= i <= cauda
    {
      r.enfileira(a[i]);
      i := i + 1;
    }

    var j := 0;
    while j < f2.cauda
      invariant 0 <= j <= f2.cauda
    {
      r.enfileira(f2.a[j]);
      j := j + 1;
    }
  }
}

method Main() {
  var fila := new Fila();
  fila.enfileira(1);
  fila.enfileira(2);
  fila.enfileira(3);
  fila.enfileira(4);
  var q := fila.tamanho();
  var e := fila.desenfileira();
  var r := fila.contem(1);
  var r2 := fila.contem(2);
  var vazia := fila.estaVazia();
  var outraFila := new Fila();
  vazia := outraFila.estaVazia();
  outraFila.enfileira(5);
  outraFila.enfileira(6);
  outraFila.enfileira(7);
  var concatenada := fila.concat(outraFila);
}