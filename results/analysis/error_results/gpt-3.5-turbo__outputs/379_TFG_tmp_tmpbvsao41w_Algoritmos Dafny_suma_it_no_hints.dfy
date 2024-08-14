method suma_it(V: array<int>) returns (x: int)
    requires V != null
    ensures x == suma_vector(V, 0)
{
    var n := V.Length;
    var i := 0;
    x := 0;
    while i < n
        invariant 0 <= i <= n
        invariant x == suma_vector(V, i)
        decreases n - i
    {
        x := x + V[i];
        i := i + 1;
    }
}

function suma_vector(V: array<int>, n: nat): int
    requires V != null
    requires 0 <= n <= V.Length
    reads V
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
