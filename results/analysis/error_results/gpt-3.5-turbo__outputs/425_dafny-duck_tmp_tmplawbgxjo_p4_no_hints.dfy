
method single(x: array<int>, y: array<int>) returns (b: array<int>)
    requires x.Length > 0
    requires y.Length > 0
    ensures b[..] == x[..] + y[..]
{
    b := new int[x.Length + y.Length](i => if i < x.Length then x[i] else y[i - x.Length]);
}

method Main()
{
    var a := new int[4]([1, 5, 2, 3]);
    var b := new int[3]([4, 3, 5]);
    var c := new int[7];
    c := single(a, b);
    //print c[..];
}
