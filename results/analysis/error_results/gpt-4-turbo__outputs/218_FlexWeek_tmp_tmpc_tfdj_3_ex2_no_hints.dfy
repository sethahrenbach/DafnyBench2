function abs(a:int):nat
{
    if a < 0 then -a else a
}

method aba(a:array<int>) returns (b:array<int>)
    ensures a.Length == b.Length // needed for next line
    ensures forall x :: 0 <= x < b.Length ==> b[x] == abs(a[x])
{
    b := new int[a.Length];
    var i := 0;

    while (i < a.Length)
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> b[k] == abs(a[k])
        decreases a.Length - i
    {
        if(a[i] < 0){
            b[i] := -a[i];
        } else{
            b[i] := a[i];
        }
        i := i + 1;
    }
}

method Main()
{
  var a := new int[4];
  a[0] := 1; a[1] := -2; a[2] := -2; a[3] := 1;
  var b := aba(a);
}