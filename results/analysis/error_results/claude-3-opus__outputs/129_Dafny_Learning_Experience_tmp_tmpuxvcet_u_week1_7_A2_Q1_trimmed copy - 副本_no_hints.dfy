ghost function Count(hi: nat, s:seq<int>): int
    requires 0 <= hi <= |s|
{
    if hi == 0 then 0
    else if s[hi-1]%2 == 0 then 1 + Count(hi-1, s) else Count(hi-1, s)
}

method FooCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    modifies b
    ensures p == Count(CountIndex,a)
{
    if CountIndex == 0{
        p :=0;
    } else{
        assert a[CountIndex-1]%2 !=0 ==>  |a| == b.Length && 0<= CountIndex -1 <|a| && Count(CountIndex-1,a) == Count(CountIndex,a);
        if a[CountIndex-1]%2==0{
            var d := FooCount(CountIndex -1,a,b);
            p:= d+1;
        }else{
            var d:= FooCount(CountIndex -1,a,b);
            p:= d;
        }
        b[CountIndex-1] := p;
        assert p == Count(CountIndex,a);
    }
}

method FooPreCompute(a:array<int>,b:array<int>)
    requires a.Length == b.Length
    modifies b
    ensures forall i :: 0 <= i < a.Length ==> b[i] == Count(i+1, a[..])
{
    var CountIndex := 1;
    while CountIndex != a.Length + 1
        invariant 1 <= CountIndex <= a.Length + 1
        invariant forall i :: 0 <= i < CountIndex-1 ==> b[i] == Count(i+1, a[..])
        modifies b
    {   
        assert CountIndex-1 < a.Length;
        var p := FooCount(CountIndex,a[..],b);
        assert p == Count(CountIndex, a[..]);
        assert b[CountIndex-1] == p;
        CountIndex := CountIndex +1;
    }
    assert forall i :: 0 <= i < a.Length ==> b[i] == Count(i+1, a[..]);
}


method ComputeCount(CountIndex:nat, a:seq<int>,b:array<int>) returns (p:nat)
    requires  CountIndex == 0 || (|a| == b.Length && 1 <= CountIndex <= |a|)
    modifies b
    ensures p == Count(CountIndex,a)
{
    if CountIndex == 0{
        p :=0;
    } else{
        if a[CountIndex-1]%2==0{
            var d := ComputeCount(CountIndex -1,a,b);
            p:= d+1;
        }else{
            var d:= ComputeCount(CountIndex -1,a,b);
            p:= d;
        }
        b[CountIndex-1] := p;
        assert p == Count(CountIndex,a);  
    }
}

method PreCompute(a:array<int>,b:array<int>)returns(p:nat)
    requires a.Length == b.Length 
    modifies b
    ensures (b.Length == 0 || (a.Length == b.Length && 1 <= b.Length <= a.Length)) &&
    forall p::p == Count(b.Length,a[..]) ==> p==Count(b.Length,a[..])
{
    assert (forall p::p == Count(b.Length,a[..]) ==> p==Count(b.Length,a[..]) );
    p := ComputeCount(b.Length,a[..],b);
    assert p == Count(b.Length,a[..]);
}

method Evens(a:array<int>) returns (c:array2<int>)
    ensures forall i,j:: 0 <=i <a.Length && 0 <= j < a.Length ==> j<i ==> c[i,j] == 0
    ensures forall i,j:: 0 <=i <a.Length && 0 <= j < a.Length && i <= j ==> 
                (i == 0 ==> c[i,j] == Count(j+1,a[..])) && 
                (i > 0 ==> c[i,j] == Count(j+1,a[..]) - Count(i,a[..]))
{ 
     c := new int[a.Length,a.Length];
     var b := new int[a.Length];
     FooPreCompute(a,b); 
     var m := 0;
     while m != a.Length
        invariant 0 <= m <= a.Length
        invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length && j<i ==> c[i,j] == 0
        invariant forall i,j:: 0 <=i <m && 0 <= j < a.Length && i <= j ==> 
                    (i == 0 ==> c[i,j] == Count(j+1,a[..])) && 
                    (i > 0 ==> c[i,j] == Count(j+1,a[..]) - Count(i,a[..]))
        modifies c
     {  
        var n := 0;
        while n != a.Length
            invariant 0 <= n <= a.Length
            invariant forall j:: 0 <= j < n && j < m ==> c[m,j] == 0
            invariant forall j:: 0 <= j < n && m <= j < a.Length ==> 
                        (m == 0 ==> c[m,j] == Count(j+1,a[..])) &&
                        (m > 0 ==> c[m,j] == Count(j+1,a[..]) - Count(m,a[..]))
            modifies c
        {   
            if (n < m) {
                c[m,n] := 0;
            }else if m <= n < a.Length { 
                if m > 0 {
                    assert b[n] == Count(n+1,a[..]);
                    assert b[m-1] == Count(m,a[..]);
                    assert Count(n+1,a[..]) - Count(m,a[..]) == b[n] - b[m-1];
                    c[m,n] := b[n] - b[m-1];
                }else{
                    assert b[n] == Count(n+1,a[..]);
                    c[m,n] := b[n];
                }
            }
            n := n + 1;
        }
        m := m + 1;
     }
}

method Mult(x:int, y:int) returns (r:int)
    requires x>= 0 && y>=0
    ensures r == x*y
{
    if x==0 {
        r:=0;
    }else{
        var z:= Mult(x-1,y);
        r:=z+y;
    }
    assert r == x*y;
}