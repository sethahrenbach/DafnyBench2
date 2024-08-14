/*                                      Cumulative Sums over Arrays                                        */

/*
    Daniel Cavalheiro   57869
    Pedro Nunes         57854
*/



//(a)

function sum(a: array<int>, i: int, j: int): int
    reads a
    requires 0 <= i <= j <= a.Length
    ensures (i == j) ==> sum(a, i, j) == 0
    ensures (i < j) ==> sum(a, i, j) == a[i] + sum(a, i+1, j)
    decreases j - i
{
    if (i == j) then 0
    else a[i] + sum(a, i+1, j)
}



//(b)

method query(a: array<int>, i: int, j: int) returns (res:int)
    requires 0 <= i <= j <= a.Length
    ensures res == sum(a, i, j)
{
    res := 0;
    var k := i;

    while(k < j)
        invariant 0 <= i <= k <= j <= a.Length
        invariant res == sum(a, i, k)
        decreases j - k
    {
        res := res + a[k];
        k := k + 1;
    }
    assert res == sum(a, i, j);
}



//(c)

predicate is_prefix_sum_for (a: array<int>, c: array<int>)
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    reads c, a
{
    forall i: int :: 0 <= i < a.Length ==> c[i+1] == c[i] + a[i]
}

lemma aux(a: array<int>, c: array<int>, i: int, j: int)
    requires 0 <= i <= j <= a.Length
    requires a.Length + 1 == c.Length
    requires c[0] == 0
    requires is_prefix_sum_for(a, c)
    ensures sum(a, i, j) == c[j] - c[i]
    decreases j - i
{
    if (i == j) {
        assert sum(a, i, j) == 0;
        assert c[j] - c[i] == 0;
    } else {
        assert sum(a, i, j) == a[i] + sum(a, i+1, j);
        aux(a, c, i+1, j);
        assert sum(a, i+1, j) == c[j] - c[i+1];
        assert sum(a, i, j) == a[i] + (c[j] - c[i+1]);
        assert sum(a, i, j) == c[j] - c[i];
    }
}


method queryFast(a: array<int>, c: array<int>, i: int, j: int) returns (r: int)
    requires a.Length + 1 == c.Length && c[0] == 0
    requires 0 <= i <= j <= a.Length
    requires is_prefix_sum_for(a,c)  
    ensures r == sum(a, i, j)
{   
    aux(a, c, i, j);
    r := c[j] - c[i];    
}



method Main()
{
    var x := new int[10];
    x[0], x[1], x[2], x[3] := 2, 2, 1, 5;
    var y := sum(x, 0, 4);
    assert y == 10;
    var c := new int[11];
    c[0], c[1], c[2], c[3], c[4] := 0, 2, 4, 5, 10;
    assert is_prefix_sum_for(x, c);
    var r := queryFast(x, c, 0, 4);
    assert r == y;
}