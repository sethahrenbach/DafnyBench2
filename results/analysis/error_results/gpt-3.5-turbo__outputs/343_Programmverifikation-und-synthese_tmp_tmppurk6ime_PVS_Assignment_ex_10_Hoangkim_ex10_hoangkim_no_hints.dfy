//Problem01
method square0(n:nat) returns (sqn : nat)
    requires n >= 0;
    ensures sqn == n*n
{
    sqn := 0;
    var i := 0;
    var x:int;
    while i < n
        invariant i >= 0 && i <= n
        invariant sqn == i*i
    {
        x := 2*i+1;
        sqn := sqn+x;
        i := i+1;
    }
    
}

method square1(n:nat) returns (sqn : nat)
    requires n >= 0;
    ensures sqn == n*n
{
    sqn := 0;
    var i := 0;

    while i < n
        invariant i >= 0 && i <= n
        invariant sqn == i*i
    {
        var x := 2*i+1;
        sqn := sqn+x;
        i := i+1;
    }
    
}

//Problem02
method q(x:nat, y:nat) returns (z:nat)
    requires y - x > 2;
    ensures x < z*z < y;

method strange()
    ensures 1==2
{
    var x := 4;
    var c:nat := q(x,2*x); 
}

//Problem 3
method test0(){
    var x:int := *;
    assume x*x < 100;
    assert x <= 9;
}