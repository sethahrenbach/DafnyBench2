//Problem01
method square0(n:nat) returns (sqn : nat)
ensures sqn == n*n
{
    sqn := 0;
    var i:= 0;
    var x;
    while i < n
        invariant sqn == i*i
        invariant i <= n
    {
        x := 2*i+1;
        sqn := sqn+x;
        i := i+1;
    }
    
}

method square1(n:nat) returns (sqn : nat)
ensures sqn == n*n
{
    sqn := 0;
    var i:= 0;

    while i < n
        invariant sqn == i*i
        invariant i <= n
    {
        var x := 2*i+1;
        sqn := sqn+x;
        i := i+1;
    }
    
}

//Problem02
//As you can see below, Dafny claims that after executing the following method
//strange() we will have that 1=2;
method q(x:nat, y:nat) returns (z:nat)
requires y - x > 2
ensures x < z*z < y

method strange()
ensures 1==2
{
    var x := 4;
    var c:nat := q(x,2*x); 
}

//Problem 3
//Use what you know about the weakest preconditions/strongest postconditions to ex-
//plain why the following code verifies:
method test0(){
    var x:int := *;
    assume x*x < 100;
    assert -9 <= x <= 9;
}