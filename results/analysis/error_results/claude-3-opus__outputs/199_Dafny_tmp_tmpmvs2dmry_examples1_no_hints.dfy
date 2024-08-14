method Abs(x:int) returns (y:int)
ensures y>=0;
ensures x>=0 ==> x == y;
ensures x<0 ==> -x == y;
ensures y == abs(x);
{   
    if(x<0)
    {
        y := -x;
        assert y >= 0;
        assert -x == y;
        assert y == abs(x);
    }
    else{
        y := x;
        assert y >= 0;
        assert x == y;
        assert y == abs(x);
    }
}

method Testing(){
    var v:= Abs(-3);
    assert v == 3;
}

method MultiReturn(x:int, y:int) returns (more:int, less:int)
requires y>=0;
ensures less <= x <= more;
{
    more := x + y;
    assert more == x + y;
    less := x - y;
    assert less == x - y;
    assert less <= x <= more;
}

method Max(x:int, y:int) returns (a:int)
ensures a == x || a == y;
ensures x > y ==> a == x;
ensures x <= y ==> a == y;
{
    if ( x > y ) 
    { 
        a := x;
        assert a == x;
        assert x > y ==> a == x;
    } else 
    { 
        a := y;
        assert a == y;
        assert x <= y ==> a == y; 
    }
    assert a == x || a == y;
}
