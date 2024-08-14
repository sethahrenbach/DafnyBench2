
method Abs(x:int) returns (y:int)
    ensures y>=0;
    ensures x>=0 ==> x == y;
    ensures x<0 ==> -x == y;
    ensures y == abs(x);
{
    if(x<0)
    {
        assert -x >= 0;
        assert -x == abs(x);
        return -x;
    }
    else
    {
        assert x >= 0;
        assert x == abs(x);
        return x;
    }
}

function abs(x: int): int
{
    if x>0 then x else -x
}

method Testing()
{
    var v:= Abs(-3);
}

method MultiReturn(x:int, y:int) returns (more:int, less:int)
    requires y>=0;
    ensures less <= x <= more;
{
    more := x + y;
    less := x - y;
}

method Max(x:int, y:int) returns (a:int)
    ensures a == x || a == y;
    ensures x > y ==> a == x;
    ensures x <= y ==> a == y;
{
    if ( x > y ) 
    { 
        assert x > y;
        a := x;
    } else 
    { 
        assert x <= y;
        a := y; 
    }
}
