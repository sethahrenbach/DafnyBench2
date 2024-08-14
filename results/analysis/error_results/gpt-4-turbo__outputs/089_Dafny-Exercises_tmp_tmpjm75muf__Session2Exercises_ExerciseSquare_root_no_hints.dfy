method mroot1(n:int) returns (r:int) //Cost O(root n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    r:=0;
    while (r+1)*(r+1) <= n
    invariant r >= 0 && r*r <= n && n < (r+2)*(r+2)
    {
        r:=r+1;
    }
}


method mroot2(n:int) returns (r:int) //Cost O(n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{
    r:=n;
    while n<r*r
    invariant r >= 0 && r*r > n
    {
        r:=r-1;
    }
}

method mroot3(n:int) returns (r:int) //Cost O(log n)
requires n>=0
ensures r>=0 && r*r <= n <(r+1)*(r+1)
{   
    var y:int;
    var h:int;
    r:=0;
    y:=n+1;
    while (y!=r+1)
    invariant r >= 0 && y > r && r*r <= n && (y == n + 1 || y*y > n)
    invariant r+1 < y // Ensures progress towards termination
    {
        h:=(r+y)/2;
        if (h*h<=n)
        {
            r:=h;
        }
        else
        {
            y:=h;
        } 
    }
}