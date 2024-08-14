
method abs(x: int) returns (y: int)
    ensures true
{
    if x < 0 {
        y := -x;
    } else {
        y :=  x;
    }
}

method foo(x: int) 
    requires x >= 0
{
    var y := abs(x);
}

method max(x: int, y: int) returns (m: int)
requires true;
ensures true;
{
    if x > y {
        m := x;
    } else {
        m := y;
    }
}

method ex1(n: int)
    requires true
    ensures true
{
    var i := 0;
    while i < n
        decreases n - i
    {
        i := i + 1;
    }
}

method foo2() 
    ensures false
{
    while true 
    {
    }
}

method find(a: seq<int>, key: int) returns (index: int)
    requires true
    ensures true
{
    index := 0;
    while index < |a|
        decreases |a| - index
    {
        if a[index] == key {
            return index;
        }
        index := index + 1;
    }
    index := -1;
}

method isPalindrome(a: seq<char>) returns (b: bool) 
{
    var i := 0;
    var j := |a| - 1;
    b := true;
    while i < j
        decreases j - i
    {
        if a[i] != a[j] {
            b := false;
            break;
        }
        i := i + 1;
        j := j - 1;
    }
    return b;
}

predicate sorted(a: seq<int>) 
{
    forall j, k::0 <= j < k < |a| ==> a[j] <= a[k]
}

method unique(a: seq<int>) returns (b: seq<int>) 
    requires sorted(a)
    ensures true
{
    b := [];
    if |a| > 0 {
        var last := a[0];
        b := [last];
        var i := 1;
        while i < |a|
            decreases |a| - i
        {
            if a[i] != last {
                b := b + [a[i]];
                last := a[i];
            }
            i := i + 1;
        }
    }
    return b;
}

method Main() {
    var r := find([], 1);   
    print r, "\n";

    r := find([0,3,5,7], 5);  
    print r, "\n";

    var s1 := ['a'];
    var r1 := isPalindrome(s1);
    print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

    s1 := [];
    r1 := isPalindrome(s1);
    print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

    s1 := ['a', 'b'];
    r1 := isPalindrome(s1);
    print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

    s1 := ['a', 'b', 'a'];
    r1 := isPalindrome(s1);
    print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

    var i := [0,1,3,3,5,5,7];
    var s := unique(i);
    print "unique applied to ", i, " is ", s, "\n";
}
