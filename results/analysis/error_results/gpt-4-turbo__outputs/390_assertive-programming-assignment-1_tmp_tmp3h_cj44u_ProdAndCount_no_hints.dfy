method Main() {
    var q := [7, -2, 3, -2];

    var p, c := ProdAndCount(q, -2);
    print "The product of all positive elements in [7,-2,3,-2] is ";
    print p;
    print "\nThe number of occurrences of -2 in [7,-2,3,-2] is ";
    print c;
}

function RecursivePositiveProduct(q: seq<int>): int
{
    if q == [] then 1
    else if q[0] <= 0 then RecursivePositiveProduct(q[1..])
    else q[0] * RecursivePositiveProduct(q[1..])
}

function RecursiveCount(key: int, q: seq<int>): int
{
    if q == [] then 0
    else if q[|q|-1] == key then 1 + RecursiveCount(key, q[..|q|-1])
    else RecursiveCount(key, q[..|q|-1])
}

method ProdAndCount(q: seq<int>, key: int) returns (prod: int, count: nat)
    ensures prod == RecursivePositiveProduct(q)
    ensures count == RecursiveCount(key, q)
{
    prod := 1; 
    count := 0;
    var size := |q|;
    var i := 0;

    while i < size
        invariant i <= size
        invariant count == RecursiveCount(key, q[..i])
        invariant prod == RecursivePositiveProduct(q[..i])
    {
        if q[i] > 0 {
            prod := prod * q[i];
        }
        if q[i] == key {
            count := count + 1;
        }
        i := i + 1;
    }
}