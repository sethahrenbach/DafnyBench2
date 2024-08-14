
function expo(x:int, n:nat): int
{
    if n == 0 then 1
    else x * expo(x, n-1)
}

lemma {:induction false} Expon23(n: nat)
requires n >= 0
ensures ((expo(2,3*n) - expo(3,n)) % (2+3)) == 0
{   
    // base case
    if (n == 0) {
        assert expo(2, 3*0) - expo(3, 0) == 0;
        assert (expo(2, 3*0) - expo(3, 0)) % (2+3) == 0;
    }

    else if (n == 1) {
        assert expo(2, 3*1) - expo(3, 1) == 0;
        assert (expo(2, 3*1) - expo(3, 1)) % (2+3) == 0;
    }
    else {
        Expon23(n-1); // lemma proved for case n-1  
        
        assert expo(2, 3*n) - expo(3, n) == 0;
        assert (expo(2, 3*n) - expo(3, n)) % (2+3) == 0;
    }
}
