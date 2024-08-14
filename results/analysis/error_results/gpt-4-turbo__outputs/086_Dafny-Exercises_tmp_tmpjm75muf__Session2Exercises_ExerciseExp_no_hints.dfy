function exp(x:int, e:int):int
    requires e >= 0
    ensures x > 0 ==> exp(x,e) > 0
{
    if e == 0 then 1 else x*exp(x,e-1)
}

lemma exp3_Lemma(n:int) 
    requires n >= 1
    ensures (exp(3,n)-1)%2 == 0
{
    if n == 1 {
        assert exp(3, 1) - 1 == 2 - 1;
        assert (2 - 1) % 2 == 0;
    } else {
        exp3_Lemma(n-1);
        assert (exp(3, n) - 1) == (3 * exp(3, n-1) - 1);
        assert ((3 * exp(3, n-1) - 1) % 2) == 0;
    }
}

lemma mult8_Lemma(n:int)
    requires n >= 1
    ensures (exp(3,2*n) - 1)%8 == 0
{
    if(n==1){
        assert exp(3, 2*1) - 1 == 8 - 1;
        assert (8 - 1) % 8 == 0;
    }
    else{
        mult8_Lemma(n-1);
        assert (exp(3, 2*(n-1)) - 1) % 8 == 0;
        assert (exp(3, 2*n) - 1) == (9 * exp(3, 2*(n-1)) - 1);
        assert ((9 * exp(3, 2*(n-1)) - 1) % 8) == 0;
    }
}