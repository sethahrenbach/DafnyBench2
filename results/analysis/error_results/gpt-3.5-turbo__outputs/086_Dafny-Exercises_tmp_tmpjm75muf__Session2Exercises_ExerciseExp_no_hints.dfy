function exp(x:int, e:int):int
	requires e >= 0
    ensures x > 0 ==> exp(x,e) > 0
{
	if e == 0 then 1 else x*exp(x,e-1)
}

lemma   exp3_Lemma(n:int) 
    requires n >= 1
	ensures (exp(3,n)-1)%2 == 0
{}

lemma  mult8_Lemma(n:int)
	requires n >= 1
	ensures (exp(3,2*n) - 1)%8 == 0
{
    if(n==1){
        assert (exp(3,2*n) - 1) % 8 == 0;
    }
    else{
        var result := exp(3,2*n);
        calc{
            result % 8;
            (exp(3, 2*(n-1)) * 8 + exp(3,2*(n-1)) - 1) % 8;
            mult8_Lemma(n-1);
            assert result % 8 == 0;
        }
    }
}