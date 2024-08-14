  function exp(x:int, e:int):int
	requires e >= 0
	ensures x > 0 ==> exp(x,e) > 0
{
	if e == 0 then 1 else x*exp(x,e-1)
}