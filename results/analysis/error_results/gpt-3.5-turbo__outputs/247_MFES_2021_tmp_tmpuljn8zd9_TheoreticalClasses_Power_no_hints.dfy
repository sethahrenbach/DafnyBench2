
/* 
* Formal verification of O(n) and O(log n) algorithms to calculate the natural
* power of a real number (x^n), illustrating the usage of lemmas.
* FEUP, MIEIC, MFES, 2020/21.
*/

// Initial specification/definition of x^n, recursive, functional style, 
// with time and space complexity O(n).
function power(x: real, n: nat) : real
{
    if n == 0 then 1.0 else x * power(x, n-1)
}

// Iterative version, imperative, with time complexity O(n) and space complexity O(1).
method powerIter(x: real, n: nat) returns (p : real)
    ensures p == power(x, n)
{
    var i := 0;
    p := 1.0;
    while i < n
      invariant 0 <= i <= n
      invariant p == power(x, i)
    {
        p := p * x;
        i := i + 1;
    }
}

// Recursive version, imperative, with time and space complexity O(log n).
method powerOpt(x: real, n: nat) returns (p : real)
    ensures p == power(x, n);
{
    if n == 0 {
        return 1.0;
    }
    else if n == 1 {
        return x;
    }
    else if n % 2 == 0 {
        distributiveProperty(x, n/2, n/2);
        var temp := powerOpt(x, n/2);
        return temp * temp;
    }
    else {
        distributiveProperty(x, (n-1)/2, (n-1)/2);
        var temp := powerOpt(x, (n-1)/2);
        return temp * temp * x;
    } 
}

// States the property x^a * x^b = x^(a+b), that powerOpt takes advantage of. 
// The annotation {:induction a} guides Dafny to prove the property
// by automatic induction on 'a'.
lemma {:induction a} distributiveProperty(x: real, a: nat, b: nat) 
    ensures power(x, a) * power(x, b)  == power(x, a + b) 
{
    if a == 0 {
        calc {
            power(x, a) * power(x, b);
            power(x, 0) * power(x, b);
            1.0 * power(x, b);
            power(x, b);
            power(x, a + b);
        }
    }
    else {
        distributiveProperty(x, a-1, b);
        calc {
            power(x, a) * power(x, b);
            (x * power(x, a-1)) * power(x, b);
            x * (power(x, a-1) * power(x, b));
            x * power(x, a + b - 1);
            power(x, a + b);
        }
    }
}

// A simple test case to make sure the specification is adequate.
method testPowerIter(){
    var p1 := powerIter(2.0, 5);
    assert p1 == power(2.0, 5);
}

method testPowerOpt(){
    var p1 := powerOpt(2.0, 5);
    assert p1 == power(2.0, 5);
}
