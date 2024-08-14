datatype Steps = One | Two

function stepSum(xs: seq<Steps>): nat {
    if xs == [] then 0 else (match xs[0] {
        case One => 1
        case Two => 2
    } + stepSum(xs[1..]))
}

ghost predicate stepEndsAt(xs: seq<Steps>, n: nat) {
    stepSum(xs) == n
}
ghost predicate allEndAtN(ss: set<seq<Steps> >, n: nat) {
    forall xs ::  xs in ss ==> stepEndsAt(xs, n)
}

lemma stepBaseZero() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 0) && |ss| == 1
{
    var ss: set<seq<Steps>> := {[]};
    assert allEndAtN(ss, 0);
    assert |ss| == 1;
}
lemma stepBaseOne() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 1) && |ss| == 1
{
    var ss: set<seq<Steps>> := {[One]};
    assert allEndAtN(ss, 1);
    assert |ss| == 1;
}

lemma stepBaseTwo() 
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 2) && |ss| == 2
{
    var ss: set<seq<Steps>> := {[Two], [One, One]};
    assert allEndAtN(ss, 2);
    assert |ss| == 2;
}

ghost function plusOne(x: seq<Steps>): seq<Steps> {
    [One]+x
}

ghost function addOne(ss: set<seq<Steps>>): set<seq<Steps>> 
    ensures forall x :: x in ss ==> plusOne(x) in addOne(ss)
    ensures addOne(ss) == set x | x in ss :: plusOne(x)
{
    set x | x in ss :: plusOne(x)
}

lemma SeqsNotEqualImplication<T>(xs: seq<T>, ys: seq<T>, someT: T)
    requires xs != ys
    ensures (exists i: nat :: i < |xs| && i <|ys| && xs[i] != ys[i]) || |xs| < |ys| || |ys| < |xs|
{}

lemma UnequalSeqs<T>(xs: seq<T>, ys: seq<T>, someT: T)
    requires xs != ys
    ensures [someT]+xs != [someT]+ys
{
    if |xs| < |ys| {} else if |ys| > |xs| {}
    else if i: nat :| i < |xs| && i <|ys| && xs[i] != ys[i] {
    }
}

lemma plusOneNotIn(ss: set<seq<Steps>>, x: seq<Steps>)
    requires x !in ss
    ensures plusOne(x) !in addOne(ss)
{
    if x == [] {
    }
    if plusOne(x) in addOne(ss) {
        var y :| y in ss && plusOne(y) == plusOne(x);
        assert y != x;
        UnequalSeqs(x, y, One);
        assert false;
    }
}

lemma addOneSize(ss: set<seq<Steps>>)
    ensures |addOne(ss)| == |ss|
{
    var size := |ss|;
    if x :| x in ss {
        addOneSize(ss - {x});
        plusOneNotIn(ss-{x}, x);
    }else{

    }
}

lemma addOneSum(ss: set<seq<Steps>>, sum: nat) 
    requires allEndAtN(ss, sum)
    ensures allEndAtN(addOne(ss), sum+1)
{
    forall x | x in ss
        ensures stepEndsAt(plusOne(x), sum+1)
    {
        assert stepSum(plusOne(x)) == stepSum([One]) + stepSum(x) == 1 + sum;
    }
}

lemma endAtNPlus(ss: set<seq<Steps>>, sz: set<seq<Steps>>, sum: nat)
    requires allEndAtN(ss, sum)
    requires allEndAtN(sz, sum)
    ensures allEndAtN(ss+sz, sum)
{
    forall x | x in ss+sz
        ensures stepEndsAt(x, sum)
    {
        if x in ss {
        } else {
            assert x in sz;
        }
    }
}

ghost function plusTwo(x: seq<Steps>): seq<Steps> {
    [Two]+x
}

ghost function addTwo(ss: set<seq<Steps>>): set<seq<Steps>> 
    ensures forall x :: x in ss ==> plusTwo(x) in addTwo(ss)
    ensures addTwo(ss) == set x | x in ss :: plusTwo(x)
{
    set x | x in ss :: plusTwo(x)
}

lemma plusTwoNotIn(ss: set<seq<Steps>>, x: seq<Steps>)
    requires x !in ss
    ensures plusTwo(x) !in addTwo(ss)
{
    if x == [] {
    }
    if plusTwo(x) in addTwo(ss) {
        var y :| y in ss && plusTwo(y) == plusTwo(x);
        assert y != x;
        UnequalSeqs(x, y, Two);
        assert false;
    }
}

lemma addTwoSize(ss: set<seq<Steps>>)
    ensures |addTwo(ss)| == |ss|
{
    var size := |ss|;
    if x :| x in ss {
        addTwoSize(ss - {x});
        plusTwoNotIn(ss-{x}, x);
    }
}

lemma addTwoSum(ss: set<seq<Steps>>, sum: nat) 
    requires allEndAtN(ss, sum)
    ensures allEndAtN(addTwo(ss), sum+2)
{
    forall x | x in ss
        ensures stepEndsAt(plusTwo(x), sum+2)
    {
        assert stepSum(plusTwo(x)) == stepSum([Two]) + stepSum(x) == 2 + sum;
    }
}

lemma setSizeAddition<T>(sx: set<T>, sy: set<T>, sz: set<T>) 
    requires sx !! sy
    requires sz == sx + sy
    ensures |sx + sy| == |sx| + |sy|
    ensures |sz| == |sx| + |sy|
{
    assert forall x :: x in sz <==> x in sx || x in sy;
}

lemma stepSetsAdd(i: nat, steps: array<nat>) 
    requires i >= 3
    requires steps.Length >= i+1
    requires forall k: nat :: 0 <= k < i ==> exists ss: set< seq<Steps> > :: steps[k] == |ss| && allEndAtN(ss, k)
    ensures exists sp : set< seq<Steps> > :: |sp| == steps[i-1] + steps[i-2] && allEndAtN(sp, i)
{
    var oneStepBack :| steps[i-1] == |oneStepBack| && allEndAtN(oneStepBack, i-1);
    var twoStepBack :| steps[i-2] == |twoStepBack| && allEndAtN(twoStepBack, i-2);
    var stepForward := addOne(oneStepBack);
    var stepTwoForward := addTwo(twoStepBack);
    assert stepForward !! stepTwoForward;
    addOneSize(oneStepBack);
    addTwoSize(twoStepBack);
    var sumSet := stepForward + stepTwoForward;
    setSizeAddition(stepForward, stepTwoForward, sumSet);
    addOneSum(oneStepBack, i-1);
    addTwoSum(twoStepBack, i-2);
    endAtNPlus(stepForward, stepTwoForward, i);
}

method climbStairs(n: nat) returns (count: nat) 
    ensures exists ss: set< seq<Steps> > :: count == |ss| && allEndAtN(ss, n)
{
    var steps := new nat[n+1];
    steps[0] := 1;
    if n > 0 {
        steps[1] := 1;
    }
    if n > 1 {
        steps[2] := 2;
    }
    if n == 0 {
        stepBaseZero();
        return steps[0];
    }
    if n == 1 {
        stepBaseOne();
        return steps[1];
    }
    if n == 2 {
        stepBaseTwo();
        return steps[2];
    }
    var i := 3;
    while i <= n 
        invariant 3 <= i <= n+1
        invariant forall k: nat :: 0 <= k < i ==> exists ss: set< seq<Steps> > :: steps[k] == |ss| && allEndAtN(ss, k)
        decreases n - i
    {   
        stepSetsAdd(i, steps);
        steps[i] := steps[i-1] + steps[i-2];
        i := i + 1;
    }
    return steps[n];
}


lemma stepBaseThree()
    ensures exists ss: set< seq<Steps> > :: allEndAtN(ss, 3) && |ss| == 3
{
    var ss: set<seq<Steps>> := {[One, One, One], [One, Two], [Two, One]};
    assert allEndAtN(ss, 3);
    assert |ss| == 3;
}

method Test() {
    var foo := [One, One, Two];
}
