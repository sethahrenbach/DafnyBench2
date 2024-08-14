
/*predicate palindrome<T(==)> (s:seq<T>)
{
    forall i:: 0<=i<|s| ==> s[i] == s[|s|-i-1]
}
*/

// SUM OF A SEQUENCE OF INTEGERS
function sum(v: seq<int>): int 
{
    if v==[] then 0
    else if |v|==1 then v[0]
    else v[0]+sum(v[1..])
}

// VECTOR SUM
method vector_Sum(v:seq<int>) returns (x:int)
ensures x == sum(v) 
{
    var n := 0 ;
    x := 0;
    while n != |v|
    invariant 0 <= n <= |v|
    invariant x == sum(v[..n])
    {
        x, n := x + v[n], n + 1;
    }
}

// Structural Induction on Sequences
lemma left_sum_Lemma(r:seq<int>, k:int)
requires 0 <= k <= |r|
ensures sum(r[..k]) + (if k < |r| then r[k] else 0) == sum(r[..k+1])
{
    if k == 0 {
    } else if k == |r| {
    } else {
        left_sum_Lemma(r, k-1);
    }
}

// MAXIMUM OF A SEQUENCE
method maxSeq(v: seq<int>) returns (max:int)
requires |v| >= 1
ensures forall i :: 0 <= i < |v| ==> max >= v[i]
ensures max in v
{
    max := v[0];
    var i := 1;
    while i < |v|
    invariant 1 <= i <= |v|
    invariant forall j :: 0 <= j < i ==> max >= v[j]
    invariant max in v[..i]
    {
        if v[i] > max {
            max := v[i];
        }
        i := i + 1;
    }
}

// CUBES
method Cubes (n:int) returns (s:seq<int>)
requires n >= 0
ensures |s| == n
ensures forall i:int :: 0 <= i < n ==> s[i] == i*i*i
{
    s := [];
    var j := 0;
    while j < n
    invariant 0 <= j <= n
    invariant |s| == j
    invariant forall i :: 0 <= i < j ==> s[i] == i*i*i
    {
        s := s + [j*j*j];
        j := j + 1;
    }
}

// REVERSE OF A SEQUENCE
function reverse<T> (s:seq<T>):seq<T> 
{
    if s==[] then []
    else reverse(s[1..])+[s[0]]
}

function seq2set<T> (s:seq<T>): set<T>
{
    if s==[] then {}
    else {s[0]}+seq2set(s[1..])
}

lemma seq2setRev_Lemma<T> (s:seq<T>)
ensures seq2set(reverse(s)) == seq2set(s)
{
    if s==[]{}
    else {
        seq2setRev_Lemma(s[1..]);

        calc {
            seq2set(s);
            seq2set([s[0]]+s[1..]);
            {
                concat_seq2set_Lemma([s[0]], s[1..]);
            }
            seq2set([s[0]]) + seq2set(s[1..]);
            {
                seq2setRev_Lemma(s[1..]);
            }
            seq2set([s[0]]) + seq2set(reverse(s[1..]));
            seq2set(reverse(s[1..])) + seq2set([s[0]]); 
            {
                concat_seq2set_Lemma(reverse(s[1..]), [s[0]]);
            }
            seq2set(reverse(s[1..]) + [s[0]]);
            {
            }
            seq2set(reverse(s));
        }
    }
}

lemma concat_seq2set_Lemma<T>(s1:seq<T>,s2:seq<T>)
ensures seq2set(s1+s2) == seq2set(s1) + seq2set(s2)
{
    if s1==[]{
    }
    else {
        concat_seq2set_Lemma(s1[1..], s2);

        calc{
            seq2set(s1) + seq2set(s2);
            seq2set([s1[0]]+s1[1..]) + seq2set(s2);
            seq2set([s1[0]]) + seq2set(s1[1..]) + seq2set(s2);
            {
                concat_seq2set_Lemma(s1[1..], s2);
            }
            seq2set([s1[0]]) + seq2set(s1[1..]+s2);
            {
            }
            seq2set([s1[0]]) + seq2set((s1+s2)[1..]);
            {
                var ls:= s1+s2;
                calc {
                    seq2set([s1[0]]) + seq2set((s1+s2)[1..]);
                    seq2set([ls[0]])+ seq2set(ls[1..]);
                    seq2set([ls[0]]+ ls[1..]);
                    seq2set(ls);
                    seq2set(s1+s2);
                }
            }
            seq2set(s1+s2);
        }
    }
}
