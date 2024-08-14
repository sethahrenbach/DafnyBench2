module Seq {
    export reveals *
    function ToSet<A>(xs: seq<A>): set<A>
        ensures forall x :: x in ToSet(xs) ==> x in xs
        ensures forall x :: x !in ToSet(xs) ==> x !in xs
    {
        if xs == [] then {} else {xs[0]}+ToSet(xs[1..])
    }

    predicate substring1<A(==)>(sub: seq<A>, super: seq<A>) {
        exists k :: 0 <= k < |super| && sub <= super[k..]
    }

    ghost predicate isSubstringAlt<A(!new)>(sub: seq<A>, super: seq<A>) {
        |sub| <= |super| && exists xs: seq<A> :: IsSuffix(xs, super) && sub <= xs
    }

    predicate isSubstring<A(==)>(sub: seq<A>, super: seq<A>) {
        |sub| <= |super| && exists k,j :: 0 <= k < j <= |super| && sub == super[k..j]
    }

    lemma SliceOfSliceIsSlice<A>(xs: seq<A>, k: int, j: int, s: int, t: int)
        requires 0 <= k <= j <= |xs|
        requires 0 <= s <= t <= j-k
        ensures xs[k..j][s..t] == xs[(k+s)..(k+t)]
    {
        if j-k == 0 {
        } else if t-s == 0 {
        } else if t-s > 0 {
            SliceOfSliceIsSlice(xs, k, j, s, t-1);
        }
    }

    lemma AllSubstringsAreSubstrings<A>(subsub: seq<A>, sub: seq<A>, super: seq<A>)
        requires isSubstring(sub, super)
        requires isSubstring(subsub, sub)
        ensures isSubstring(subsub, super)
    {
        var k, j :| 0 <= k < j <= |super| && sub == super[k..j];
        var s, t :| 0 <= s < t <= |sub| && subsub == sub[s..t];
        calc {
            subsub;
            == sub[s..t];
            == super[k..j][s..t];
            { SliceOfSliceIsSlice(super, k, j, s, t); }
            == super[(k+s)..(k+t)];
        }
    }

    predicate IsSuffix<T(==)>(xs: seq<T>, ys: seq<T>) {
        |xs| <= |ys| && xs == ys[|ys| - |xs|..]
    }

    predicate IsPrefix<T(==)>(xs: seq<T>, ys: seq<T>) {
        |xs| <= |ys| && xs == ys[..|xs|]
    }

    lemma PrefixRest<T>(xs: seq<T>, ys: seq<T>)
        requires IsPrefix(xs, ys)
        ensures exists yss: seq<T> :: ys == xs + yss && |yss| == |ys|-|xs|
    {
    }

    lemma IsSuffixReversed<T>(xs: seq<T>, ys: seq<T>)
        requires IsSuffix(xs, ys)
        ensures IsPrefix(reverse(xs), reverse(ys))
    {
        ReverseIndexAll(xs);
        ReverseIndexAll(ys);
    }

    lemma IsPrefixReversed<T>(xs: seq<T>, ys: seq<T>)
        requires IsPrefix(xs, ys)
        ensures IsSuffix(reverse(xs), reverse(ys))
    {
        ReverseIndexAll(xs);
        ReverseIndexAll(ys);
    }

    lemma IsPrefixReversedAll<T>(xs: seq<T>, ys: seq<T>)
        requires IsPrefix(reverse(xs), reverse(ys))
        ensures IsSuffix(reverse(reverse(xs)), reverse(reverse(ys)))
    {
        ReverseIndexAll(xs);
        ReverseIndexAll(ys);
        PrefixRest(reverse(xs), reverse(ys));
        var yss :| reverse(ys) == reverse(xs) + yss && |yss| == |ys|-|xs|;
        reverseReverseIdempotent(ys);
        ReverseConcat(reverse(xs), yss);
        calc {
            reverse(reverse(ys));
            ys;
            reverse(reverse(xs) + yss);
            reverse(yss)+reverse(reverse(xs));
            == {reverseReverseIdempotent(xs);}
            reverse(yss)+xs;
        }
    }

    function reverse<A>(x: seq<A>): seq<A> 
    {
        if x == [] then [] else reverse(x[1..])+[x[0]]
    }

    lemma reversePreservesMultiset<A>(xs: seq<A>) 
        ensures multiset(xs) == multiset(reverse(xs))
    {
        if xs == [] {

        } else {
            var x := xs[0];
            reversePreservesMultiset(xs[1..]);
        }
    }

    lemma reversePreservesLength<A>(xs: seq<A>)
        ensures |xs| == |reverse(xs)|
    {
    }

    lemma lastReverseIsFirst<A>(xs: seq<A>)
        requires |xs| > 0
        ensures xs[0] == reverse(xs)[|reverse(xs)|-1]
    {
        reversePreservesLength(xs);
    }

    lemma firstReverseIsLast<A>(xs: seq<A>)
        requires |xs| > 0
        ensures reverse(xs)[0] == xs[|xs|-1]
    {
    }

    lemma ReverseConcat<T>(xs: seq<T>, ys: seq<T>)
        ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
    {
        if |xs| == 0 {
        } else {
        }
    }

    lemma ReverseIndexAll<T>(xs: seq<T>)
        ensures |reverse(xs)| == |xs|
        ensures forall i :: 0 <= i < |xs| ==> reverse(xs)[i] == xs[|xs| - i - 1]
    {
    }

    lemma reverseReverseIdempotent<A>(xs: seq<A>) 
        ensures reverse(reverse(xs)) == xs
    {
        if xs == [] {

        } else {
            calc {
                reverse(reverse(xs));
                reverse(reverse([xs[0]] + xs[1..]));
                == {ReverseConcat([xs[0]] , xs[1..]);}
                reverse(reverse(xs[1..]) + reverse([xs[0]]));
                == {ReverseConcat(reverse(xs[1..]), [xs[0]]);}
                reverse([xs[0]]) + reverse(reverse(xs[1..]));
                [xs[0]] + reverse(reverse(xs[1..]));
                == {reverseReverseIdempotent(xs[1..]);}
                xs;
            }
        }
    }

    lemma SeqTest() {
        var t1 := [4,5,6,1,2,3];
        var s1 := [1,2,3];
    }

}