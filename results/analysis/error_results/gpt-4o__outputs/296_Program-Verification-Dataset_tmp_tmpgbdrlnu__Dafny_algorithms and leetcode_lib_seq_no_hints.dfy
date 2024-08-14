module Seq {
    export reveals *
    function ToSet<A>(xs: seq<A>): set<A>
        ensures forall x :: x in ToSet(xs) ==> x in xs
        ensures forall x :: x !in ToSet(xs) ==> x !in xs
    {
        if xs == [] then {} else {xs[0]} + ToSet(xs[1..])
    }

    predicate substring1<A(==)>(sub: seq<A>, super: seq<A>) {
        exists k :: 0 <= k < |super| && sub <= super[k..]
    }

    ghost predicate isSubstringAlt<A(!new)>(sub: seq<A>, super: seq<A>) {
        |sub| <= |super| && exists xs: seq<A> :: IsSuffix(xs, super) && sub <= xs
    }

    predicate isSubstring<A(==)>(sub: seq<A>, super: seq<A>) {
        |sub| <= |super| && exists k, j :: 0 <= k < j <= |super| && sub == super[k..j]
    }

    lemma SliceOfSliceIsSlice<A>(xs: seq<A>, k: int, j: int, s: int, t: int)
        requires 0 <= k <= j <= |xs|
        requires 0 <= s <= t <= j - k
        ensures xs[k..j][s..t] == xs[(k + s)..(k + s + (t - s))]
    {
        if j - k == 0 {
        } else if t - s == 0 {
        } else if t - s > 0 {
            SliceOfSliceIsSlice(xs, k, j, s, t - 1);
            assert xs[k..j][s..t] == xs[(k + s)..(k + s + (t - s))];
        }
    }

    lemma AllSubstringsAreSubstrings<A>(subsub: seq<A>, sub: seq<A>, super: seq<A>)
        requires isSubstring(sub, super)
        requires isSubstring(subsub, sub)
        ensures isSubstring(subsub, super)
    {
        var k, j :| 0 <= k < j <= |super| && sub == super[k..j];
        var s, t :| 0 <= s < t <= |sub| && subsub == sub[s..t];
        if t < j {
            calc {
                subsub;
                super[k..j][s..t];
                {SliceOfSliceIsSlice(super, k, j, s, t);}
                super[(k + s)..(k + s + (t - s))];
            }
        } else if t <= j {
            assert isSubstring(subsub, super);
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
        ensures exists yss: seq<T> :: ys == xs + yss && |yss| == |ys| - |xs|
    {
        assert exists yss: seq<T> :: ys == xs + ys[|xs|..] && |ys[|xs|..]| == |ys| - |xs|;
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
        var yss :| reverse(ys) == reverse(xs) + yss && |yss| == |ys| - |xs|;
        reverseReverseIdempotent(ys);
        ReverseConcat(reverse(xs), yss);
        calc {
            reverse(reverse(ys));
            ys;
            reverse(reverse(xs) + yss);
            reverse(yss) + reverse(reverse(xs));
            == {reverseReverseIdempotent(xs);}
            reverse(yss) + xs;
        }
    }

    predicate IsSuffix2<T(==)>(xs: seq<T>, ys: seq<T>) {
        |xs| <= |ys| && exists K :: 0 <= K <= |ys| - |xs| && ys == ys[0..K] + xs + ys[(K + |xs|)..]
    }

    function reverse<A>(x: seq<A>): seq<A>
    {
        if x == [] then [] else reverse(x[1..]) + [x[0]]
    }

    lemma {:induction false} reversePreservesMultiset<A>(xs: seq<A>)
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
        if xs == [] {
        } else {
            reversePreservesLength(xs[1..]);
            assert |xs| == 1 + |xs[1..]|;
            assert |reverse(xs)| == 1 + |reverse(xs[1..])|;
        }
    }

    lemma lastReverseIsFirst<A>(xs: seq<A>)
        requires |xs| > 0
        ensures xs[0] == reverse(xs)[|reverse(xs)| - 1]
    {
        reversePreservesLength(xs);
        if |xs| == 1 {
            assert xs[0] == reverse(xs)[0];
        } else {
            lastReverseIsFirst(xs[1..]);
            assert xs[0] == reverse(xs)[|reverse(xs)| - 1];
        }
    }

    lemma firstReverseIsLast<A>(xs: seq<A>)
        requires |xs| > 0
        ensures reverse(xs)[0] == xs[|xs| - 1]
    {
        reversePreservesLength(xs);
        if |xs| == 1 {
            assert reverse(xs)[0] == xs[0];
        } else {
            firstReverseIsLast(xs[1..]);
            assert reverse(xs)[0] == xs[|xs| - 1];
        }
    }

    lemma ReverseConcat<T>(xs: seq<T>, ys: seq<T>)
        ensures reverse(xs + ys) == reverse(ys) + reverse(xs)
    {
        if |xs| == 0 {
            assert reverse(xs + ys) == reverse(ys);
            assert reverse(ys) + reverse(xs) == reverse(ys);
        } else {
            ReverseConcat(xs[1..], ys);
            assert reverse(xs + ys) == reverse(xs[1..] + ys) + [xs[0]];
            assert reverse(ys) + reverse(xs) == reverse(ys) + (reverse(xs[1..]) + [xs[0]]);
        }
    }

    lemma reverseRest<A>(xs: seq<A>)
        requires |xs| > 0
        ensures reverse(xs) == [xs[|xs| - 1]] + reverse(xs[0..|xs| - 1])
    {
        firstReverseIsLast(xs);
        calc {
            reverse(xs);
            reverse(xs[0..|xs| - 1] + [xs[|xs| - 1]]);
            == {ReverseConcat(xs[0..|xs| - 1], [xs[|xs| - 1]]);}
            reverse([xs[|xs| - 1]]) + reverse(xs[0..|xs| - 1]);
        }
    }

    lemma ReverseIndexAll<T>(xs: seq<T>)
        ensures |reverse(xs)| == |xs|
        ensures forall i :: 0 <= i < |xs| ==> reverse(xs)[i] == xs[|xs| - i - 1]
    {
        reversePreservesLength(xs);
        if |xs| == 0 {
        } else {
            ReverseIndexAll(xs[1..]);
            assert reverse(xs)[0] == xs[|xs| - 1];
            assert reverse(xs)[|xs| - 1] == xs[0];
        }
    }

    lemma ReverseIndex<T>(xs: seq<T>, i: int)
        requires 0 <= i < |xs|
        ensures |reverse(xs)| == |xs|
        ensures reverse(xs)[i] == xs[|xs| - i - 1]
    {
        ReverseIndexAll(xs);
    }

    lemma ReverseIndexBack<T>(xs: seq<T>, i: int)
        requires 0 <= i < |xs|
        ensures |reverse(xs)| == |xs|
        ensures reverse(xs)[|xs| - i - 1] == xs[i]
    {
        ReverseIndexAll(xs);
    }

    lemma ReverseSingle<A>(xs: seq<A>)
        requires |xs| == 1
        ensures reverse(xs) == xs
    {
        assert reverse(xs) == xs;
    }

    lemma SeqEq<T>(xs: seq<T>, ys: seq<T>)
        requires |xs| == |ys|
        requires forall i :: 0 <= i < |xs| ==> xs[i] == ys[i]
        ensures xs == ys
    {
        if |xs| == 0 {
            assert xs == ys;
        } else {
            SeqEq(xs[1..], ys[1..]);
            assert xs == ys;
        }
    }

    lemma reverseReverseIdempotent<A>(xs: seq<A>)
        ensures reverse(reverse(xs)) == xs
    {
        if xs == [] {
        } else {
            calc {
                reverse(reverse(xs));
                reverse(reverse([xs[0]] + xs[1..]));
                == {ReverseConcat([xs[0]], xs[1..]);}
                reverse(reverse(xs[1..]) + reverse([xs[0]]));
                == {ReverseSingle([xs[0]]);}
                reverse(reverse(xs[1..]) + [xs[0]]);
                == {ReverseConcat(reverse(xs[1..]), [xs[0]]);}
                reverse([xs[0]]) + reverse(reverse(xs[1..]));
                [xs[0]] + reverse(reverse(xs[1..]));
                == {reverseReverseIdempotent(xs[1..]);}
                xs;
            }
        }
    }

    lemma notInNotEqual<A>(xs: seq<A>, elem: A)
        requires elem !in xs
        ensures forall k :: 0 <= k < |xs| ==> xs[k] != elem
    {
        forall k | 0 <= k < |xs|
            ensures xs[k] != elem
        {
            assert xs[k] != elem;
        }
    }

    predicate distinct<A(==)>(s: seq<A>) {
        forall x, y :: x != y && 0 <= x <= y < |s| ==> s[x] != s[y]
    }

    lemma distincts<A>(xs: seq<A>, ys: seq<A>)
        requires distinct(xs)
        requires distinct(ys)
        requires forall x :: x in xs ==> x !in ys
        requires forall y :: y in ys ==> y !in xs
        ensures distinct(xs + ys)
    {
        var len := |xs + ys|;
        forall x, y | x != y && 0 <= x <= y < |xs + ys|
            ensures (xs + ys)[x] != (xs + ys)[y]
        {
            if 0 <= x < |xs| && 0 <= y < |xs| {
                assert (xs + ys)[x] != (xs + ys)[y];
            } else if |xs| <= x < |xs + ys| && |xs| <= y < |xs + ys| {
                assert (xs + ys)[x] != (xs + ys)[y];
            } else if 0 <= x < |xs| && |xs| <= y < |xs + ys| {
                notInNotEqual(ys, xs[x]);
                assert (xs + ys)[x] != (xs + ys)[y];
            }
        }
    }

    lemma reverseDistinct<A>(list: seq<A>)
        requires distinct(list)
        ensures distinct(reverse(list))
    {
        ReverseIndexAll(list);
        forall x, y | x != y && 0 <= x <= y < |reverse(list)|
            ensures reverse(list)[x] != reverse(list)[y]
        {
            assert reverse(list)[x] != reverse(list)[y];
        }
    }

    lemma distinctSplits<A>(list: seq<A>)
        requires distinct(list)
        ensures forall i :: 1 <= i < |list| ==> distinct(list[..i])
    {
        forall i | 1 <= i < |list|
            ensures distinct(list[..i])
        {
            assert distinct(list[..i]);
        }
    }

    lemma multisetItems<A>(list: seq<A>, item: A)
        requires item in list
        requires multiset(list)[item] > 1
        ensures exists i, j :: 0 <= i < j < |list| && list[i] == item && list[j] == item && i != j
    {
        var k :| 0 <= k < |list| && list[k] == item;
        var rest := list[..k] + list[k + 1..];
        assert exists i, j :: 0 <= i < j < |list| && list[i] == item && list[j] == item && i != j;
    }

    lemma distinctMultisetIs1<A>(list: seq<A>, item: A)
        requires distinct(list)
        requires item in list
        ensures multiset(list)[item] == 1
    {
        if multiset(list)[item] == 0 {
        }
        if multiset(list)[item] > 1 {
            multisetItems(list, item);
            var i, j :| 0 <= i < j < |list| && list[i] == item && list[j] == item && i != j;
            assert false;
        }
    }

    lemma indistinctMultisetIsGreaterThan1<A>(list: seq<A>)
        requires !distinct(list)
        ensures exists item :: multiset(list)[item] > 1
    {
        var x, y :| x != y && 0 <= x <= y < |list| && list[x] == list[y];
        var item := list[x];
        assert multiset(list)[item] > 1;
    }

    lemma multisetIsGreaterThan1Indistinct<A>(list: seq<A>)
        requires exists item :: multiset(list)[item] > 1
        ensures !distinct(list)
    {
        var item :| multiset(list)[item] > 1;
        var x :| 0 <= x < |list| && list[x] == item;
        var y :| x != y && 0 <= y < |list| && list[y] == item;
        assert !distinct(list);
    }

    lemma indistinctPlusX<A>(items: seq<A>, x: A)
        requires !distinct(items)
        ensures forall i :: 0 <= i < |items| ==> !distinct(items[..i] + [x] + items[i..])
    {
        forall i | 0 <= i < |items|
            ensures !distinct(items[..i] + [x] + items[i..])
        {
            indistinctMultisetIsGreaterThan1(items);
            var item :| multiset(items)[item] > 1;
            var itemsPlus := items[..i] + [x] + items[i..];
            calc {
                multiset(itemsPlus);
                multiset(items[..i]) + multiset(items[i..]) + multiset{x};
                multiset(items) + multiset{x};
            }
            multisetIsGreaterThan1Indistinct(itemsPlus);
        }
    }

    lemma pigeonHolesMultiset<A>(items: set<A>, list: seq<A>, n: nat)
        requires |items| == n
        requires forall x :: x in list ==> x in items
        requires |list| > n
        ensures exists item :: multiset(list)[item] > 1
    {
        if x :| multiset(list)[x] > 1 {
        } else if x :| multiset(list)[x] == 1 {
            var i :| 0 <= i < |list| && list[i] == x;
            var rest := list[..i] + list[i + 1..];
            forall y | y in rest
                ensures y in items - {x}
            {
                assert y in items - {x};
            }
            if n - 1 == 0 {
                assert |items| == 1;
                assert x in items;
            } else {
                pigeonHolesMultiset(items - {x}, rest, n - 1);
                var item :| multiset(rest)[item] > 1;
                assert multiset(list)[item] > 1;
            }
        } else if x :| multiset(list)[x] == 0 {}
    }

    lemma pigeonHoles<A>(items: set<A>, list: seq<A>, n: nat)
        requires |items| == n
        requires forall x :: x in list ==> x in items
        requires |list| > n
        ensures !distinct(list)
    {
        if x :| multiset(list)[x] > 1 {
            multisetItems(list, x);
            var i, j :| 0 <= i < j < |list| && list[i] == x && list[j] == x && i != j;
            assert !distinct(list);
        } else if x :| multiset(list)[x] == 1 {
            var i :| 0 <= i < |list| && list[i] == x;
            var rest := list[..i] + list[i + 1..];
            forall y | y in rest
                ensures y in items - {x}
            {
                assert y in items - {x};
            }
            pigeonHoles(items - {x}, rest, n - 1);
            indistinctPlusX(rest, x);
            assert !distinct(list);
        } else if x :| multiset(list)[x] == 0 {}
    }

    lemma reverseInitList<T>(xs: seq<T>)
        requires |xs| > 1
        requires |reverse(xs)| == |xs|
        ensures reverse(reverse(xs)[..|xs| - 1]) == xs[