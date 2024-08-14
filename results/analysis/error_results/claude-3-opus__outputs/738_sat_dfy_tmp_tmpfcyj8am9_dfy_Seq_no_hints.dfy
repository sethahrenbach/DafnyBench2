module Seq {
    function seq_sum(s: seq<int>) : (sum: int)
    {
        if s == [] then
            0
        else
            var x := s[0];
            var remaining := s[1..];
            x + seq_sum(remaining)
    }

    lemma SeqPartsSameSum(s: seq<int>, s1: seq<int>, s2: seq<int>)
        requires s == s1 + s2
        ensures seq_sum(s) == seq_sum(s1) + seq_sum(s2)
    {
        if s == [] {
            assert s1 == [] && s2 == [];
        } else if s1 == [] {
            assert s == s2;
        } else {
            var x := s1[0];
            var s1' := s1[1..];
            assert s == [x] + s1' + s2;
            SeqPartsSameSum(s[1..], s1', s2);
            assert seq_sum(s) == x + seq_sum(s[1..]);
            assert seq_sum(s1) == x + seq_sum(s1');
        }
    }

    lemma DifferentPermutationSameSum(s1: seq<int>, s2: seq<int>)
        requires multiset(s1) == multiset(s2)
        ensures seq_sum(s1) == seq_sum(s2)
    {
        if s1 == [] {
            assert s2 == [];
        } else {
            var x :| x in s1;
            var i1 :| 0 <= i1 < |s1| && s1[i1] == x;
            var i2 :| 0 <= i2 < |s2| && s2[i2] == x;

            var remaining1 := s1[..i1] + s1[i1+1..];
            assert multiset(remaining1) == multiset(s1) - multiset{x};
            SeqPartsSameSum(s1, s1[..i1] + [x] + s1[i1+1..], []);
            assert seq_sum(s1) == seq_sum(s1[..i1]) + x + seq_sum(s1[i1+1..]);
            assert seq_sum(remaining1) == seq_sum(s1[..i1]) + seq_sum(s1[i1+1..]);

            var remaining2 := s2[..i2] + s2[i2+1..];
            assert multiset(remaining2) == multiset(s2) - multiset{x};
            SeqPartsSameSum(s2, s2[..i2] + [x] + s2[i2+1..], []);
            assert seq_sum(s2) == seq_sum(s2[..i2]) + x + seq_sum(s2[i2+1..]);
            assert seq_sum(remaining2) == seq_sum(s2[..i2]) + seq_sum(s2[i2+1..]);

            assert multiset(remaining1) == multiset(remaining2);
            DifferentPermutationSameSum(remaining1, remaining2);
            assert seq_sum(remaining1) == seq_sum(remaining2);
            calc == {
                seq_sum(s1);
                seq_sum(s1[..i1]) + x + seq_sum(s1[i1+1..]);
                seq_sum(remaining1) + x;
                seq_sum(remaining2) + x;
                seq_sum(s2[..i2]) + x + seq_sum(s2[i2+1..]);
                seq_sum(s2);
            }
        }
    }
}