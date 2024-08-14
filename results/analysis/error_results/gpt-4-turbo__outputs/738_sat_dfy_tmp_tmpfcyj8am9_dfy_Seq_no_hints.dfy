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
            assert seq_sum(s) == 0;
            assert seq_sum(s1) + seq_sum(s2) == 0;
        } else if s1 == [] {
            assert seq_sum(s1) == 0;
            assert seq_sum(s) == seq_sum(s2);
        } else {
            var x := s1[0];
            var s1' := s1[1..];
            SeqPartsSameSum(s[1..], s1[1..], s2);
            assert seq_sum(s) == seq_sum(s1) + seq_sum(s2);
        }
    }

    lemma DifferentPermutationSameSum(s1: seq<int>, s2: seq<int>)
        requires multiset(s1) == multiset(s2)
        ensures seq_sum(s1) == seq_sum(s2)
    {
        if s1 == [] {
            assert seq_sum(s2) == 0;
        } else {
            var x :| x in s1;
            var remaining1 := s1;
            var remaining2 := s2;
            var found := false;

            for i1 := 0; i1 < |s1|; i1 := i1 + 1 {
                if s1[i1] == x {
                    remaining1 := s1[..i1] + s1[i1+1..];
                    found := true;
                    break;
                }
            }
            assert found; // Ensure x was found and removed from s1

            found := false;
            for i2 := 0; i2 < |s2|; i2 := i2 + 1 {
                if s2[i2] == x {
                    remaining2 := s2[..i2] + s2[i2+1..];
                    found := true;
                    break;
                }
            }
            assert found; // Ensure x was found and removed from s2

            DifferentPermutationSameSum(remaining1, remaining2);
            assert seq_sum(s1) == seq_sum(s2);
        }
    }
}