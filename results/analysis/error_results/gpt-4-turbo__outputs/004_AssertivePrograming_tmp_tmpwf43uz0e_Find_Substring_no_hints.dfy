// Noa Leron 207131871
// Tsuri Farhana 315016907

ghost predicate ExistsSubstring(str1: string, str2: string) {
    exists offset :: 0 <= offset <= |str1| && str2 <= str1[offset..];
}

ghost predicate Post(str1: string, str2: string, found: bool, i: nat) {
    (found <==> ExistsSubstring(str1, str2)) &&
    (found ==> i + |str2| <= |str1| && str2 <= str1[i..]);
}

method {:verify true} FindFirstOccurrence(str1: string, str2: string) returns (found: bool, i: nat)
    ensures Post(str1, str2, found, i)
{
    if |str2| == 0 {
        found := true;
        i := 0;
    } else if |str1| < |str2| {
        found := false;
        i := 0; // value of i irrelevant in this case
    } else {
        found := false;
        i := |str2|-1;

        while !found && i < |str1| {
            invariant 0 <= i <= |str1|
            invariant !found ==> !ExistsSubstring(str1[..i], str2);

            var j := |str2|-1;
            ghost var old_i := i;
            ghost var old_j := j;

            while !found && str1[i] == str2[j] {
                invariant 0 <= j <= |str2|
                invariant 0 <= i < |str1|
                invariant str1[i..] starts with str2[j..];

                if j == 0 {
                    found := true;
                } else {
                    i := i - 1;
                    j := j - 1;
                }
            }

            if !found {
                Lemma1(str1, str2, i, j, old_i, old_j, found);
                i := i + |str2| - j;
            }
        }
    }
}

method Main() {
    var str1a, str1b := "string", " in Dafny is a sequence of characters (seq<char>)";
    var str1, str2 := str1a + str1b, "ring";
    var found, i := FindFirstOccurrence(str1, str2);
    print "\nfound, i := FindFirstOccurrence(\"", str1, "\", \"", str2, "\") returns found == ", found;
    if found {
        print " and i == ", i;
    }
    str1 := "<= on sequences is the prefix relation";
    found, i := FindFirstOccurrence(str1, str2);
    print "\nfound, i := FindFirstOccurrence(\"", str1, "\", \"", str2, "\") returns found == ", found;
    if found {
        print " and i == ", i;
    }
}

lemma {:verify true} Lemma1(str1: string, str2: string, i: nat, j: int, old_i: nat, old_j: nat, found: bool)
    requires !found
    requires |str2| > 0
    requires old_j - j == old_i - i
    requires i + |str2| - j == old_i + 1
    requires old_i + 1 >= |str2|
    requires old_i + 1 <= |str1|
    requires 0 <= i < |str1| && 0 <= j < |str2|
    requires str1[i] != str2[j]
    requires !ExistsSubstring(str1[..old_i], str2)
    ensures !ExistsSubstring(str1[..old_i + 1], str2)
{
    // Proof of lemma goes here
}