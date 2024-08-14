// Noa Leron 207131871
// Tsuri Farhana 315016907

ghost predicate ExistsSubstring(str1: string, str2: string) {
	// string in Dafny is a sequence of characters (seq<char>) and <= on sequences is the prefix relation
	exists offset :: 0 <= offset <= |str1| && str2 <= str1[offset..]
}

ghost predicate Post(str1: string, str2: string, found: bool, i: nat) {
	(found <==> ExistsSubstring(str1, str2)) &&
	(found ==> i + |str2| <= |str1| && str2 <= str1[i..])
}

/*
Goal: Verify correctness of the following code. Once done, remove the {:verify false} (or turn it into {:verify true}).

Feel free to add GHOST code, including calls to lemmas. But DO NOT modify the specification or the original (executable) code.
*/
method {:verify true} FindFirstOccurrence(str1: string, str2: string) returns (found: bool, i: nat)
	ensures Post(str1, str2, found, i)
{
	if |str2| == 0 {
		found, i := true, 0;
	}
	else if |str1| < |str2| {
		found, i := false, 0; // value of i irrelevant in this case
	}
	else {
		found, i := false, |str2|-1;

		while !found && i < |str1|
			invariant !found ==> i <= |str1| 
			invariant found ==> i + |str2| <= |str1| && str2 <= str1[i..]
			invariant !found && 0 < i <= |str1| && i != |str2|-1 ==> !(ExistsSubstring(str1[..i], str2))
		{
			var j := |str2|-1;
			ghost var old_i := i;
            ghost var old_j := j;

			while !found && str1[i] == str2[j]
				invariant 0 <= j <= i
				invariant j < |str2| 
				invariant i < |str1|
				invariant str1[i] == str2[j] ==> str2[j..] <= str1[i..]
				invariant found ==> j==0 && str1[i] == str2[j]
				invariant old_j - j == old_i - i
			{
				if j == 0 {
					found := true;
				}
				else {
					i, j := i-1, j-1;
				}
			}

			if !found {
				assert old_i+1 >= |str2|;
				assert old_i+1 <= |str1|;
				assert 0 <= i < |str1| && 0 <= j < |str2|;
				assert str1[i] != str2[j];
				assert |str2| > 0;
				assert 0 < old_i <= |str1| ==> !(ExistsSubstring(str1[..old_i], str2));
				assert i+|str2|-j == old_i + 1;
				Lemma1(str1, str2, i, j, old_i, old_j, found);
				i := i+|str2|-j;
			}
		}
	}
}

lemma {:verify true} Lemma1 (str1: string, str2: string, i : nat, j: int, old_i: nat, old_j: nat, found: bool)
	requires !found;
	requires |str2| > 0;
	requires !found ==> old_i <= |str1|;
	requires found ==> old_i + |str2| <= |str1| && str2 <= str1[old_i..];
	requires !found && 0 < old_i <= |str1| && old_i != |str2|-1 ==> !(ExistsSubstring(str1[..old_i], str2));
	requires i+|str2|-j == old_i + 1;
	requires old_i+1 >= |str2|;
	requires old_i+1 <= |str1|;
	requires 0 <= i < |str1| && 0 <= j < |str2|;
	requires str1[i] != str2[j];
	requires 0 < old_i <= |str1| ==> !(ExistsSubstring(str1[..old_i], str2));
	ensures 0 < old_i+1 <= |str1| ==> !(ExistsSubstring(str1[..old_i+1], str2));
{
	if 0 < old_i+1 <= |str1| {
		if ExistsSubstring(str1[..old_i+1], str2) {
			Lemma2(str1, str2, old_i);
			assert str2 <= str1[old_i+1 - |str2| .. old_i+1];
			assert str1[i] != str2[j];
			assert str1[old_i+1 - |str2|] != str2[0];
			assert !(str2 <= str1[old_i+1 - |str2| .. old_i+1]); // contradiction
		}
	}
}

lemma {:verify true} Lemma2 (str1: string, str2: string, i : nat)
	requires 0 <= i < |str1|;
	requires 0 < |str2| <= i+1;
	requires !ExistsSubstring(str1[..i], str2);
	requires ExistsSubstring(str1[..i+1], str2);
	ensures str2 <= str1[i+1 - |str2| .. i+1];
{
	var offset :| 0 <= offset <= i+1 && str2 <= str1[offset..i+1];
	assert offset <= i ==> !(str2 <= str1[offset..i]);
	Lemma3(str1, str2, i);
	assert offset == i+1 - |str2|;
}

lemma Lemma3(str1: string, str2: string, i : nat)
	requires 0 <= i < |str1|;
	requires 0 < |str2| <= i+1;
	requires exists offset :: (0 <= offset <= i+1) && str2 <= str1[offset..i+1];
	requires forall offset :: 0 <= offset <= i+1 ==> (offset <= i ==> !(str2 <= str1[offset..i]));
	ensures exists offset :: (0 <= offset <= i+1) && (str2 <= str1[offset..i+1]) && (offset <= i ==> !(str2 <= str1[offset..i]));
{
	var offset :| (0 <= offset <= i+1) && str2 <= str1[offset..i+1];
	assert offset <= i ==> !(str2 <= str1[offset..i]);
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