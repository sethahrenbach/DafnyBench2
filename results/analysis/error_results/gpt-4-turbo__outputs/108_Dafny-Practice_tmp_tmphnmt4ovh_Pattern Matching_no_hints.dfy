method {:verify true} FindAllOccurrences(text: string, pattern: string) returns (offsets: set<nat>)
    ensures forall i :: i in offsets ==> i + |pattern| <= |text|
    ensures forall i :: 0 <= i <= |text| - |pattern| ==> (text[i..i+|pattern|] == pattern <==> i in offsets)
{
    offsets := {};
    var i: int := 0;
    if |pattern| > |text| {
        return offsets;
    }

    if pattern == "" {
        while i <= |text| {
            invariant 0 <= i <= |text|
            invariant forall k :: 0 <= k <= i ==> k in offsets
            offsets := offsets + {i};
            i := i + 1;
        }
        return offsets;
    }

    var pattern_hash: int := RecursiveSumDown(pattern);
    var text_hash: int := RecursiveSumDown(text[..|pattern|]);
    
    if pattern_hash == text_hash && text[..|pattern|] == pattern {
        offsets := offsets + {0};
    }

    i := 1; // Start from 1 because we already checked index 0 above
    while i < |text| - |pattern| + 1 {
        invariant 0 <= i < |text| - |pattern| + 1
        invariant forall k :: 0 <= k < i ==> (text[k..k+|pattern|] == pattern <==> k in offsets)
        invariant text_hash == RecursiveSumDown(text[i-1..i-1+|pattern|])
        var old_text_hash := text_hash;
        var left_letter_as_int := text[i-1] as int;
        var right_new_letter_as_int := text[i-1+|pattern|] as int;
        text_hash := text_hash - left_letter_as_int + right_new_letter_as_int;

        if pattern_hash == text_hash && text[i..i + |pattern|] == pattern {
            offsets := offsets + {i};
        }
        i := i + 1;
    }
    return offsets;
}