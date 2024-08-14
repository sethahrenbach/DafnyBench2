module Split {
    function splitHelper(s: string, separator: string, index: nat, sindex: nat, results: seq<string>): seq<string>
        requires index <= |s|
        requires sindex <= |s|
        requires sindex <= index
        ensures forall ss :: ss in splitHelper(s, separator, index, sindex, results) ==> !Contains(ss, separator)
        decreases |s| - index
    {
        if index >= |s| then results + [s[sindex..index]]
        else if |separator| == 0 && index == |s|-1 then splitHelper(s, separator, index+1, index, results)
        else if |separator| == 0 then 
            splitHelper(s, separator, index+1, index+1, results + [s[sindex..(index+1)]])
        else if index+|separator| > |s| then splitHelper(s, separator, |s|, sindex, results)
        else if s[index..index+|separator|] == separator then splitHelper(s, separator, index+|separator|, index+|separator|, results + [s[sindex..index]])
        else splitHelper(s, separator, index+1, sindex, results)
    }

    function split(s: string, separator: string): seq<string> 
        ensures split(s, separator) == splitHelper(s, separator, 0,0, [])
    {
        splitHelper(s, separator, 0, 0, [])
    }

    predicate Contains(haystack: string, needle: string)
        ensures Contains(haystack, needle) <==> exists k :: 0 <= k < |haystack| - |needle| + 1 && haystack[k..k+|needle|] == needle
    {
        if |needle| > |haystack| then false
        else if needle == haystack[0..|needle|] then true
        else Contains(haystack[1..], needle)
    }

    function splitOnBreak(s: string): seq<string> {
        if Contains(s, "\r\n") then split(s,"\r\n") else split(s,"\n")
    }

    function splitOnDoubleBreak(s: string): seq<string> {
        if Contains(s, "\r\n\r\n") then split(s,"\r\n\r\n") else split(s,"\n\n")
    }
}