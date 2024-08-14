
module Split
{
  function split(s: string, separator: char): seq<string>
    requires 0 <= s.Length <= 100
    requires 0 <= separator.Length <= 100
    ensures 0 <= result.Length <= 100
    ensures result == splitHelper(s, separator, 0, 0, [])
  {
    if s.Length == 0 then
      []
    else if s[0] == separator then
      [s[0..]]
    else
      [s[0..]] + splitHelper(s[1..], separator, 0, 0, [])
  }

  function splitHelper(s: string, separator: char, index: nat, sindex: nat, results: seq<string>): seq<string>
    requires 0 <= s.Length <= 100
    requires 0 <= separator.Length <= 100
    requires 0 <= index <= s.Length
    requires 0 <= sindex <= s.Length
    requires 0 <= results.Length <= 100
    ensures 0 <= result.Length <= 100
    ensures result == splitHelper(s, separator, index + 1, sindex + 1, results + [s[index..sindex]])
  {
    if index == s.Length then
      results
    else if s[index] == separator then
      splitHelper(s, separator, index + 1, index + 1, results + [s[index..sindex]])
    else
      splitHelper(s, separator, index + 1, sindex, results)
  }
}
