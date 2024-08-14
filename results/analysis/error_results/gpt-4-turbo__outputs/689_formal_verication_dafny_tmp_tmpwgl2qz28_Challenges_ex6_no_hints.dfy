
function bullspec(s:seq<nat>, u:seq<nat>): nat
  requires 0 <= |u| == |s| && nomultiples(u)
{
  reccbull(s, u, 0)
}

function cowspec(s:seq<nat>, u:seq<nat>): nat
  requires 0 <= |u| == |s| && nomultiples(u)
{
  recccow(s, u, 0)
}

function reccbull(s: seq<nat>, u:seq<nat>, i:int): nat
  requires 0 <= i <= |s| == |u|
  decreases |s| - i
{
  if i == |s| then 0
  else if s[i] == u[i] then 1 + reccbull(s, u, i + 1)
  else reccbull(s, u, i + 1)
}

function recccow(s: seq<nat>, u:seq<nat>, i:int): nat
  requires 0 <= i <= |s| == |u|
  decreases |s| - i
{
  if i == |s| then 0
  else if s[i] != u[i] && u[i] in s then 1 + recccow(s, u, i + 1)
  else recccow(s, u, i + 1)
}

predicate nomultiples(u:seq<nat>) 
{
  forall j, k :: 0 <= j < k < |u| ==> u[j] != u[k]
}

method BullsCows(s:seq<nat>, u:seq<nat>) returns (b:nat, c:nat)
  requires 0 < |u| == |s| <= 10 && nomultiples(u) && nomultiples(s)
  ensures b >= 0 && c >= 0
  ensures b == bullspec(s, u)
  ensures c == cowspec(s, u)
{
  b, c := 0, 0;
  var i := |s|;
  while i > 0
    decreases i
    invariant 0 <= i <= |s|
    invariant b + c <= |s| - i
    invariant b == bullspec(s[..|s|-i], u[..|s|-i])
    invariant c == cowspec(s[..|s|-i], u[..|s|-i])
  {
    i := i - 1;
    if s[i] == u[i] {
      b := b + 1;
    } else if u[i] in s && s[i] != u[i] {
      c := c + 1;
    }
  }
}
