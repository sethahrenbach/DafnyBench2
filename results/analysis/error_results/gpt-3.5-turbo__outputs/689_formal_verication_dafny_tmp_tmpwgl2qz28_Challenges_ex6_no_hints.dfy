
// see pdf 'ex6 & 7 documentation' for excercise question

function bullspec(s: seq<nat>, u: seq<nat>): nat
  requires 0 <= |u| == |s| && nomultiples(u)
{ reccbull(s, u, 0) }

function cowspec(s: seq<nat>, u: seq<nat>): nat
  requires 0 <= |u| == |s| && nomultiples(u)
{ recccow(s, u, 0) }

function reccbull(s: seq<nat>, u: seq<nat>, i: int): nat
  requires 0 <= i <= |s| == |u|
{
  if i == |s| then 0
  else if s[i] == u[i] then reccbull(s, u, i + 1) + 1
  else reccbull(s, u, i + 1)
}

function recccow(s: seq<nat>, u: seq<nat>, i: int): nat
  requires 0 <= i <= |s| == |u|
{
  if i == |s| then 0
  else if s[i] != u[i] && u[i] in s then recccow(s, u, i + 1) + 1
  else recccow(s, u, i + 1)
}

predicate nomultiples(u: seq<nat>)
{
  forall j, k :: 0 <= j < k < |u| ==> u[j] != u[k]
}

method BullsCows(s: seq<nat>, u: seq<nat>) returns (b: nat, c: nat)
  requires 0 < |u| == |s| <= 10
  requires nomultiples(u) && nomultiples(s)
  ensures b >= 0 && c >= 0
  ensures b == bullspec(s, u)
  ensures c == cowspec(s, u)
{
  var bCount := 0;
  var cCount := 0;
  var i := |s|;

  while i > 0
    invariant 0 <= i <= |s|
    invariant 0 <= bCount <= |s|
    invariant 0 <= cCount <= |s|
    decreases i
  {
    i := i - 1;
    if s[i] != u[i] && u[i] in s {
      cCount := cCount + 1;
    } else if s[i] == u[i] {
      bCount := bCount + 1;
    }
  }

  return bCount, cCount;
}

method TEST() {
  var sys := [1, 2, 9, 10];
  var usr := [1, 2, 3, 7];
  var b1, c1 := BullsCows(sys, usr);

  var sys1 := [1, 2, 3, 4];
  var usr1 := [4, 3, 2, 1];
  var b2, c2 := BullsCows(sys1, usr1);

  var sys2 := [1, 2, 3, 4, 5, 6, 7];
  var usr2 := [1, 2, 3, 4, 5, 6, 7];
  var b3, c3 := BullsCows(sys2, usr2);

  var sys3 := [1, 2, 3, 4, 5, 6, 7];
  var usr3 := [1, 2, 3, 7, 8, 6, 5];
  var b4, c4 := BullsCows(sys3, usr3);
}
