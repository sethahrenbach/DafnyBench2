method insert(line:array<char>, l:int, nl:array<char>, p:int, at:int)
  requires 0 <= l+p <= line.Length
  requires 0 <= p <= nl.Length
  requires 0 <= at <= l
  modifies line
  ensures forall i :: (0<=i<p) ==> line[at+i] == nl[i]
  ensures forall i :: (0<=i<at) ==> line[i] == old(line[i])
  ensures forall i :: (at+p<=i<l+p) ==> line[i] == old(line[i-p])
{
  ghost var initialLine := line[..];

  var i:int := l;
  while(i>at)
    decreases i
    invariant at <= i <= l
    invariant forall j :: at <= j < i ==> line[j+p] == old(line[j])
    invariant forall j :: 0 <= j < at ==> line[j] == old(line[j])
    invariant forall j :: i <= j < l ==> line[j+p] == old(line[j])
    invariant line[..l+p] == initialLine[..at] + initialLine[at..i] + initialLine[i..l] + initialLine[l..l+p]
  {
    i := i - 1;
    line[i+p] := line[i];
  }

  i := 0;
  while(i<p)
    decreases p - i
    invariant 0 <= i <= p
    invariant forall j :: 0 <= j < i ==> line[at+j] == nl[j]
    invariant forall j :: i <= j < p ==> line[at+j] == old(line[at+j])
    invariant forall j :: 0 <= j < at ==> line[j] == initialLine[j]
    invariant forall j :: at + i <= j < at + p ==> line[j] == nl[j - at]
    invariant forall j :: at + p <= j < l + p ==> line[j] == initialLine[j - p]
  {
    line[at + i] := nl[i];
    i := i + 1;
  }

  assert forall i :: (0<=i<p) ==> line[at+i] == nl[i];
  assert forall i :: (0<=i<at) ==> line[i] == initialLine[i];
  assert forall i :: (at+p<=i<l+p) ==> line[i] == initialLine[i-p];
}