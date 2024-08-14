// RUN: /compile:0

predicate reversed (arr : array<char>, outarr: array<char>)
requires arr != null && outarr != null
requires arr.Length == outarr.Length
reads arr, outarr
{
  forall k :: 0<=k<arr.Length ==> outarr[k] == arr[(arr.Length-1-k)]
}

method yarra(arr : array<char>) returns (outarr : array<char>)
requires arr != null && arr.Length > 0
ensures outarr != null && arr.Length == outarr.Length && reversed(arr,outarr)
{
  var i:= 0;
  var j:= arr.Length-1;
  outarr := new char[arr.Length];
  while i<arr.Length
    invariant 0 <= i <= arr.Length
    invariant -1 <= j < arr.Length
    invariant outarr != null && outarr.Length == arr.Length
    invariant forall k :: 0 <= k < i ==> outarr[k] == arr[arr.Length-1-k]
  {
    outarr[i] := arr[j];
    i:=i+1;
    j:=j-1;
  }
  assert reversed(arr, outarr);
  return outarr;
}

method Main()
{
  var s := ['a','b','a','b','a','b','a','b','a','b','a','b'];
  var a,b,c,d := new char[5], new char[5], new char[5], new char[5];
  a[0], a[1], a[2], a[3], a[4] := 'y', 'a', 'r', 'r', 'a';
  d[0], d[1], d[2], d[3], d[4] := 'y', 'a', 'r', 'r', 'a';
  b := yarra(a);
  c := yarra(b);
  assert c.Length == a.Length;
  assert d[0] == a[0];
  print c; print a;
}