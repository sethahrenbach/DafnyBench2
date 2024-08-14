method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  ensures count == |SetLessThan(numbers, threshold)|
{
  count := 0;
  var ss := numbers;
  while ss != {}
    decreases |ss|
    invariant count == |SetLessThan(numbers - ss, threshold)|
    invariant ss + (numbers - ss) == numbers
    invariant |ss| + count == |numbers| - |SetLessThan(numbers, threshold)|
    invariant forall x :: x in ss ==> x in numbers
  {
    var i: int :| i in ss;
    ss := ss - {i};
    if i < threshold {
      count := count + 1;
    }
  }
  assert count == |SetLessThan(numbers, threshold)|;
}

function SetLessThan(numbers: set<int>, threshold: int): set<int>
{
  set i | i in numbers && i < threshold
}

method Main()
{
  var t: seq<int> := [1, 2, 3];
  var s: set<int> := {1, 2, 3};

  s := set x | x in t;
  set_memebrship_implies_cardinality(s, set x | x in t);  
  var s2 : set<int> := set x | x in t;

  s2 := {1, 2, 3};
  set_memebrship_implies_cardinality(s, s2); 
}

lemma set_memebrship_implies_cardinality_helper<A>(s: set<A>, t: set<A>, s_size: int)
  requires s_size >= 0 && s_size == |s|
  requires forall x :: x in s <==> x in t
  ensures |s| == |t|
{
  if s_size == 0 {
  } else {
    var s_hd;
    s_hd :| s_hd in s;
    set_memebrship_implies_cardinality_helper(s - {s_hd}, t - {s_hd}, s_size - 1);
  }
}

lemma set_memebrship_implies_cardinality<A>(s: set<A>, t: set<A>)
  requires forall x :: x in s <==> x in t
  ensures |s| == |t| {
  set_memebrship_implies_cardinality_helper(s, t, |s|);
}

function seqSet(nums: seq<int>, index: nat): set<int> {
    set x | 0 <= x < index < |nums| :: nums[x]
}

lemma containsDuplicateI(nums: seq<int>) returns (containsDuplicate: bool)
    ensures containsDuplicate ==>  exists i,j :: 0 <= i < j < |nums| && nums[i] == nums[j]
{
    var windowGhost: set<int> := {};
    var windowSet: set<int> := {};
    for i:= 0 to |nums| 
        invariant forall x :: x in windowSet ==> x in nums
        invariant windowSet == set x | x in nums[..i]
    {
        windowGhost := windowSet;
        if nums[i] in windowSet {
            return true;
        }
        windowSet := windowSet + {nums[i]};
    }
    return false;
}

lemma set_memebrship_implies_equality_helper<A>(s: set<A>, t: set<A>, s_size: int)
  requires s_size >= 0 && s_size == |s|
  requires forall x :: x in s <==> x in t
  ensures s == t
{
  if s_size == 0 {
  } else {
    var s_hd;
    s_hd :| s_hd in s;
    set_memebrship_implies_equality_helper(s - {s_hd}, t - {s_hd}, s_size - 1);
  }
}

lemma set_memebrship_implies_equality<A>(s: set<A>, t: set<A>)
  requires forall x :: x in s <==> x in t
  ensures s == t {
  set_memebrship_implies_equality_helper(s, t, |s|);
}

lemma set_seq_equality(s: set<int>, t: seq<int>)
  requires distinct(t)
  requires forall x :: x in t <==> x in s
{
  var s2 : set<int> := set x | x in t;
  set_memebrship_implies_equality_helper(s, s2, |s|);
}

ghost predicate SortedSeq(a: seq<int>)
{
  (forall i,j :: 0<= i< j < |a| ==> ( a[i] < a[j] ))
}

method GetInsertIndex(a: array<int>, limit: int, x:int) returns (idx:int)
  requires x !in a[..]
  requires 0 <= limit <= a.Length
  requires SortedSeq(a[..limit])
  ensures 0<= idx <= limit
  ensures SortedSeq(a[..limit])
  ensures idx > 0 ==> a[idx-1]< x
  ensures idx < limit ==> x < a[idx]
{
  idx := limit;
  for i := 0 to limit
  {
    if x < a[i] {
      idx := i;
      break;
    }
  }
}

predicate sorted(a: seq<int>)
{
  forall i,j :: 0 <= i < j < |a| ==> a[i] < a[j]
}

predicate distinct(a: seq<int>)
{
  forall i,j :: (0 <= i < |a| && 0 <= j < |a| && i != j) ==> a[i] != a[j]
}

predicate sorted_eq(a: seq<int>)
{
  forall i,j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

predicate lessThan(a:seq<int>, key:int) {
  forall i :: 0 <= i < |a| ==> a[i] < key
}

predicate greaterThan(a:seq<int>, key:int) {
  forall i :: 0 <= i < |a| ==> a[i] > key
}

predicate greaterEqualThan(a:seq<int>, key:int) {
  forall i :: 0 <= i < |a| ==> a[i] >= key
}

lemma DistributiveLemma(a: seq<bool>, b: seq<bool>)
  ensures count(a + b) == count(a) + count(b)
{
  if a == [] {
  } else {
    DistributiveLemma(a[1..], b);
  }
}

function count(a: seq<bool>): nat
{
  if |a| == 0 then 0 else
    (if a[0] then 1 else 0) + count(a[1..])
}

lemma DistributiveIn(a: seq<int>, b:seq<int>, k:int, key:int)
    requires |a| + 1 == |b| 
    requires 0 <= k <= |a|
    requires b == a[..k] + [key] + a[k..]
    ensures forall i :: 0 <= i < |a| ==> a[i] in b
{
}

lemma DistributiveGreater(a: seq<int>, b:seq<int>, k:int, key:int)
    requires |a| + 1 == |b| 
    requires 0 <= k <= |a|
    requires b == a[..k] + [key] + a[k..]
    requires forall j :: 0 <= j < |a| ==> a[j] > 0
    requires key > 0
    ensures forall i :: 0 <= i < |b| ==> b[i] > 0
{
}

method InsertIntoSorted(a: array<int>, limit:int, key:int) returns (b: array<int>)
    requires key > 0
    requires key !in a[..]
    requires 0 <= limit < a.Length
    requires forall i :: 0 <= i < limit ==> a[i] > 0
    requires forall i :: limit <= i < a.Length ==> a[i] == 0
    requires sorted(a[..limit]) 
    ensures b.Length == a.Length
    ensures sorted(b[..(limit+ 1)])
    ensures forall i :: limit + 1 <= i < b.Length ==> b[i] == 0  
    ensures forall i :: 0 <= i < limit ==> a[i] in b[..]
    ensures forall i :: 0 <= i < limit + 1 ==> b[i] > 0
{
    b:= new int[a.Length];

    ghost var k := 0;
    b[0] := key;

    ghost var a' := a[..];

    var i:= 0;
    while (i < limit)
        modifies b
        invariant 0 <= i <= limit
        invariant sorted(a[..limit])
        invariant sorted(b[..i])
        invariant forall j :: 0 <= j < i ==> b[j] > 0
        invariant forall j :: i <= j < limit ==> a[j] > 0
        invariant forall j :: limit <= j < b.Length ==> b[j] == 0
        invariant forall j :: 0 <= j < i ==> a[j] in b[..]
        invariant forall j :: 0 <= j < limit ==> a[j] in a[..]
    {
        if(a[i]<key)
        {
            b[i]:= a[i];
            b[i+1] := key;
            k := i+1;
        }
        else if (a[i] >= key)
        {
            b[i+1] := a[i];
        } 
        i := i+1;
    }

    DistributiveIn(a[..limit], b[..limit+1], k, key);

    DistributiveGreater(a[..limit], b[..limit+1], k, key);

    ghost var b' := b[..];
    i := limit + 1;
    while i < b.Length 
        invariant limit + 1 <= i <= b.Length
        invariant forall j :: limit + 1 <= j < b.Length ==> b[j] == 0
    {
        b[i] := 0;
        i := i + 1;
    }
}