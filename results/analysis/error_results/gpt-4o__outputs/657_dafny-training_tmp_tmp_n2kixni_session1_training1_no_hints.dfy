/*
 * Copyright 2021 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may 
 * not use this file except in compliance with the License. You may obtain 
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT 
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the 
 * License for the specific language governing permissions and limitations 
 * under the License.
 */

/**
 *  Example 0.a.
 *  Add pre-cond to specify x >= 0 and a post cond of your choice.
 *  Counter-example generation.
 */
method abs(x: int) returns (y: int)
    ensures true
{
    if x < 0 {
        y := -x;
    } else {
        y :=  x;
    }
}

/** Call abs */
method foo(x: int) 
    requires x >= 0
{
    var y := abs(x);
    assert y == x;
}

/**
 *  Example 0.b.
 *  The goal is to compute the maximum of x and y and return it in m.
 *  The current version is buggy and returns 0 is x > y and 1 if x <= 1.
 * 
 *  Try to:
 *  1. write the post-condition that shows that max(x,y) (i.e. m) is larger than x and y.
 *  2. write a set of post-conditions that fully characterises max.
 *  3. fix the code and make sure it verifies.
 */
method max(x: int, y: int) returns (m: int)
    ensures m >= x && m >= y
    ensures m == x || m == y
{
    if x > y  {
        m := x;
    } else {
        m := y;
    }
}

/**
 *  Example 1.
 *  
 *  Try to prove 
 *  1. the final assert statement (uncomment it and you may need to strengthen pre condition).
 *  2. termination, propose a decrease clause (to replace *)
 */
method ex1(n: int)
    requires n >= 0
    ensures true
{
    var i := 0;
    while i < n
        decreases n - i
        invariant 0 <= i <= n
    {
        i := i + 1;
    }
    assert i == n;
}

/**
 *  Infinite loop.
 */
method infiniteLoop() 
    ensures false
{
    while true 
    {
        
    }
}

//  Specify a post-condition and prove it.

/**
 *  Example 2.
 *
 *  Find a key in an array.
 *
 *  @param      a   The array.
 *  @param      key The key to find.
 *  @returns        An index i such a[i] == key if key in a and -1 otherwise.
 *
 *  Try to:
 *  0.  uncomment line index := index + 2 and check problems
 *  1.  write the property defined by the @returns above
 *  2.  prove this property (you may add loop invariants)
 *
 *  @note       The code below is flawed on purpose.
 *              |a| is the length of a
 *              to test whether an integer `k` is in `a`: k in a (true
 *              iff exists 0 <= i < |a|, a[i] == k). 
 *              And: !(k in a) <==> k !in a
 *              a[i..j] is the sub sequence a[i], ..., a[j - 1] 
 *              a[..j] is a[0..j] and a[i..] is a[i..|a|]
 *              a[..] is same as a
 */
method find(a: seq<int>, key: int) returns (index: int)
    ensures (exists i :: 0 <= i < |a| && a[i] == key) ==> (0 <= index < |a| && a[index] == key)
    ensures !(exists i :: 0 <= i < |a| && a[i] == key) ==> index == -1
{
    index := 0;
    while index < |a|
        decreases |a| - index
        invariant 0 <= index <= |a|
        invariant (forall i :: 0 <= i < index ==> a[i] != key)
    {
        // index := index + 1;
        if a[index] == key {
            return index;
        }
        index := index + 1;
    }
    index := -1;
}

/**
 *  Palindrome checker.
 *  Example 3.
 *
 *  Check whether a sequence of letters is a palindrome.
 *
 *  Try to:
 *  1. write the algorithm to determine whether a string is a palindrome
 *  2. write the ensures clauses that specify the palidrome properties
 *  3. verify algorithm. 
 *
 *  Notes: a[k] accesses element k of a for 0 <= k < |a|
 *  a[i..j] is (a seq) with the first j elements minus the first i
 *  a[0..|a|] is same as a.  
 */
method isPalindrome(a: seq<char>) returns (b: bool)
    ensures b <==> a == a[..|a|/2] + a[..|a|/2][..|a|/2]
{
    var i := 0;
    var j := |a| - 1;
    while i < j
        decreases j - i
        invariant 0 <= i <= j < |a|
        invariant (forall k :: 0 <= k < i ==> a[k] == a[|a| - 1 - k])
    {
        if a[i] != a[j] {
            b := false;
            return;
        }
        i := i + 1;
        j := j - 1;
    }
    b := true;
}

/**
 *  Whether a sequence of ints is sorted (ascending).
 *  
 *  @param  a   A sequence on integers.
 *  @returns    Whether the sequence is sorted.
 */
predicate sorted(a: seq<int>) 
{
    forall j, k :: 0 <= j < k < |a| ==> a[j] <= a[k]
}

/**
 *  Example 4.
 *
 *  Remove duplicates from a sorted sequence.
 *
 *  Try to:
 *  1. write the code to compute b
 *  2. write the ensures clauses that specify the remove duplicates properties
 *  3. verify algorithm. 
 *
 *  Notes: a[k] accesses element k of a for 0 <= k < |a|
 *  a[i..j] is (a seq) with the first j elements minus the first i
 *  a[0.. |a| - 1] is same as a.  
 */
method unique(a: seq<int>) returns (b: seq<int>) 
    requires sorted(a)
    ensures sorted(b)
    ensures forall x :: x in b ==> x in a
    ensures forall x :: x in a ==> x in b || (exists y :: y in b && y == x)
    ensures forall i :: 0 <= i < |b| - 1 ==> b[i] != b[i + 1]
{
    if |a| == 0 {
        b := [];
        return;
    }
    b := [a[0]];
    var i := 1;
    while i < |a|
        decreases |a| - i
        invariant 1 <= i <= |a|
        invariant sorted(b)
        invariant forall x :: x in b ==> x in a[..i]
        invariant forall x :: x in a[..i] ==> x in b || (exists y :: y in b && y == x)
        invariant forall j :: 0 <= j < |b| - 1 ==> b[j] != b[j + 1]
    {
        if a[i] != b[|b| - 1] {
            b := b + [a[i]];
        }
        i := i + 1;
    }
}

/**
 *  Dafny compiles the Main method if it finds one in a file.
 */
method Main() {

    //  run find
    var r := find([], 1);   
    print r, "\n";

    r := find([0,3,5,7], 5);  
    print r, "\n";

    //  run palindrome
    var s1 := ['a'];
    var r1 := isPalindrome(s1);
    print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

    s1 := [];
    r1 := isPalindrome(s1);
    print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

    s1 := ['a', 'b'];
    r1 := isPalindrome(s1);
    print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

    s1 := ['a', 'b', 'a'];
    r1 := isPalindrome(s1);
    print "is [", s1, "]", " a isPalindrome? ", r1, " \n";

    // run unique
    var i := [0,1,3,3,5,5,7];
    var s := unique(i);
    print "unique applied to ", i, " is ", s, "\n";
    
}
