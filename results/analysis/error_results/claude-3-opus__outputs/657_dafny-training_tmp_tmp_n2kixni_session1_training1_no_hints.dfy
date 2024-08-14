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
    // assert( y == x);
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
requires true;
ensures true;
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
    requires true
    ensures true
{
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        decreases n - i
    {
        i := i + 1;
    }
    /** This is the property to prove: */
    // assert i == n;
}

/**
 *  Infinite loop.
 */
method foo2() 
    ensures false
{
    while true 
    {
        // Infinite loop, cannot prove ensures false        
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
    requires true
    ensures true
{
    index := 0;
    while index < |a|
        invariant 0 <= index <= |a|
        invariant forall i :: 0 <= i < index ==> a[i] != key
        decreases |a| - index
    {
        // index := index + 1;
        if  a[index] == key  { 
            return index;
        }
        index := index + 1;
    }
    index := -1;
}

//  Prove more complicated invariants with quantifiers.

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
{
    var i := 0;
    var j := |a| - 1;
    
    while i < j
        invariant 0 <= i <= j < |a|
        invariant forall k :: 0 <= k < i ==> a[k] == a[|a|-1-k]
        decreases j - i
    {
        if a[i] != a[j] {
            return false;
        }
        i := i + 1;
        j := j - 1;
    }
    
    return true;
}

/**
 *  Whether a sequence of ints is sorted (ascending).
 *  
 *  @param  a   A sequence on integers.
 *  @returns    Whether the sequence is sorted.
 */
predicate sorted(a: seq<int>) 
{
    forall j, k::0 <= j < k < |a|  ==> a[j] <= a[k]
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
    ensures true
{
    if |a| == 0 {
        return [];
    }
    
    b := [a[0]];
    var i := 1;
    
    while i < |a|
        invariant 1 <= i <= |a|
        invariant sorted(b)
        invariant forall j :: 0 <= j < |b| ==> b[j] in a[..i]
        invariant forall x :: x in a[..i] ==> x in b
        invariant forall j :: 0 <= j < |b|-1 ==> b[j] != b[j+1]
        decreases |a| - i
    {
        if a[i] != b[|b|-1] {
            b := b + [a[i]];
        }
        i := i + 1;
    }
    
    return b;
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