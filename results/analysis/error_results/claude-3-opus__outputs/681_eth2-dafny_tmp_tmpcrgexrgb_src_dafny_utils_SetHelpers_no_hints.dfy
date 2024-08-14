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
 *  Provide some folk theorems on sets.
 */
module SetHelpers {

    /**
     *  If a set is included in another one, their intersection
     *  is the smallest one.
     *
     *  @param  T   A type.
     *  @param  x   A finite set.
     *  @param  y   A finite set.
     *  @returns    A proof that x <= y implies x * y == x.
     */
    lemma interSmallest<T>(x : set<T>, y : set<T>) 
        requires x <= y 
        ensures x * y == x
    {   //  Thanks Dafny
    }

    /**
     *  If x [= {0, ..., k - 1} and y [= {0, .., k - 1}
     *  then x U y has at most k elements.
     *
     *  @param  T   A type.
     *  @param  x   A finite set.
     *  @param  y   A finite set.
     *  @param  k   k a natural number.
     *  @returns    A proof that if x [= {0, ..., k - 1} and y [= {0, .., k - 1}
     *              then |x + y| <=k.
     */
    lemma unionCardBound(x : set<nat>, y : set<nat>, k : nat) 
        requires forall e :: e in x ==> e < k
        requires forall e :: e in y ==> e < k
        ensures  forall e :: e in x + y ==> e < k
        ensures |x + y| <= k 
    {
        natSetCardBound(x + y, k);
    }

    /**
     *  If  x [= {0, ..., k - 1} then x has at most k elements.
     *
     *  @param  T   A type.
     *  @param  x   A finite set.
     *  @param  k   k a natural number.
     *  @returns    A proof that if x [= {0, ..., k - 1} then |x| <= k.
     */
    lemma natSetCardBound(x : set<nat>, k : nat) 
        requires forall e :: e in x ==> e < k
        ensures |x| <= k 
    {
        if k == 0 {
        } else {
            var x' := x - { k - 1};
            forall e | e in x'
                ensures e < k - 1 
            {
                assert e in x;
                assert e < k;
                assert e != k-1;
            }
            natSetCardBound(x', k - 1);
            assert |x'| <= k - 1;
            assert |x| <= |x'| + 1 <= k;
        }
    }

    /** 
     *  If x contains all successive elements {0, ..., k-1} then x has k elements.
     *
     *  @param  T   A type.
     *  @param  x   A finite set.
     *  @param  k   k a natural number.
     *  @returns    A proof that if x = {0, ..., k - 1} then |x| == k.
     */

    lemma {:induction k} successiveNatSetCardBound(x : set<nat>, k : nat) 
        requires x == set x: nat | 0 <= x < k :: x
        ensures |x| == k
    {
        if k == 0 {
        } else {
            successiveNatSetCardBound(x - {k - 1}, k - 1);
            assert |x - {k-1}| == k-1;
            assert |x| == |x - {k-1}| + 1;
        }
    }
    
   /**
    *  If a finite set x is included in a finite set y, then
    *  card(x) <= card(y).
    *
    *  @param  T   A type.
    *  @param  x   A finite set.
    *  @param  y   A finite set.
    *  @returns    A proof that x <= y implies card(x) <= card(y)
    *              in other terms, card(_) is monotonic.
    */
    lemma cardIsMonotonic<T>(x : set<T>, y : set<T>) 
        requires x <= y 
        ensures |x| <= |y|
    {
        if |y| == 0 {
        } else {
            //  |y| >= 1, get an element in y
            var e :| e in y;
            var y' := y - { e };
            //  Split recursion according to whether e in x or not
            if e in x {
                var x' := x - {e};
                cardIsMonotonic(x', y');
                assert |x'| <= |y'|;
                assert |x| == |x'| + 1 <= |y'| + 1 == |y|;
            } else {
                cardIsMonotonic(x, y');
                assert |x| <= |y'| < |y|;
            }
        }
    }

   /**
    *  If two finite sets x and y are included in another one z and
    *  have more than 2/3(|z|) elements, then their intersection has more
    *  then |z|/3 elements.
    *
    *  @param  T   A type.
    *  @param  x   A finite set.
    *  @param  y   A finite set.
    *  @param  z   A finite set.
    *  @returns    A proof that if two finite sets x and y are included in 
    *              another one z and have more than 2/3(|z|) elements, then 
    *              their intersection has more then |z|/3 elements.   
    */
    lemma pigeonHolePrinciple<T>(x: set<T>, y : set<T>, z : set<T>)
        requires  x <= z 
        requires y <= z
        requires |x| >= 2 * |z| / 3 + 1   //    or equivalently 2 * |z| < 3 * |x| 
        requires |y| >= 2 * |z| / 3 + 1   //    or equivalently 2 * |z| < 3 * |y|
        ensures |x * y| >= |z| / 3 + 1    //    or equivalently 3 * |x * y| < |z| 
    {
        //  Proof of alternative assumption
        //  Proof by contradiction
        if |x * y| < |z| / 3 + 1 {
            //  size of union is sum of sizes minus size of intersection.
            calc {
                |x + y|;
                |x| + |y| - |x * y|;
                >= 2 * |z| / 3 + 1 + 2 * |z| / 3 + 1 - |x * y|;
                > 2 * |z| / 3 + 1 + 2 * |z| / 3 + 1 - (|z| / 3 + 1);
                4 * |z| / 3 + 1;
                |z| + |z| / 3 + 1;
                > |z|;
            }
            cardIsMonotonic(x + y, z);
            assert false; // contradiction
        } 
        //  proof of alternative conclusion
    } 

}
