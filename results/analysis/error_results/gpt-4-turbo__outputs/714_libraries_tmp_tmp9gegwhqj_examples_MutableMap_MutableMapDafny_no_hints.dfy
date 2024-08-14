/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

// RUN: %verify "%s"
   
/**
  *  Implements mutable maps in Dafny to guard against inconsistent specifications.
  *  Only exists to verify feasability; not meant for actual usage.
  */
module {:options "-functionSyntax:4"} MutableMapDafny {
  /**
    *  NOTE: Only here because of #2500; once resolved import "MutableMapTrait.dfy".
    */
  trait {:termination false} MutableMapTrait<K(==),V(==)> {
    function content(): map<K, V>
      reads this

    method Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]   
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v}

    function Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys

    predicate HasKey(k: K)
      reads this
      ensures HasKey(k) <==> k in this.content().Keys

    function Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values

    function Items(): (items: set<(K,V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k | k in this.content().Keys :: (k, this.content()[k])

    function Select(k: K): (v: V)
      reads this
      requires this.HasKey(k)
      ensures v in this.content().Values
      ensures this.content()[k] == v

    method Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values
 
    function Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
  }

  class MutableMapDafny<K(==),V(==)> extends MutableMapTrait<K,V> {
    var m: map<K,V>

    function content(): map<K, V> 
      reads this
    {
      return m;
    }

    constructor ()
      ensures this.content() == map[]
    {
      m := map[];
    }

    method Put(k: K, v: V)
      modifies this
      ensures this.content() == old(this.content())[k := v]   
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values + {v}
      ensures k !in old(this.content()).Keys ==> this.content().Values == old(this.content()).Values + {v}
    {
      m := m[k := v];
    }

    function Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys
    {
      return m.Keys;
    }

    predicate HasKey(k: K)
      reads this
      ensures HasKey(k) <==> k in this.content().Keys
    {
      return k in m.Keys;
    }

    function Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values
    {
      return m.Values;
    }

    function Items(): (items: set<(K,V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k | k in this.content().Keys :: (k, this.content()[k])
    {
      return set k | k in m.Keys :: (k, m[k]);
    }

    function Select(k: K): (v: V)
      reads this
      requires this.HasKey(k)
      ensures v in this.content().Values
      ensures this.content()[k] == v
    {
      return m[k];
    }

    method Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values
    {
      m := map k' | k' in m.Keys && k' != k :: m[k'];
    }

    function Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
    {
      return |m|;
    }
  }
}