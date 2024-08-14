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
      m
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
      var oldVal := if k in m.Keys then m[k] else v; // Dummy value
      m := m[k := v];
      if k in old(m).Keys {
        var oldValSet := if oldVal == v then {} else {oldVal};
        assert oldVal in old(m).Values;
        assert v in m.Values;
        assert oldVal !in m.Values || oldVal == v;
        forall v' | v' in old(m).Values + {v} 
          ensures v' in m.Values + oldValSet
        {
          if v' == v {
          } else if v' == oldVal {
            assert oldVal in old(m).Values;
            if oldVal != v {
              assert oldVal !in m.Values;
            }
          } else {
            assert v' in old(m).Values;
            assert v' in m.Values;
          }
        }
      } else {
        assert oldVal == v;
        assert v !in old(m).Values;
        forall v' | v' in old(m).Values + {v} 
          ensures v' in m.Values
        {
          if v' == v {
          } else {
            assert v' in old(m).Values;
            assert v' in m.Values;
          }
        }
      }
    }

    function Keys(): (keys: set<K>)
      reads this
      ensures keys == this.content().Keys
    {
      m.Keys
    }

    predicate HasKey(k: K)
      reads this
      ensures HasKey(k) <==> k in this.content().Keys
    {
      k in m.Keys
    }

    function Values(): (values: set<V>)
      reads this
      ensures values == this.content().Values
    {
      m.Values
    }

    function Items(): (items: set<(K,V)>)
      reads this
      ensures items == this.content().Items
      ensures items == set k | k in this.content().Keys :: (k, this.content()[k])
    {
      set k | k in m.Keys :: (k, m[k])
    }

    function Select(k: K): (v: V)
      reads this
      requires this.HasKey(k)
      ensures v in this.content().Values
      ensures this.content()[k] == v
    {
      m[k]
    }

    method Remove(k: K)
      modifies this
      ensures this.content() == old(this.content()) - {k}
      ensures k in old(this.content()).Keys ==> this.content().Values + {old(this.content())[k]} == old(this.content()).Values
    {
      if k in m.Keys {
        var oldVal := m[k];
        m := map k' | k' in m.Keys && k' != k :: m[k'];
        assert oldVal in old(m).Values;
        assert oldVal !in m.Values;
        forall v' | v' in old(m).Values
          ensures v' in m.Values + {oldVal}
        {
          if v' == oldVal {
          } else {
            assert v' in old(m).Values;
            assert v' in m.Values;
          }
        }
      }
    }

    function Size(): (size: int)
      reads this
      ensures size == |this.content().Items|
    {
      |m|
    }
  }
}
