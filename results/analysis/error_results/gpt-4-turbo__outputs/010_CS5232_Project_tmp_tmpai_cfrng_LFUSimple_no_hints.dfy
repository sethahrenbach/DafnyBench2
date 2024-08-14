class LFUCache {

    var capacity : int;
    var cacheMap : map<int, (int, int)>; // key -> {value, freq}

    constructor(capacity: int)
      requires capacity > 0;
      ensures Valid();
    {
      this.capacity := capacity;
      this.cacheMap := map[];
    }

    predicate Valid()
      reads this;
    {
      this.capacity > 0 &&
      0 <= |cacheMap| <= capacity &&
      (|cacheMap| > 0 ==> (forall e :: e in cacheMap ==> cacheMap[e].1 >= 1)) && // frequency should always larger than 0
      (|cacheMap| > 0 ==> (forall e :: e in cacheMap ==> cacheMap[e].0 >= 0)) // only allow positive values
    } 

    method getLFUKey() returns (lfuKey : int) 
      requires Valid();
      requires |cacheMap| > 0;
      ensures Valid();
      ensures lfuKey in cacheMap;
      ensures forall k :: k in cacheMap ==> cacheMap[lfuKey].1 <= cacheMap[k].1;
    {
      var minFreq := int.MaxValue;
      lfuKey := 0;
      var minKey := 0;

      for (k, v) in cacheMap {
        if (v.1 < minFreq) {
          minFreq := v.1;
          minKey := k;
        }
      }

      lfuKey := minKey;
      assert forall k :: k in cacheMap ==> cacheMap[lfuKey].1 <= cacheMap[k].1;
      return lfuKey;
    }

    method get(key: int) returns (value: int)
      requires Valid();
      modifies this;
      ensures Valid();
      ensures key !in cacheMap ==> value == -1;
      ensures forall e :: e in old(cacheMap) <==> e in cacheMap;
      ensures forall e :: e in old(cacheMap) ==> (old(cacheMap[e].0) == cacheMap[e].0);
      ensures key in cacheMap ==> value == cacheMap[key].0 && old(cacheMap[key].1) + 1 == cacheMap[key].1;
    {
      if (key !in cacheMap) {
        value := -1;
      } else {
        value := cacheMap[key].0;
        var oldFreq := cacheMap[key].1;
        var newV := (value, oldFreq + 1);
        cacheMap := cacheMap[key := newV];
      }
      return value;
    }
    
    
    method put(key: int, value: int)
      requires Valid();
      requires value > 0;
      modifies this;
      ensures Valid();
    {
      if (key in cacheMap) {
        var currFreq := cacheMap[key].1;
        cacheMap := cacheMap[key := (value, currFreq + 1)];
      } else {
        if (|cacheMap| < capacity) {
          cacheMap := cacheMap[key := (value, 1)];
        } else {
          var LFUKey := getLFUKey();
          cacheMap := cacheMap - {LFUKey};
          cacheMap := cacheMap[key := (value, 1)];
        }
      }
    }
}