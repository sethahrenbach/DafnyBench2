method CountLessThan(numbers: set<int>, threshold: int) returns (count: int)
  requires numbers != null
  requires threshold >= 0
  ensures count == |set i | i in numbers && i < threshold|
{
  count := 0;
  var shrink := numbers;
  var grow := {};
  while |shrink | > 0
    invariant count <= |set i | i in numbers && i < threshold|
    invariant shrink + grow == numbers
  {
    var i: int :| i in shrink;
    var found: bool := false;
    var temp: set<int> := {};
    var elem: int;
    var foundElem: bool := false;
    var chosenElem: int;
    for elem in shrink
      invariant elem in shrink
      invariant (foundElem ==> chosenElem == i)
      invariant (foundElem ==> temp + {i} == grow)
      invariant (!foundElem ==> temp + {elem} + grow == numbers)
    {
      if !foundElem && elem in shrink {
        chosenElem := elem;
        foundElem := true;
      } else {
        temp := temp + {elem};
      }
    }
    shrink := temp;
    grow := grow + {chosenElem};
    if chosenElem < threshold {
      count := count + 1;
    }
  }
}
