
method ExecuteAutomaton(init: seq<bool>, rule: (bool, bool, bool) -> bool, steps: nat)
  returns (table: seq<seq<bool>>)
  requires |init| >= 2
  ensures |table| == 1 + steps
  ensures table[0] == init
  ensures forall i | 0 <= i < |table| :: |table[i]| == |init|
  ensures forall i | 0 <= i < |table| - 1 ::
            forall j | 1 <= j <= |table[i]| - 2 :: table[i + 1][j] == rule(table[i][j - 1], table[i][j], table[i][j + 1])
  ensures forall i | 0 <= i < |table| - 1 ::
            table[i + 1][0] == rule(false, table[i][0], table[i][1]) &&
            table[i + 1][|table[i]| - 1] == rule(table[i][|table[i]| - 2], table[i][|table[i]| - 1], false)
{
  var currentSeq := init;
  var index := 0;

  while index < steps {
    var nextSeq := [];
    nextSeq := nextSeq + [rule(false, currentSeq[0], currentSeq[1])];

    while index < |currentSeq| - 1 {
      nextSeq := nextSeq + [rule(currentSeq[index - 1], currentSeq[index], currentSeq[index + 1])];
      index := index + 1;
    }

    nextSeq := nextSeq + [rule(currentSeq[|currentSeq| - 2], currentSeq[|currentSeq| - 1], false)];

    currentSeq := nextSeq;
    table := table + [nextSeq];
    index := index + 1;
  }

  return table;
}
