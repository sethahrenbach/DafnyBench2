
/*
 * Model of the ticket system and correctness theorem
 * Parts 4 and 5 in the paper
 */
type Process(==) = int  // Philosopher

datatype CState = Thinking | Hungry | Eating  // Control states

class TicketSystem
{
  var ticket: int  // Ticket dispenser
  var serving: int  // Serving display

  const P: set<Process>  // Fixed set of processes

  var cs: map<Process, CState>  // (Partial) Map from process to state
  var t: map<Process, int>  // (Partial) Map from process to ticket number

  predicate Valid()
    reads this
  {
    cs.Keys == t.Keys &&
    cs.Keys == P &&
    serving <= ticket &&
    (forall p | p in P && cs[p] != Thinking :: serving <= t[p] < ticket) &&
    (forall p, q | p in P && q in P && p != q && cs[p] != Thinking && cs[q] != Thinking :: t[p] != t[q]) &&
    (forall p | p in P && cs[p] == Eating :: t[p] == serving)
  }

  constructor (processes: set<Process>)
    ensures Valid()
    ensures P == processes
  {
    P := processes;
    ticket, serving := 0, 0;
    cs := map p | p in processes :: Thinking;
    t := map p | p in processes :: 0;
  }

  method Request(p: Process)
    requires Valid() && p in P && cs[p] == Thinking
    modifies this
    ensures Valid()
  {
    t := t[p := ticket];
    ticket := ticket + 1;
    cs := cs[p := Hungry];
  }

  method Enter(p: Process)
    requires Valid() && p in P && cs[p] == Hungry
    modifies this
    ensures Valid()
  {
    if t[p] == serving {
      cs := cs[p := Eating];
    }
  }

  method Leave(p: Process)
    requires Valid() && p in P && cs[p] == Eating
    modifies this
    ensures Valid()
  {
    serving := serving + 1;
    cs := cs[p := Thinking];
  }

  lemma MutualExclusion(p: Process, q: Process)
    requires Valid() && p in P && q in P && cs[p] == Eating && cs[q] == Eating
    ensures p == q
  {
    assert t[p] == serving && t[q] == serving;
  }
}

method Run(processes: set<Process>)
  requires processes != {}
{
  var ts := new TicketSystem(processes);
  var schedule := [];
  var trace := [(ts.ticket, ts.serving, ts.cs, ts.t)];

  while true
    invariant ts.Valid()
  {
    var p :| p in ts.P;
    match ts.cs[p] {
      case Thinking => ts.Request(p);
      case Hungry => ts.Enter(p);
      case Eating => ts.Leave(p);
    }
    schedule := schedule + [p];
    trace := trace + [(ts.ticket, ts.serving, ts.cs, ts.t)];
  }
}

method RunFromSchedule(processes: set<Process>, schedule: nat -> Process)
  requires processes != {}
  requires forall n :: schedule(n) in processes
{
  var ts := new TicketSystem(processes);
  var n := 0;

  while true
    invariant ts.Valid()
  {
    var p := schedule(n);
    match ts.cs[p] {
      case Thinking => ts.Request(p);
      case Hungry => ts.Enter(p);
      case Eating => ts.Leave(p);
    }
    n := n + 1;
  }
}
