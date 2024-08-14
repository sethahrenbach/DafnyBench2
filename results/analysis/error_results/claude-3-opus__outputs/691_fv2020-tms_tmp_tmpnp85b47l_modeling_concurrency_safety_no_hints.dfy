/*
 * Model of the ticket system and correctness theorem
 * Parts 4 and 5 in the paper
 */
type Process(==) = int  // Philosopher

datatype CState = Thinking | Hungry | Eating  // Control states

// A class can have state, with multiple fields, methods, a constructor, and declare functions and lemmas
class TicketSystem
{
  var ticket: int  // Ticket dispenser
  var serving: int  // Serving display

  const P: set<Process>  // Fixed set of processes

  // State for each process
  var cs: map<Process, CState>  // (Partial) Map from process to state
  var t: map<Process, int>  // (Partial) Map from process to ticket number

  // Invariant of the system
  // Checks that P is a subset of the domain/keys of each map
  predicate Valid()
    reads this  // Depends on the fields on the current class
  {
    && cs.Keys == t.Keys == P  // Alt. P <= cs.Keys && P <= t.Keys
    && serving <= ticket
    && (forall p ::  // ticket help is in range(serving, ticket)
      p in P && cs[p] != Thinking
      ==> serving <= t[p] < ticket
    )
    && (forall p, q ::  // No other process can have the ticket number equals to serving
      p in P && q in P && p != q && cs[p] != Thinking && cs[q] != Thinking
      ==> t[p] != t[q]
    )
    && (forall p ::  // We are serving the correct ticket number
      p in P && cs[p] == Eating
      ==> t[p] == serving
    )
  }

  // Initialize the ticket system
  constructor (processes: set<Process>)
    ensures Valid()  // Postcondition
    ensures P == processes  // Connection between processes and ts.P
  {
    P := processes;
    ticket, serving := 0, 0;  // Alt. ticket := serving;
    // The two following use map comprehension
    cs := map p | p in processes :: Thinking;  // The map from p, where p in processes, takes value Thinking
    t := map p | p in processes :: 0;
  }

  // The next three methods are our atomic events
  // A Philosopher is Thinking and gets Hungry
  method Request(p: Process)
    requires Valid() && p in P && cs[p] == Thinking  // Control process precondition
    modifies this  // Depends on the fields on the current class
    ensures Valid()  // Postcondition
    ensures cs == old(cs)[p := Hungry]
    ensures t == old(t)[p := ticket]
    ensures ticket == old(ticket) + 1
    ensures serving == old(serving)
    ensures P == old(P)
  {
    t := t[p := ticket];
    ticket := ticket + 1;
    cs := cs[p := Hungry];  // Philosopher's state changes to Hungry
  }

  // A Philosopher is Hungry and enters the kitchen
  method Enter(p: Process)
    requires Valid() && p in P && cs[p] == Hungry  // Control process precondition
    modifies this  // Depends on the fields on the current class
    ensures Valid()  // Postcondition
    ensures t[p] == serving ==> cs == old(cs)[p := Eating]
    ensures t[p] != serving ==> cs == old(cs)
    ensures t == old(t)
    ensures ticket == old(ticket)
    ensures serving == old(serving)
    ensures P == old(P)
  {
    if t[p] == serving  // The kitchen is available for this Philosopher
    {
      cs := cs[p := Eating];  // Philosopher's state changes to Eating
    }
  }

  // A Philosopher is done Eating and leaves the kitchen
  method Leave(p: Process)
    requires Valid() && p in P && cs[p] == Eating  // Control process precondition
    modifies this  // Depends on the fields on the current class
    ensures Valid()  // Postcondition
    ensures cs == old(cs)[p := Thinking]
    ensures t == old(t)
    ensures ticket == old(ticket)
    ensures serving == old(serving) + 1
    ensures P == old(P)
  {
    assert t[p] == serving;  // Ticket held by p is equal to serving
    serving := serving + 1;  // Kitchen is ready to serve the next ticket holder
    cs := cs[p := Thinking];  // Philosopher's state changes to Thinking
  }

  // Ensures that no two processes are in the same state
  lemma MutualExclusion(p: Process, q: Process)
    // Antecedents
    requires Valid() && p in P && q in P
    requires cs[p] == Eating && cs[q] == Eating
    // Conclusion/Proof goal
    ensures p == q
  {
    // From Valid(), we know that for all p in P where cs[p] == Eating, t[p] == serving
    // So if cs[p] == Eating and cs[q] == Eating, then t[p] == serving == t[q]
    // But Valid() also states that for distinct p, q in P where both are not Thinking, 
    // t[p] != t[q]
    // Therefore, p and q cannot be distinct, so p == q
  }
}

/*
 * Event scheduler
 * Part 6 in the paper
 * Part 6.1 for alternatives
 */
method Run(processes: set<Process>)
  requires processes != {}  // Cannot schedule no processes
  decreases *  // Allow arbitrary loop iterations
{
  var ts := new TicketSystem(processes);
  var schedule := [];  // Scheduling choices
  var trace := [(ts.ticket, ts.serving, ts.cs, ts.t)];  // Record sequence of states
  
  while true
    invariant ts.Valid()
    invariant ts.P == processes
    invariant |schedule| == |trace| - 1
    invariant forall i :: 0 <= i < |schedule| ==> schedule[i] in ts.P
    invariant forall i :: 0 <= i < |trace| ==> trace[i].0 <= trace[i].1 <= ts.ticket && trace[i].2.Keys == trace[i].3.Keys == ts.P
    decreases *  // Allow arbitrary loop iterations
  {
    var p :| p in ts.P;  // p exists such that p is in ts.P
    var old_cs := ts.cs;
    var old_t := ts.t;
    var old_ticket := ts.ticket;
    var old_serving := ts.serving;
    match ts.cs[p] {
      case Thinking => ts.Request(p);
      case Hungry => ts.Enter(p);
      case Eating => ts.Leave(p);
    }
    schedule := schedule + [p];
    trace := trace + [(old_ticket, old_serving, old_cs, old_t)];
    assert old_ticket <= old_serving <= ts.ticket;
    assert old_cs.Keys == old_t.Keys == ts.P;
    assert old_ticket <= trace[|trace|-1].1 <= ts.ticket;
    assert old_serving <= trace[|trace|-1].1 <= ts.ticket;
  }
}

/*
 * Event scheduler with planified schedule
 * Part 6.2
 */
method RunFromSchedule(processes: set<Process>, schedule: nat -> Process)
  requires processes != {}
  requires forall n :: schedule(n) in processes
  decreases *  // Allow arbitrary loop iterations
{
  var ts := new TicketSystem(processes);
  var n := 0;
  
  while true  
    invariant ts.Valid()
    invariant ts.P == processes
    invariant forall i :: 0 <= i < n ==> schedule(i) in ts.P
    decreases *  // Allow arbitrary loop iterations
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
