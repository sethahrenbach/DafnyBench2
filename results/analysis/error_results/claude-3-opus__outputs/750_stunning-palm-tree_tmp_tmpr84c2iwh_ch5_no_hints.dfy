function More(x: int): int {
  if x <= 0 then 1 else More(x - 2) + 3
}

lemma {:induction false} Increasing(x: int)
  ensures x < More(x)
{
  if x <= 0 {
    // trivial
  }
  else {
    // x < More(x) <=> x < More(x - 2) + 3
    //             <=> x - 3 < More(x - 2)
    // Increasing(x - 2) ==> x - 2 < More(x - 2)
    //                   ==> x - 3 < x - 2 < More(x - 2)
    Increasing(x - 2);
    assert x - 3 < More(x - 2);
    assert x < More(x - 2) + 3;
  }
}

method ExampleLemmaUse(a: int) {
  var b := More(a);
  Increasing(a);
  assert a < b;
  var c := More(b);
  Increasing(b);
  assert b < c;
}

// Ex 5.0
method ExampleLemmaUse50(a: int) {
  Increasing(a);
  var b := More(a);
  assert a < b;
  var c := More(b);
  assert b < c;
  if a < 1000 {
    Increasing(b);
    assert b < c;
  }
}

// Ex 5.1
method ExampleLemmaUse51(a: int) {
  Increasing(a);
  var b := More(a);
  assert a < b;
  Increasing(b);
  b := More(b);
  assert a < b;
  if a < 1000 {
    Increasing(More(a));
    assert More(a) < b;
  }
}

// Ex 5.6
function Ack(m: nat, n: nat): nat {
  if m == 0 then
    n + 1
  else if n == 0 then
    Ack(m - 1, 1)
  else
    Ack(m - 1, Ack(m, n - 1))
}

lemma {:induction false} Ack1n(m: nat, n: nat)
  requires m == 1
  ensures Ack(m, n) == n + 2
{
  if n == 0 {
    calc {
      Ack(m, n);
    ==
      Ack(m - 1, 1);
    ==
      Ack(0, 1);
    ==
      1 + 1;
    ==
      2;
    ==
      n + 2;
    }
  }
  else {
    calc {
      Ack(m, n);
    ==  // defn
      Ack(m - 1, Ack(m, n - 1));
    ==  // subs m := 1
      Ack(0, Ack(1, n - 1));
    == { Ack1n(1, n - 1); }
      Ack(0, (n - 1) + 2);
    ==  // arith
      Ack(0, n + 1);
    ==  // arith
      (n + 1) + 1;
    ==  // arith
      n + 2;
    }
  }
}

// Ex 5.5
function Reduce(m: nat, x: int): int {
  if m == 0 then x else Reduce(m / 2, x + 1) - m
}

lemma {:induction false} ReduceUpperBound(m: nat, x: int)
  ensures Reduce(m, x) <= x
{
  if m == 0 {  // trivial
  }
  else {
    calc {
      Reduce(m, x);
    ==  // defn
      Reduce(m / 2, x + 1) - m;
    <= { ReduceUpperBound(m/2, x+1); }
      x + 1 - m;
    <= { assert m >= 1; }
      x;
    }
  }
}

// 5.5.1
lemma {:induction false} ReduceLowerBound(m: nat, x: int)
  ensures x - 2 * m <= Reduce(m, x)
{
  if m == 0 {  // trivial
  }
  else {
    calc {
      Reduce(m, x);
    ==  // defn
      Reduce(m / 2, x + 1) - m;
    >= { ReduceLowerBound(m/2, x+1); }
      x + 1 - 2 * (m/2) - m;
    >= { assert m >= 1; }  // m >= 1 ==> m/2 <= m - 1
      x + 1 - 2 * (m - 1) - m;
    ==  // arith
      x - 2 * m + 1;
    >=  // arith
      x - 2 * m;
    }
  }
}


// ------------------------------------------------------------------------------
// ----- Expr Eval --------------------------------------------------------------
// ------------------------------------------------------------------------------

// 5.8.0

datatype Expr = Const(nat)
              | Var(string)
              | Node(op: Op, args: List<Expr>)

datatype Op = Mul | Add
datatype List<T> = Nil | Cons(head: T, tail: List<T>)

function Eval(e: Expr, env: map<string, nat>): nat
{
  match e {
    case Const(c) => c
    case Var(s) => if s in env then env[s] else 0
    case Node(op, args) => EvalList(op, args, env)
  }
}

// intro'd in 5.8.1
function Unit(op: Op): nat {
  match op case Add => 0 case Mul => 1
}

function EvalList(op: Op, args: List<Expr>, env: map<string, nat>): nat
{
  match args {
    case Nil => Unit(op)
    case Cons(e, tail) =>
      var v0, v1 := Eval(e, env), EvalList(op, tail, env);
      match op
      case Add => v0 + v1
      case Mul => v0 * v1
  }
}

function Substitute(e: Expr, n: string, c: nat): Expr
{
  match e
  case Const(_) => e
  case Var(s) => if s == n then Const(c) else e
  case Node(op, args) => Node(op, SubstituteList(args, n, c))
}

function SubstituteList(es: List<Expr>, n: string, c: nat): List<Expr>
{
  match es
  case Nil => Nil
  case Cons(head, tail) => Cons(Substitute(head, n, c), SubstituteList(tail, n, c))
}

lemma {:induction false} EvalSubstituteCorrect(e: Expr, n: string, c: nat, env: map<string, nat>)
  ensures Eval(Substitute(e, n, c), env) == Eval(e, env[n := c])
{
  match e
  case Const(_) => {}
  case Var(s) => {
    calc {
      Eval(Substitute(e, n, c), env);
    ==  // defn Substitute
      Eval(if s == n then Const(c) else e, env);
    ==  // defn Eval
      if s == n then Eval(Const(c), env) else Eval(e, env);
    ==  // defn Eval
      if s == n then c else Eval(e, env);
    ==  // defn Eval
      if s == n then c else Eval(e, env[n := c]);
    ==  // s-c-s
      if s == n then Eval(e, env[n := c]) else Eval(e, env[n := c]);
    ==  // defn Eval
      Eval(e, env[n := c]);
    }
  }
  case Node(op, args) => {
    EvalSubstituteListCorrect(op, args, n, c, env);
  }
}

lemma {:induction false} EvalSubstituteListCorrect(op: Op, args: List<Expr>, n: string, c: nat, env: map<string, nat>)
  ensures EvalList(op, SubstituteList(args, n, c), env) == EvalList(op, args, env[n := c])
{
  match args
  case Nil => {}
  case Cons(head, tail) => {
    // Ex 5.15
    calc {
      EvalList(op, SubstituteList(args, n, c), env);
    ==  // defn SubstituteList
      EvalList(op, Cons(Substitute(head, n, c), SubstituteList(tail, n, c)), env);
    ==  // defn EvalList
      (match op
       case Add => Eval(Substitute(head, n, c), env) + EvalList(op, SubstituteList(tail, n, c), env)
       case Mul => Eval(Substitute(head, n, c), env) * EvalList(op, SubstituteList(tail, n, c), env));
    == { EvalSubstituteCorrect(head, n, c, env); }
      (match op
       case Add => Eval(head, env[n := c]) + EvalList(op, SubstituteList(tail, n, c), env)
       case Mul => Eval(head, env[n := c]) * EvalList(op, SubstituteList(tail, n, c), env));
    == { EvalSubstituteListCorrect(op, tail, n, c, env); }
      (match op
       case Add => Eval(head, env[n := c]) + EvalList(op, tail, env[n := c])
       case Mul => Eval(head, env[n := c]) * EvalList(op, tail, env[n := c]));
    ==  // defn EvalList
      EvalList(op, args, env[n := c]);
    }
  }
}

// Ex 5.16
lemma EvalEnv(e: Expr, n: string, env: map<string, nat>)
  requires n in env.Keys
  ensures Eval(e, env) == Eval(Substitute(e, n, env[n]), env)
{
  match e
  case Const(_) => {}
  case Var(s) => {
    if s == n {
      calc {
        Eval(Substitute(e, n, env[n]), env);
      ==  // defn Substitute
        Eval(Const(env[n]), env);
      ==  // defn Eval
        env[n];
      ==  // defn Eval
        Eval(e, env);
      }
    }
  }
  case Node(op, args) => {
    EvalEnvList(op, args, n, env);
  }
}

lemma EvalEnvList(op: Op, es: List<Expr>, n: string, env: map<string, nat>)
  requires n in env.Keys
  ensures EvalList(op, es, env) == EvalList(op, SubstituteList(es, n, env[n]), env)
{
  match es
  case Nil => {}
  case Cons(head, tail) => { EvalEnv(head, n, env); EvalEnvList(op, tail, n, env); }
}

// Ex 5.17
lemma EvalEnvDefault(e: Expr, n: string, env: map<string, nat>)
  requires n !in env.Keys
  ensures Eval(e, env) == Eval(Substitute(e, n, 0), env)
{
  match e
  case Const(_) => {}
  case Var(s) => {
    if s == n {
      calc {
        Eval(Substitute(e, n, 0), env);
      ==  // defn Substitute
        Eval(Const(0), env);
      ==  // defn Eval
        0;
      ==  // defn Eval
        Eval(e, env);
      }
    }
  }
  case Node(op, args) => {
    EvalEnvDefaultList(op, args, n, env);
  }
}

lemma EvalEnvDefaultList(op: Op, args: List<Expr>, n: string, env: map<string, nat>)
  requires n !in env.Keys
  ensures EvalList(op, args, env) == EvalList(op, SubstituteList(args, n, 0), env)
{
  match args
  case Nil => {}
  case Cons(head, tail) => { EvalEnvDefault(head, n, env); EvalEnvDefaultList(op, tail, n, env); }
}

// Ex 5.18
lemma SubstituteIdempotent(e: Expr, n: string, c: nat)
  ensures Substitute(Substitute(e, n, c), n, c) == Substitute(e, n, c)
{
  match e
  case Const(_) => {}
  case Var(s) => {
    if s == n {
      calc {
        Substitute(Substitute(e, n, c), n, c);
      ==  // defn Substitute
        Substitute(Const(c), n, c);
      ==  // defn Substitute
        Const(c);
      ==  // defn Substitute
        Substitute(e, n, c);
      }
    }
  }
  case Node(op, args) => { SubstituteListIdempotent(args, n, c); }
}

lemma SubstituteListIdempotent(args: List<Expr>, n: string, c: nat)
  ensures SubstituteList(SubstituteList(args, n, c), n, c) == SubstituteList(args, n, c)
{
  match args
  case Nil => {}
  case Cons(head, tail) => { SubstituteIdempotent(head, n, c); SubstituteListIdempotent(tail, n, c); }
}

// 5.8.1
// Optimization is correct

function Optimize(e: Expr): Expr
  ensures forall env: map<string, nat> :: Eval(Optimize(e), env) == Eval(e, env)
{
  if e.Node? then
    var args := OptimizeAndFilter(e.args, Unit(e.op));
    Shorten(e.op, args)
  else
    e
}

lemma OptimizeCorrect(e: Expr, env: map<string, nat>)
  ensures Eval(Optimize(e), env) == Eval(e, env)
{
  if e.Node? {
    OptimizeAndFilterCorrect(e.args, e.op, env); 
    ShortenCorrect(OptimizeAndFilter(e.args, Unit(e.op)), e.op, env); 
  }
}

function OptimizeAndFilter(args: List<Expr>, u: nat): List<Expr>
  ensures forall op: Op, env: map<string, nat> :: u == Unit(op) ==> Eval(Node(op, OptimizeAndFilter(args, u)), env) == Eval(Node(op, args), env)
{
  match args
  case Nil => Nil
  case Cons(head, tail) =>
    var hd, tl := Optimize(head), OptimizeAndFilter(tail, u);
    if hd == Const(u) then tl else Cons(hd, tl)
}

lemma OptimizeAndFilterCorrect(args: List<Expr>, op