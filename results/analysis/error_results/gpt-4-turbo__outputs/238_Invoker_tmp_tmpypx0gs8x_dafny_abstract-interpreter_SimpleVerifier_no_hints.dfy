
module Ints {
  const U32_BOUND: nat := 0x1_0000_0000;
  newtype u32 = x: int | 0 <= x < U32_BOUND;
  newtype i32 = x: int | -0x8000_0000 <= x < 0x8000_0000;
}

module Lang {
  import opened Ints;

  datatype Reg = R0 | R1 | R2 | R3;

  datatype Expr =
    | Const(n: u32)
    | Add(r1: Reg, r2: Reg)
    | Sub(r1: Reg, r2: Reg);

  datatype Stmt =
    | Assign(r: Reg, e: Expr)
    | JmpZero(r: Reg, offset: i32);

  datatype Program = Program(stmts: seq<Stmt>);
}

module ConcreteEval {
  import opened Ints;
  import opened Lang;

  type State = Reg -> u32;

  function update_state(s: State, r0: Reg, v: u32): State {
    r: Reg => if r == r0 then v else s(r)
  }

  datatype Option<T> = Some(v: T) | None;

  function expr_eval(env: State, e: Expr): Option<u32> {
    match e {
      case Const(n) => Some(n)
      case Add(r1, r2) =>
        if (env(r1) as int + env(r2) as int >= U32_BOUND) then None
        else Some(env(r1) + env(r2))
      case Sub(r1, r2) =>
        if env(r1) as int - env(r2) as int < 0 then Some(0)
        else Some(env(r1) - env(r2))
    }
  }

  function stmt_step(env: State, s: Stmt): Option<(State, int)> {
    match s {
      case Assign(r, e) =>
        var e' := expr_eval(env, e);
        match e' {
          case Some(v) => Some((update_state(env, r, v), 1))
          case None => None
        }
      case JmpZero(r, offset) =>
        Some((env, if env(r) == 0 then offset else 1))
    }
  }

  datatype ExecResult = Ok(env: State) | NoFuel | Error;

  function stmts_step(env: State, ss: seq<Stmt>, pc: nat, fuel: nat): ExecResult
    requires pc <= |ss|
  {
    if fuel == 0 then NoFuel
    else if pc == |ss| then Ok(env)
    else match stmt_step(env, ss[pc]) {
      case None => Error
      case Some((env', offset)) =>
        if !(0 <= pc + offset <= |ss|) then Error
        else stmts_step(env', ss, pc + offset, fuel - 1)
    }
  }
}
