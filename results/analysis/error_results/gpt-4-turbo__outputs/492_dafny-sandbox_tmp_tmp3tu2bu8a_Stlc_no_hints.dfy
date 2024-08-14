
// Proving type safety of a Simply Typed Lambda-Calculus in Dafny
// adapted from Coq (http://www.cis.upenn.edu/~bcpierce/sf/Stlc.html)

/// Utilities

// ... handy for partial functions
datatype option<A> = None | Some(get: A)

/// -----
/// Model
/// -----

/// Syntax

// Types
datatype ty = TBase                             // (opaque base type)
            | TArrow(T1: ty, T2: ty)             // T1 => T2

// Terms
datatype tm = tvar(id: int)                      // x                  (variable)
            | tapp(f: tm, arg: tm)               // t t                (application)
            | tabs(x: int, T: ty, body: tm)      // \x:T.t             (abstraction)

/// Operational Semantics

// Values
predicate value(t: tm)
{
  match t
  {
    case tabs(_, _, _) => true
    case _ => false
  }
}

// Free Variables and Substitution

function fv(t: tm): set<int>
{
  match t
  {
    case tvar(id) => {id}
    case tabs(x, _, body) => fv(body) - {x}
    case tapp(f, arg) => fv(f) + fv(arg)
  }
}

function subst(x: int, s: tm, t: tm): tm
{
  match t
  {
    case tvar(id) => if x == id then s else t
    case tabs(x', T, body) => tabs(x', T, subst(x, s, body))
    case tapp(f, arg) => tapp(subst(x, s, f), subst(x, s, arg))
  }
}

// Reduction
function step(t: tm): option<tm>
{
  match t
  {
    case tapp(f, arg) if f is tabs(x, _, body) && value(arg) => Some(subst(x, arg, body))
    case tapp(f, arg) if !value(f) => step(f).map(f' => tapp(f', arg))
    case tapp(f, arg) if value(f) && !value(arg) => step(arg).map(arg' => tapp(f, arg))
    case _ => None
  }
}

// Multistep reduction:
predicate reduces_to(t: tm, t': tm, n: nat)
{
  t == t' || (n > 0 && step(t).Some? && reduces_to(step(t).get, t', n-1))
}

// Examples
lemma lemma_step_example1(n: nat)
  requires n > 0;
  ensures reduces_to(tapp(tabs(0, TArrow(TBase, TBase), tvar(0)), tabs(0, TBase, tvar(0))),
                     tabs(0, TBase, tvar(0)), n);
{
}

/// Typing

// A context is a partial map from variable names to types.
function find(c: map<int,ty>, x: int): option<ty>
{
  if x in c then Some(c[x]) else None
}

function extend(x: int, T: ty, c: map<int,ty>): map<int,ty>
{
  c[x := T]
}

// Typing Relation
function has_type(c: map<int,ty>, t: tm): option<ty>
{
  match t
  {
    case tvar(id) => find(c, id)
    case tabs(x, T, body) =>
      var ty_body := has_type(extend(x, T, c), body);
      if ty_body.Some? then Some(TArrow(T, ty_body.get)) else None
    case tapp(f, arg) =>
      var ty_f := has_type(c, f);
      var ty_arg := has_type(c, arg);
      if ty_f.Some? && ty_arg.Some? && ty_f.get is TArrow(T1, T2) && T1 == ty_arg.get then Some(T2) else None
  }
}

// Examples

lemma example_typing_1()
  ensures has_type(map[], tabs(0, TBase, tvar(0))) == Some(TArrow(TBase, TBase));
{
}

lemma example_typing_2()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TArrow(TBase, TBase), tapp(tvar(1), tapp(tvar(1), tvar(0)))))) ==
          Some(TArrow(TBase, TArrow(TArrow(TBase, TBase), TBase)));
{
}

lemma nonexample_typing_1()
  ensures has_type(map[], tabs(0, TBase, tabs(1, TBase, tapp(tvar(0), tvar(1))))) == None;
{
}

lemma nonexample_typing_3(S: ty, T: ty)
  ensures has_type(map[], tabs(0, S, tapp(tvar(0), tvar(0)))) != Some(T);
{
}

/// -----------------------
/// Type-Safety Properties
/// -----------------------

// Progress:
lemma theorem_progress(t: tm)
  requires has_type(map[], t).Some?;
  ensures value(t) || step(t).Some?;
{
}

// Preservation:
lemma theorem_preservation(t: tm)
  requires has_type(map[], t).Some?;
  requires step(t).Some?;
  ensures has_type(map[], step(t).get) == has_type(map[], t);
{
  if t is tapp(f, arg) && f is tabs(x, T, body) && value(arg) {
    // Apply substitution lemma here
  }
}

// A normal form cannot step.
predicate normal_form(t: tm)
{
  step(t).None?
}

// A stuck term is a normal form that is not a value.
predicate stuck(t: tm)
{
  normal_form(t) && !value(t)
}

// Type soundness:
lemma corollary_soundness(t: tm, t': tm, T: ty, n: nat)
  requires has_type(map[], t) == Some(T);
  requires reduces_to(t, t', n);
  ensures !stuck(t');
{
  theorem_progress(t);
  if t != t' {
    theorem_preservation(t);
    corollary_soundness(step(t).get, t', T, n-1);
  }
}

/// QED
