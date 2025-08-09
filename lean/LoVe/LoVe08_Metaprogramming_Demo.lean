/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Demo 8: Metaprogramming

Users can extend Lean with custom tactics and tools. This kind of
programming—programming the prover—is called metaprogramming.

Lean's metaprogramming framework uses mostly the same notions and syntax as
Lean's input language itself. Abstract syntax trees __reflect__ internal data
structures, e.g., for expressions (terms). The prover's internals are exposed
through Lean interfaces, which we can use for

* accessing the current context and goal;
* unifying expressions;
* querying and modifying the environment;
* setting attributes.

Most of Lean itself is implemented in Lean.

Example applications:

* proof goal transformations;
* heuristic proof search;
* decision procedures;
* definition generators;
* advisor tools;
* exporters;
* ad hoc automation.

Advantages of Lean's metaprogramming framework:

* Users do not need to learn another programming language to write
  metaprograms; they can work with the same constructs and notation used to
  define ordinary objects in the prover's library.

* Everything in that library is available for metaprogramming purposes.

* Metaprograms can be written and debugged in the same interactive environment,
  encouraging a style where formal libraries and supporting automation are
  developed at the same time. -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## Tactic Combinators

When programming our own tactics, we often need to repeat some actions on
several goals, or to recover if a tactic fails. Tactic combinators help in such
cases.

`repeat'` applies its argument repeatedly on all (sub…sub)goals until it cannot
be applied any further. -/

theorem repeat'_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    repeat' apply Even.add_two
    repeat' sorry

/- The "first" combinator `first | ⋯ | ⋯ | ⋯` tries its first argument. If that
fails, it applies its second argument. If that fails, it applies its third
argument. And so on. -/

theorem repeat'_first_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    repeat'
      first
      | apply Even.add_two
      | apply Even.zero
    repeat' sorry

/- `all_goals` applies its argument exactly once to each goal. It succeeds only
if the argument succeeds on **all** goals. -/

/-
theorem all_goals_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    all_goals apply Even.add_two   -- fails
    repeat' sorry
-/

/- `try` transforms its argument into a tactic that never fails. -/

theorem all_goals_try_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    all_goals try apply Even.add_two
    repeat sorry

/- `any_goals` applies its argument exactly once to each goal. It succeeds
if the argument succeeds on **any** goal. -/

theorem any_goals_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    any_goals apply Even.add_two
    repeat' sorry

/- `solve | ⋯ | ⋯ | ⋯` is like `first` except that it succeeds only if one of
the arguments fully proves the current goal. -/

theorem any_goals_solve_repeat_first_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    repeat' apply And.intro
    any_goals
      solve
      | repeat'
          first
          | apply Even.add_two
          | apply Even.zero
    repeat' sorry

/- The combinator `repeat'` can easily lead to infinite looping: -/

/-
-- loops
theorem repeat'_Not_example :
    ¬ Even 1 :=
  by repeat' apply Not.intro
-/


/- ## Macros -/

/- We start with the actual metaprogramming, by coding a custom tactic as a
macro. The tactic embodies the behavior we hardcoded in the `solve` example
above: -/

macro "intro_and_even" : tactic =>
  `(tactic|
      (repeat' apply And.intro
       any_goals
         solve
         | repeat'
             first
             | apply Even.add_two
             | apply Even.zero))

/- Let us apply our custom tactic: -/

theorem intro_and_even_example :
    Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 :=
  by
    intro_and_even
    repeat' sorry


/- ## The Metaprogramming Monads

`MetaM` is the low-level metaprogramming monad. `TacticM` extends `MetaM` with
goal management.

* `MetaM` is a state monad providing access to the global context (including all
  definitions and inductive types), notations, and attributes (e.g., the list of
  `@[simp]` theorems), among others. `TacticM` additionally provides access to
  the list of goals.

* `MetaM` and `TacticM` behave like an option monad. The metaprogram `failure`
  leaves the monad in an error state.

* `MetaM` and `TacticM` support tracing, so we can use `logInfo` to display
  messages.

* Like other monads, `MetaM` and `TacticM` support imperative constructs such as
  `for`–`in`, `continue`, and `return`. -/

def traceGoals : TacticM Unit :=
  do
    logInfo m!"Lean version {Lean.versionString}"
    logInfo "All goals:"
    let goals ← getUnsolvedGoals
    logInfo m!"{goals}"
    match goals with
    | []     => return
    | _ :: _ =>
      logInfo "First goal's target:"
      let target ← getMainTarget
      logInfo m!"{target}"

elab "trace_goals" : tactic =>
  traceGoals

theorem Even_18_and_Even_20 (α : Type) (a : α) :
    Even 18 ∧ Even 20 :=
  by
    apply And.intro
    trace_goals
    intro_and_even


/- ## First Example: An Assumption Tactic

We define a `hypothesis` tactic that behaves essentially the same as the
predefined `assumption` tactic. -/

def hypothesis : TacticM Unit :=
  withMainContext
    (do
       let target ← getMainTarget
       let lctx ← getLCtx
       for ldecl in lctx do
         if ! LocalDecl.isImplementationDetail ldecl then
           let eq ← isDefEq (LocalDecl.type ldecl) target
           if eq then
             let goal ← getMainGoal
             MVarId.assign goal (LocalDecl.toExpr ldecl)
             return
       failure)

elab "hypothesis" : tactic =>
  hypothesis

theorem hypothesis_example {α : Type} {p : α → Prop} {a : α}
      (hpa : p a) :
    p a :=
  by hypothesis


/- ## Expressions

The metaprogramming framework revolves around the type `Expr` of expressions or
terms. -/

#print Expr


/- ### Names

We can create literal names with backticks:

* Names with a single backtick, `n, are not checked for existence.

* Names with two backticks, ``n, are resolved and checked. -/

#check `x
#eval `x
#eval `Even          -- wrong
#eval `LoVe.Even     -- suboptimal
#eval ``Even
/-
#eval ``EvenThough   -- fails
-/


/- ### Constants -/

#check Expr.const

#eval ppExpr (Expr.const ``Nat.add [])
#eval ppExpr (Expr.const ``Nat [])


/- ### Sorts (lecture 12) -/

#check Expr.sort

#eval ppExpr (Expr.sort Level.zero)
#eval ppExpr (Expr.sort (Level.succ Level.zero))


/- ### Free Variables -/

#check Expr.fvar

#check FVarId.mk `n
#eval ppExpr (Expr.fvar (FVarId.mk `n))


/- ### Metavariables -/

#check Expr.mvar


/- ### Applications -/

#check Expr.app

#eval ppExpr (Expr.app (Expr.const ``Nat.succ [])
  (Expr.const ``Nat.zero []))


/- ### Anonymous Functions and Bound Variables -/

#check Expr.bvar
#check Expr.lam

#eval ppExpr (Expr.bvar 0)

#eval ppExpr (Expr.lam `x (Expr.const ``Nat []) (Expr.bvar 0)
  BinderInfo.default)

#eval ppExpr (Expr.lam `x (Expr.const ``Nat [])
  (Expr.lam `y (Expr.const ``Nat []) (Expr.bvar 1)
     BinderInfo.default)
  BinderInfo.default)


/- ### Dependent Function Types -/

#check Expr.forallE

#eval ppExpr (Expr.forallE `n (Expr.const ``Nat [])
  (Expr.app (Expr.const ``Even []) (Expr.bvar 0))
  BinderInfo.default)

#eval ppExpr (Expr.forallE `dummy (Expr.const `Nat [])
  (Expr.const `Bool []) BinderInfo.default)


/- ### Other Constructors -/

#check Expr.letE
#check Expr.lit
#check Expr.mdata
#check Expr.proj


/- ## Second Example: A Conjunction-Destructing Tactic

We define a `destruct_and` tactic that automates the elimination of `∧` in
premises, automating proofs such as these: -/

theorem abc_a (a b c : Prop) (h : a ∧ b ∧ c) :
    a :=
  And.left h

theorem abc_b (a b c : Prop) (h : a ∧ b ∧ c) :
    b :=
  And.left (And.right h)

theorem abc_bc (a b c : Prop) (h : a ∧ b ∧ c) :
    b ∧ c :=
  And.right h

theorem abc_c (a b c : Prop) (h : a ∧ b ∧ c) :
    c :=
  And.right (And.right h)

/- Our tactic relies on a helper function, which takes as argument the
hypothesis `h` to use as an expression: -/

partial def destructAndExpr (hP : Expr) : TacticM Bool :=
  withMainContext
    (do
       let target ← getMainTarget
       let P ← inferType hP
       let eq ← isDefEq P target
       if eq then
         let goal ← getMainGoal
         MVarId.assign goal hP
         return true
       else
         match Expr.and? P with
         | Option.none        => return false
         | Option.some (Q, R) =>
           let hQ ← mkAppM ``And.left #[hP]
           let success ← destructAndExpr hQ
           if success then
             return true
           else
             let hR ← mkAppM ``And.right #[hP]
             destructAndExpr hR)

#check Expr.and?

def destructAnd (name : Name) : TacticM Unit :=
  withMainContext
    (do
       let h ← getFVarFromUserName name
       let success ← destructAndExpr h
       if ! success then
         failure)

elab "destruct_and" h:ident : tactic =>
  destructAnd (getId h)

/- Let us check that our tactic works: -/

theorem abc_a_again (a b c : Prop) (h : a ∧ b ∧ c) :
    a :=
  by destruct_and h

theorem abc_b_again (a b c : Prop) (h : a ∧ b ∧ c) :
    b :=
  by destruct_and h

theorem abc_bc_again (a b c : Prop) (h : a ∧ b ∧ c) :
    b ∧ c :=
  by destruct_and h

theorem abc_c_again (a b c : Prop) (h : a ∧ b ∧ c) :
    c :=
  by destruct_and h

/-
theorem abc_ac (a b c : Prop) (h : a ∧ b ∧ c) :
    a ∧ c :=
  by destruct_and h   -- fails
-/


/- ## Third Example: A Direct Proof Finder

Finally, we implement a `prove_direct` tool that traverses all theorems in the
database and checks whether one of them can be used to prove the current
goal. -/

def isTheorem : ConstantInfo → Bool
  | ConstantInfo.axiomInfo _ => true
  | ConstantInfo.thmInfo _   => true
  | _                        => false

def applyConstant (name : Name) : TacticM Unit :=
  do
    let cst ← mkConstWithFreshMVarLevels name
    liftMetaTactic (fun goal ↦ MVarId.apply goal cst)

def andThenOnSubgoals (tac₁ tac₂ : TacticM Unit) :
  TacticM Unit :=
  do
    let origGoals ← getGoals
    let mainGoal ← getMainGoal
    setGoals [mainGoal]
    tac₁
    let subgoals₁ ← getUnsolvedGoals
    let mut newGoals := []
    for subgoal in subgoals₁ do
      let assigned ← MVarId.isAssigned subgoal
      if ! assigned then
        setGoals [subgoal]
        tac₂
        let subgoals₂ ← getUnsolvedGoals
        newGoals := newGoals ++ subgoals₂
    setGoals (newGoals ++ List.tail origGoals)

def proveUsingTheorem (name : Name) : TacticM Unit :=
  andThenOnSubgoals (applyConstant name) hypothesis

def proveDirect : TacticM Unit :=
  do
    let origGoals ← getUnsolvedGoals
    let goal ← getMainGoal
    setGoals [goal]
    let env ← getEnv
    for (name, info)
        in SMap.toList (Environment.constants env) do
      if isTheorem info && ! ConstantInfo.isUnsafe info then
        try
          proveUsingTheorem name
          logInfo m!"Proved directly by {name}"
          setGoals (List.tail origGoals)
          return
        catch _ =>
          continue
    failure

elab "prove_direct" : tactic =>
  proveDirect

/- Let us check that our tactic works: -/

theorem Nat.symm (x y : ℕ) (h : x = y) :
    y = x :=
  by prove_direct

theorem Nat.symm_manual (x y : ℕ) (h : x = y) :
    y = x :=
  by
    apply symm
    hypothesis

set_option maxHeartbeats 1000000

theorem Nat.trans (x y z : ℕ) (hxy : x = y) (hyz : y = z) :
    x = z :=
  by prove_direct

theorem List.reverse_twice (xs : List ℕ) :
    List.reverse (List.reverse xs) = xs :=
  by prove_direct

/- Lean has `apply?`: -/

theorem List.reverse_twice_apply? (xs : List ℕ) :
    List.reverse (List.reverse xs) = xs :=
  by apply?

end LoVe
