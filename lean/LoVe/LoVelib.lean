/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import Aesop
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Tree.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


/- # LoVelib: Logical Verification Library -/


set_option autoImplicit false
set_option tactic.hygienic false

open Lean
open Lean.Parser
open Lean.Parser.Term
open Lean.Meta
open Lean.Elab.Tactic
open Lean.TSyntax

namespace LoVe


/- ## Structured Proofs -/

@[term_parser] def «fix» :=
  leading_parser withPosition ("fix " >> many1 Term.ident >> " : " >> termParser)
  >> optSemicolon termParser

@[term_parser] def «assume» :=
  leading_parser withPosition ("assume " >> Term.ident >> " : " >> termParser)
  >> optSemicolon termParser

macro_rules
| `(fix $x* : $ty; $y) => `(fun $x* : $ty ↦ $y)
| `(assume $h : $ty; $y) => `(fun $h : $ty ↦ $y)


/- ## Natural Numbers -/

theorem Nat.two_mul (n : ℕ) :
    2 * n = n + n :=
  by ring

@[simp] theorem Nat.sub_one_add (n m : ℕ) (h : ¬ n = 0) :
    n - 1 + m = n + m - 1 :=
  by
    induction n with
    | zero => aesop
    | succ => simp

@[simp] theorem Nat.le_lt_imp (m n : ℕ) (p : Prop) (hge : m ≥ n) :
    (m < n → p) ↔ True :=
  by
    apply Iff.intro
    { intro himp
      apply True.intro }
    { intro htrue
      intro hlt
      have hle : n ≤ m :=
        hge
      rw [←Nat.not_lt_eq] at hle
      aesop }

@[simp] theorem Nat.lt_succ {m n : ℕ} :
    Nat.succ m < Nat.succ n ↔ m < n :=
  by
    apply Iff.intro
    { apply Nat.lt_of_succ_lt_succ }
    { apply Nat.succ_lt_succ }

@[simp] theorem Nat.le_succ {m n : ℕ} :
    Nat.succ m ≤ Nat.succ n ↔ m ≤ n :=
  by
    apply Iff.intro
    { apply Nat.le_of_succ_le_succ }
    { apply Nat.succ_le_succ }


/- ## Integers -/

@[simp] theorem Int.neg_neg :
    Int.neg ∘ Int.neg = id :=
  by
    apply funext
    intro i
    cases i with
    | ofNat n =>
      { cases n <;>
          aesop }
    | negSucc n =>
      { aesop }


/- ## Rationals -/

@[simp] theorem Rat.div_two_add_div_two (x : ℚ) :
    x / 2 + x / 2 = x :=
  by ring_nf


/- ## Lists -/

@[simp] theorem List.count_nil {α : Type} [BEq α] (x : α) :
    List.count x [] = 0 :=
  by rfl

@[simp] theorem List.count_cons {α : Type} [BEq α] (x a : α) (as : List α) :
    List.count x (a :: as) = (bif a == x then 1 else 0) + List.count x as :=
  by
    cases Classical.em (a == x) with
    | inl hx =>
      rw [List.count]
      simp [hx]
      ac_rfl
    | inr hx =>
      rw [List.count]
      simp [hx]

@[simp] theorem List.count_append {α : Type} [BEq α] (x : α) (as bs : List α) :
    List.count x (as ++ bs) = List.count x as + List.count x bs :=
  by
    induction as with
    | nil           => simp
    | cons a as' ih =>
      simp [ih]
      ac_rfl


/- ## Sets -/

@[aesop norm simp] theorem Set.subseteq_def {α : Type} (A B : Set α) :
    A ⊆ B ↔ ∀a, a ∈ A → a ∈ B :=
  by rfl

instance Set.PartialOrder {α : Type} : PartialOrder (Set α) :=
  { le               := fun A B ↦ A ⊆ B,
    lt               := fun A B ↦ A ⊆ B ∧ A ≠ B,
    le_refl          :=
      by
        intro A a ha
        assumption
    le_trans         :=
      by
        intro A B C hAB hBC a ha
        aesop,
    lt_iff_le_not_ge :=
      by
        intro A B
        apply Iff.intro
        { intro hAB
          simp [LT.lt, LE.le] at *
          cases hAB with
          | intro hsseq hneq =>
            apply And.intro
            { assumption }
            { intro hflip
              apply hneq
              apply Set.ext
              aesop } }
        { intro hAB
          simp [LT.lt, LE.le] at *
          aesop },
    le_antisymm      :=
      by
        intro A B hAB hBA
        apply Set.ext
        aesop }

@[simp] theorem Set.le_def {α : Type} (A B : Set α) :
    A ≤ B ↔ A ⊆ B :=
  by rfl

@[simp] theorem Set.lt_def {α : Type} (A B : Set α) :
    A < B ↔ A ⊆ B ∧ A ≠ B :=
  by rfl

inductive Set.Finite {α : Type} : Set α → Prop where
  | empty                      : Set.Finite {}
  | insert (a : α) (A : Set α) : Set.Finite A → Set.Finite (insert a A)


/- ## Relations -/

def Id {α : Type} : Set (α × α) :=
  {ab | Prod.snd ab = Prod.fst ab}

@[simp] theorem mem_Id {α : Type} (a b : α) :
    (a, b) ∈ @Id α ↔ b = a :=
  by rfl

def comp {α : Type} (r₁ r₂ : Set (α × α)) : Set (α × α) :=
  {ac | ∃b, (Prod.fst ac, b) ∈ r₁ ∧ (b, Prod.snd ac) ∈ r₂}

infixl:90 " ◯ " => comp

@[simp] theorem mem_comp {α : Type} (r₁ r₂ : Set (α × α)) (a b : α) :
    (a, b) ∈ r₁ ◯ r₂ ↔ (∃c, (a, c) ∈ r₁ ∧ (c, b) ∈ r₂) :=
  by rfl

def restrict {α : Type} (r : Set (α × α)) (p : α → Prop) :Set (α × α) :=
  {ab | ab ∈ r ∧ p (Prod.fst ab)}

infixl:90 " ⇃ " => restrict

@[simp] theorem mem_restrict {α : Type} (r : Set (α × α))
      (P : α → Prop) (a b : α) :
    (a, b) ∈ r ⇃ P ↔ (a, b) ∈ r ∧ P a :=
  by rfl


/- ## Reflexive Transitive Closure -/

inductive RTC {α : Type} (R : α → α → Prop) (a : α) : α → Prop
  | refl : RTC R a a
  | tail (b c) (hab : RTC R a b) (hbc : R b c) : RTC R a c

namespace RTC

theorem trans {α : Type} {R : α → α → Prop} {a b c : α} (hab : RTC R a b)
      (hbc : RTC R b c) :
    RTC R a c :=
  by
    induction hbc with
    | refl =>
      assumption
    | tail c d hbc hcd hac =>
      apply tail <;>
        assumption

theorem single {α : Type} {R : α → α → Prop} {a b : α} (hab : R a b) :
    RTC R a b :=
  tail _ _ refl hab

theorem head {α : Type} {R : α → α → Prop} (a b c : α) (hab : R a b)
      (hbc : RTC R b c) :
    RTC R a c :=
  by
    induction hbc with
    | refl =>
      exact tail _ _ refl hab
    | tail c d hbc hcd hac =>
      apply tail <;>
        assumption

theorem head_induction_on {α : Type} {R : α → α → Prop} {b : α}
      {P : ∀a : α, RTC R a b → Prop} {a : α} (h : RTC R a b)
      (refl : P b refl)
      (head : ∀a c (h' : R a c) (h : RTC R c b),
         P c h → P a (RTC.head _ _ _ h' h)) :
    P a h :=
  by
    induction h with
    | refl =>
      exact refl
    | tail b' c _ hb'c ih =>
      apply ih (P := fun a hab' ↦ P a (RTC.tail _ _ hab' hb'c))
      { exact head _ _ hb'c _ refl }
      { intro x y hxy hyb' hy
        exact head _ _ hxy _ hy }

theorem lift {α β : Type} {R : α → α → Prop} {S : β → β → Prop} {a b : α}
      (f : α → β) (hf : ∀a b, R a b → S (f a) (f b)) (hab : RTC R a b) :
    RTC S (f a) (f b) :=
  by
    induction hab with
    | refl => apply refl
    | tail b c hab hbc ih =>
      apply tail
      apply ih
      apply hf
      exact hbc

theorem mono {α : Type} {R R' : α → α → Prop} {a b : α} :
    (∀a b, R a b → R' a b) → RTC R a b → RTC R' a b :=
  lift id

theorem RTC_RTC_eq {α : Type} {R : α → α → Prop} :
    RTC (RTC R) = RTC R :=
  funext
    (fix a : α
     funext
       (fix b : α
        propext (Iff.intro
          (assume h : RTC (RTC R) a b
           by
             induction h with
             | refl => exact refl
             | tail b c hab' hbc ih =>
               apply trans <;>
                 assumption)
          (mono
             (fix a b : α
              single)))))

end RTC


/- ## Setoids -/

attribute [simp] Setoid.refl


/- ## Metaprogramming -/

def cases (id : FVarId) : TacticM Unit :=
  do
    liftMetaTactic (fun goal ↦
      do
        let subgoals ← MVarId.cases goal id
        pure (List.map (fun subgoal ↦
            InductionSubgoal.mvarId (CasesSubgoal.toInductionSubgoal subgoal))
          (Array.toList subgoals)))


/- ## States -/

def State : Type :=
  String → ℕ

def State.update (name : String) (val : ℕ) (s : State) : State :=
  fun name' ↦ if name' = name then val else s name'

macro s:term "[" name:term "↦" val:term "]" : term =>
  `(State.update $name $val $s)

@[simp] theorem update_apply (name : String) (val : ℕ) (s : State) :
    (s[name ↦ val]) name = val :=
  by
    apply if_pos
    rfl

@[simp] theorem update_apply_neq (name name' : String) (val : ℕ) (s : State)
      (hneq : name' ≠ name) :
    (s[name ↦ val]) name' = s name' :=
  by
    apply if_neg
    assumption

@[simp] theorem update_override (name : String) (val₁ val₂ : ℕ) (s : State) :
    s[name ↦ val₂][name ↦ val₁] = s[name ↦ val₁] :=
  by
    apply funext
    intro name'
    cases Classical.em (name' = name) with
    | inl h => simp [h]
    | inr h => simp [h]

theorem update_swap (name₁ name₂ : String) (val₁ val₂ : ℕ) (s : State)
      (hneq : name₁ ≠ name₂) :
-- `hneq` should have `by decide` as an auto param, but this confuses `simp`.
-- See https://github.com/leanprover/lean4/issues/3257
    s[name₂ ↦ val₂][name₁ ↦ val₁] = s[name₁ ↦ val₁][name₂ ↦ val₂] :=
  by
    apply funext
    intro name'
    cases Classical.em (name' = name₁) with
    | inl h => simp [*]
    | inr h =>
      cases Classical.em (name' = name₁) with
      | inl h => simp [*]
      | inr h => simp [State.update, *]

@[simp] theorem update_id (name : String) (s : State) :
    s[name ↦ s name] = s :=
  by
    apply funext
    intro name'
    simp [State.update]
    intro heq
    simp [*]

@[simp] theorem update_same_const (name : String) (val : ℕ) :
    (fun _ ↦ val)[name ↦ val] = (fun _ ↦ val) :=
  by
    apply funext
    simp [State.update]

example (s : State) :
    s["a" ↦ 0]["a" ↦ 2] = s["a" ↦ 2] :=
  by simp

example (s : State) :
    (s["a" ↦ 0]) "b" = s "b" :=
  by simp

example (s : State) :
    s["a" ↦ 0]["b" ↦ 2] = s["b" ↦ 2]["a" ↦ 0] :=
  by simp [update_swap]

example (s : State) :
    s["a" ↦ s "a"]["b" ↦ 0] = s["b" ↦ 0] :=
  by simp

example (s : State) :
    (s["a" ↦ 0]["b" ↦ 0]) "c" = s "c" :=
  by simp (config := {decide := true})

end LoVe
