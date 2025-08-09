/- Copyright © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Demo 13: Basic Mathematical Structures

We introduce definitions and proofs about basic mathematical structures such as
groups, fields, and linear orders. -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## Type Classes over a Single Binary Operator

Mathematically, a __group__ is a set `G` with a binary operator `⬝ : G × G → G`
with the following properties, called __group axioms__:

* associativity: for all `a, b, c ∈ G`, we have `(a ⬝ b) ⬝ c = a ⬝ (b ⬝ c)`;
* identity element: there exists an element `e ∈ G` such that for all `a ∈ G`,
  we have `e ⬝ a = a` and `a ⬝ e = a`;
* inverse element: for each `a ∈ G`, there exists an inverse element
  `b ∈ G` such that `b ⬝ a = e` and `a ⬝ b = e`.

Examples of groups are
* `ℤ` with `+`;
* `ℝ` with `+`;
* `ℝ \ {0}` with `*`.

In Lean, a type class for groups can be defined as follows: -/

namespace MonolithicGroup

class Group (α : Type) where
  mul          : α → α → α
  one          : α
  inv          : α → α
  mul_assoc    : ∀a b c, mul (mul a b) c = mul a (mul b c)
  one_mul      : ∀a, mul one a = a
  mul_left_inv : ∀a, mul (inv a) a = one

end MonolithicGroup

/- In Lean, however, group is part of a larger hierarchy of algebraic
structures:

Type class             | Properties                               | Examples
---------------------- | -----------------------------------------|-------------------
`Semigroup`            | associativity of `*`                     | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`Monoid`               | `Semigroup` with unit `1`                | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`LeftCancelSemigroup`  | `Semigroup` with `c * a = c * b → a = b` |
`RightCancelSemigroup` | `Semigroup` with `a * c = b * c → a = b` |
`Group`                | `Monoid` with inverse `⁻¹`               |

Most of these structures have commutative versions: `CommSemigroup`,
`CommMonoid`, `CommGroup`.

The __multiplicative__ structures (over `*`, `1`, `⁻¹`) are copied to produce
__additive__ versions (over `+`, `0`, `-`):

Type class                | Properties                                  | Examples
------------------------- | --------------------------------------------|-------------------
`AddSemigroup`            | associativity of `+`                        | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`AddMonoid`               | `AddSemigroup` with unit `0`                | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`AddLeftCancelSemigroup`  | `AddSemigroup` with `c + a = c + b → a = b` | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`AddRightCancelSemigroup` | `AddSemigroup` with `a + c = b + c → a = b` | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`AddGroup`                | `AddMonoid` with inverse `-`                | `ℝ`, `ℚ`, `ℤ` -/

#print Group
#print AddGroup

/- Let us define our own type, of integers modulo 2, and register it as an
additive group. -/

inductive Int2 : Type
  | zero
  | one

def Int2.add : Int2 → Int2 → Int2
  | Int2.zero, a         => a
  | Int2.one,  Int2.zero => Int2.one
  | Int2.one,  Int2.one  => Int2.zero

instance Int2.AddGroup : AddGroup Int2 :=
  { add            := Int2.add
    zero           := Int2.zero
    neg            := fun a ↦ a
    add_assoc      :=
      by
        intro a b c
        cases a <;>
          cases b <;>
          cases c <;>
          rfl
    zero_add       :=
      by
        intro a
        cases a <;>
          rfl
    add_zero       :=
      by
        intro a
        cases a <;>
          rfl
    neg_add_cancel :=
      by
        intro a
        cases a <;>
          rfl
    nsmul         :=
      @nsmulRec Int2 (Zero.mk Int2.zero) (Add.mk Int2.add)
    zsmul         :=
      @zsmulRec Int2 (Zero.mk Int2.zero) (Add.mk Int2.add)
        (Neg.mk (fun a ↦ a))
        (@nsmulRec Int2 (Zero.mk Int2.zero) (Add.mk Int2.add)) }

/- `nsmul` and `znmul` are redundant. They are needed for technical reasons. -/

#reduce Int2.one + 0 - 0 - Int2.one

/- Another example: Lists are an `AddMonoid`: -/

instance List.AddMonoid {α : Type} : AddMonoid (List α) :=
  { zero      := []
    add       := fun xs ys ↦ xs ++ ys
    add_assoc := List.append_assoc
    zero_add  := List.nil_append
    add_zero  := List.append_nil
    nsmul     :=
      @nsmulRec (List α) (Zero.mk [])
        (Add.mk (fun xs ys ↦ xs ++ ys))}


/- ## Type Classes with Two Binary Operators

Mathematically, a __field__ is a set `F` such that

* `F` forms a commutative group under an operator `+`, called addition, with
  identity element `0`.
* `F \ {0}` forms a commutative group under an operator `*`, called
  multiplication.
* Multiplication distributes over addition—i.e.,
  `a * (b + c) = a * b + a * c` for all `a, b, c ∈ F`.

In Lean, fields are also part of a larger hierarchy:

Type class      |  Properties                                         | Examples
----------------|-----------------------------------------------------|-------------------
`Semiring`      | `Monoid` and `AddCommMonoid` with distributivity    | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`CommSemiring`  | `Semiring` with commutativity of `*`                | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`Ring`          | `Monoid` and `AddCommGroup` with distributivity     | `ℝ`, `ℚ`, `ℤ`
`CommRing`      | `Ring` with commutativity of `*`                    | `ℝ`, `ℚ`, `ℤ`
`DivisionRing`  | `Ring` with multiplicative inverse `⁻¹`             | `ℝ`, `ℚ`
`Field`         | `DivisionRing` with commutativity of `*`            | `ℝ`, `ℚ` -/

#print Field

/- We continue with our example: -/

def Int2.mul : Int2 → Int2 → Int2
  | Int2.one,  a => a
  | Int2.zero, _ => Int2.zero

theorem Int2.mul_assoc (a b c : Int2) :
     Int2.mul (Int2.mul a b) c = Int2.mul a (Int2.mul b c) :=
  by
    cases a <;>
      cases b <;>
      cases c <;>
      rfl

instance Int2.Field : Field Int2 :=
  { Int2.AddGroup with
    one            := Int2.one
    mul            := Int2.mul
    inv            := fun a ↦ a
    add_comm       :=
      by
        intro a b
        cases a <;>
          cases b <;>
          rfl
    exists_pair_ne :=
      by
        apply Exists.intro Int2.zero
        apply Exists.intro Int2.one
        simp
    zero_mul       :=
      by
        intro a
        rfl
    mul_zero       :=
      by
        intro a
        cases a <;>
          rfl
    one_mul        :=
      by
        intro a
        rfl
    mul_one        :=
      by
        intro a
        cases a <;>
          rfl
    mul_inv_cancel :=
      by
        intro a h
        cases a
        { apply False.elim
          apply h
          rfl }
        { rfl }
    inv_zero       := by rfl
    mul_assoc      := Int2.mul_assoc
    mul_comm       :=
      by
        intro a b
        cases a <;>
          cases b <;>
          rfl
    left_distrib   :=
      by
        intro a b c
        cases a <;>
          cases b <;>
          rfl
    right_distrib  :=
      by
        intro a b c
        cases a <;>
          cases b <;>
          cases c <;>
          rfl
    nnqsmul        := _
    nnqsmul_def    :=
      by
        intro a b
        rfl
    qsmul          := _
    qsmul_def :=
      by
        intro a b
        rfl
    nnratCast_def  :=
      by
        intro q
        rfl }

#reduce (1 : Int2) * 0 / (0 - 1)

#reduce (3 : Int2)

theorem ring_example (a b : Int2) :
    (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3
    :=
  by ring

/- `ring` proves equalities over commutative rings and semirings by normalizing
expressions.


## Coercions

When combining numbers form `ℕ`, `ℤ`, `ℚ`, and `ℝ`, we might want to cast from
one type to another. Lean has a mechanism to automatically introduce coercions,
represented by `Coe.coe` (syntactic sugar: `↑`). `Coe.coe` can be set up to
provide implicit coercions between arbitrary types.

Many coercions are already in place, including the following:

* `Coe.coe : ℕ → α` casts `ℕ` to another semiring `α`;
* `Coe.coe : ℤ → α` casts `ℤ` to another ring `α`;
* `Coe.coe : ℚ → α` casts `ℚ` to another division ring `α`.

For example, this works, even though negation `- n` is not defined on natural
numbers: -/

theorem neg_mul_neg_Nat (n : ℕ) (z : ℤ) :
    (- z) * (- n) = z * n :=
  by simp

/- Notice how Lean introduced a `↑` coercion: -/

#check neg_mul_neg_Nat

/- Type annotations can document our intentions: -/

theorem neg_Nat_mul_neg (n : ℕ) (z : ℤ) :
    (- n : ℤ) * (- z) = n * z :=
  by simp

#print neg_Nat_mul_neg

/- In proofs involving coercions, the tactic `norm_cast` can be convenient. -/

theorem Eq_coe_int_imp_Eq_Nat (m n : ℕ)
      (h : (m : ℤ) = (n : ℤ)) :
    m = n :=
  by norm_cast at h

theorem Nat_coe_Int_add_eq_add_Nat_coe_Int (m n : ℕ) :
    (m : ℤ) + (n : ℤ) = ((m + n : ℕ) : ℤ) :=
  by norm_cast

/- `norm_cast` moves coercions towards the inside of expressions, as a form of
simplification. Like `simp`, it will often produce a subgoal.

`norm_cast` relies on theorems such as these: -/

#check Nat.cast_add
#check Int.cast_add
#check Rat.cast_add


/- ### Lists, Multisets, and Finite Sets

For finite collections of elements different structures are available:

* lists: order and duplicates matter;
* multisets: only duplicates matter;
* finsets: neither order nor duplicates matter. -/

theorem List_duplicates_example :
    [2, 3, 3, 4] ≠ [2, 3, 4] :=
  by decide

theorem List_order_example :
    [4, 3, 2] ≠ [2, 3, 4] :=
  by decide

theorem Multiset_duplicates_example :
    ({2, 3, 3, 4} : Multiset ℕ) ≠ {2, 3, 4} :=
  by decide

theorem Multiset_order_example :
    ({2, 3, 4} : Multiset ℕ) = {4, 3, 2} :=
  by decide

theorem Finset_duplicates_example :
    ({2, 3, 3, 4} : Finset ℕ) = {2, 3, 4} :=
  by decide

theorem Finset_order_example :
    ({2, 3, 4} : Finset ℕ) = {4, 3, 2} :=
  by decide

/- `decide` is a tactic that can be used on true decidable goals (e.g., a true
executable expression). -/

def List.elems : Tree ℕ → List ℕ
  | Tree.nil        => []
  | Tree.node a l r => a :: List.elems l ++ List.elems r

def Multiset.elems : Tree ℕ → Multiset ℕ
  | Tree.nil        => ∅
  | Tree.node a l r =>
    {a} ∪ Multiset.elems l ∪ Multiset.elems r

def Finset.elems : Tree ℕ → Finset ℕ
  | Tree.nil        => ∅
  | Tree.node a l r => {a} ∪ Finset.elems l ∪ Finset.elems r

#eval List.sum [2, 3, 4]
#eval Multiset.sum ({2, 3, 4} : Multiset ℕ)

#eval List.prod [2, 3, 4]
#eval Multiset.prod ({2, 3, 4} : Multiset ℕ)


/- ## Order Type Classes

Many of the structures introduced above can be ordered. For example, the
well-known order on the natural numbers can be defined as follows: -/

inductive Nat.le : ℕ → ℕ → Prop
  | refl : ∀a : ℕ, Nat.le a a
  | step : ∀a b : ℕ, Nat.le a b → Nat.le a (b + 1)

#print Preorder

/- This is an example of a linear order. A __linear order__ (or
__total order__) is a binary relation `≤` such that for all `a`, `b`, `c`, the
following properties hold:

* reflexivity: `a ≤ a`;
* transitivity: if `a ≤ b` and `b ≤ c`, then `a ≤ c`;
* antisymmetry: if `a ≤ b` and `b ≤ a`, then `a = b`;
* totality: `a ≤ b` or `b ≤ a`.

If a relation has the first three properties, it is a __partial order__. An
example is `⊆` on sets, finite sets, or multisets. If a relation has the first
two properties, it is a __preorder__. An example is comparing lists by their
length.

In Lean, there are type classes for these different kinds of orders:
`LinearOrdeer`, `PartialOrder`, and `Preorder`. -/

#print Preorder
#print PartialOrder
#print LinearOrder

/- We can declare the preorder on lists that compares lists by their length as
follows: -/

instance List.length.Preorder {α : Type} : Preorder (List α) :=
  { le :=
      fun xs ys ↦ List.length xs ≤ List.length ys
    lt :=
      fun xs ys ↦ List.length xs < List.length ys
    le_refl :=
      by
        intro xs
        apply Nat.le_refl
    le_trans :=
      by
        intro xs ys zs
        exact Nat.le_trans
    lt_iff_le_not_ge :=
      by
        intro a b
        exact Nat.lt_iff_le_not_le }

/- This instance introduces the infix syntax `≤` and the relations `≥`, `<`,
and `>`: -/

theorem list.length.Preorder_example :
    [1] > [] :=
  by decide

/- Complete lattices (lecture 11) are formalized as another type class,
`CompleteLattice`, which inherits from `PartialOrder`.

Type classes combining orders and algebraic structures are also available:

    `OrderedCancelCommMonoid`
    `OrderedCommGroup`
    `OrderedSemiring`
    `LinearOrderedSemiring`
    `LinearOrderedCommRing`
    `LinearOrderedField`

All these mathematical structures relate `≤` and `<` with `0`, `1`, `+`, and `*`
by monotonicity rules (e.g., `a ≤ b → c ≤ d → a + c ≤ b + d`) and cancellation
rules (e.g., `c + a ≤ c + b → a ≤ b`). -/

end LoVe
