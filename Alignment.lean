import semioverse

namespace Semioverse.Alignment

open Semioverse

inductive Stage : Nat → Type where
  | su0 : Stage 0
  | su1 : Stage 1
  | su2 : Stage 2
  | su3 : Stage 3
  | su4 : Stage 4
  | su5 : Stage 5
  | su6 : Stage 6
  | su7 : Stage 7

structure Residual where
  id          : String
  stage       : Nat
  description : String
  blocked_by  : List String
  deriving Repr

structure TheorySnapshot where
  theorems_proven : List String
  residuals_open  : List Residual
  deriving Repr

def LedgerAdequate (s : TheorySnapshot) : Prop :=
  ∀ r ∈ s.residuals_open, r.id ≠ ""

theorem residual_dag_acyclic (rs : List Residual)
    (_h : ∀ r ∈ rs, ∀ b ∈ r.blocked_by, ∃ r' ∈ rs, r'.id = b) :
    ∀ r ∈ rs, r.id ∉ r.blocked_by := by
  sorry -- R-A1

theorem entry_conditions (rs : List Residual) :
    ∀ r ∈ rs, r.stage ≤ 7 := by
  sorry -- R-A2

theorem reaches_closure (rs : List Residual)
    (h : ∀ r ∈ rs, r.stage ≤ 7) :
    ∀ r ∈ rs, r.id ≠ "" := by
  sorry -- R-A3

theorem self_reference_closes (s : TheorySnapshot)
    (h : LedgerAdequate s) :
    ∀ r ∈ s.residuals_open, r.id ≠ "" := by
  sorry -- R-A4

end Semioverse.Alignment
