import semioverse

namespace Semioverse

-- ====================================================================
-- §8. GAP AND OBLIGATION
-- From Syntra-Labs/router (the manifold phase table) and
-- Syntra-Archive/taskflow (the patch judgment).
-- Kept: which phase steps exist, the four-part proof a step needs, and
-- the order in which a patch is refused.
-- Left there: similarity cutoffs, hypervectors, the Myers diff, Neovim.
-- ====================================================================

inductive Phase where
  | undiscovered
  | proposed
  | selected
  | applied
  | verified
  | rejected
  deriving DecidableEq, Repr

def Phase.terminal : Phase → Bool
  | .verified => true
  | .rejected => true
  | _ => false

/-- One forward step, and reject from any phase that is not already terminal. -/
def Phase.allows (src dst : Phase) : Bool :=
  match src, dst with
  | .undiscovered, .proposed => true
  | .proposed, .selected => true
  | .selected, .applied => true
  | .applied, .verified => true
  | src, .rejected => !src.terminal
  | _, _ => false

theorem verified_is_terminal (dst : Phase) :
    Phase.allows .verified dst = false := by
  cases dst <;> rfl

theorem rejected_is_terminal (dst : Phase) :
    Phase.allows .rejected dst = false := by
  cases dst <;> rfl

/-- `divisible` continues the phase you are actually in.
    `admissible` is the caller's claim that the table allows the step.
    `correct` is the step's own condition.
    `respectful` is that a reason was given.
    Acceptance checks the table itself, so a true `admissible` flag is not enough. -/
structure StepProof where
  src : Phase
  dst : Phase
  divisible : Bool
  admissible : Bool
  correct : Bool
  respectful : Bool

def StepProof.accepts (p : StepProof) : Prop :=
  p.divisible = true ∧ p.admissible = true ∧ p.correct = true ∧
    p.respectful = true ∧ Phase.allows p.src p.dst = true

theorem accept_needs_table (p : StepProof) (h : Phase.allows p.src p.dst = false) :
    ¬ p.accepts := by
  intro hacc
  have htable : Phase.allows p.src p.dst = true := hacc.2.2.2.2
  rw [h] at htable
  exact Bool.noConfusion htable

inductive Norm where
  | ok
  | prohibition
  | permission
  | invariantBroken
  | cycle
  deriving DecidableEq, Repr

/-- Prohibition is checked first, then permission, then the invariant, then acyclicity. -/
structure Obligation where
  permitted : Bool
  prohibited : Bool
  invariantHeld : Bool
  acyclic : Bool

def Obligation.judge (o : Obligation) : Norm :=
  if o.prohibited then .prohibition
  else if !o.permitted then .permission
  else if !o.invariantHeld then .invariantBroken
  else if !o.acyclic then .cycle
  else .ok

theorem judge_ok_iff (o : Obligation) :
    o.judge = .ok ↔
      o.permitted = true ∧ o.prohibited = false ∧
      o.invariantHeld = true ∧ o.acyclic = true := by
  rcases o with ⟨p, f, i, a⟩
  cases p <;> cases f <;> cases i <;> cases a <;> simp [Obligation.judge]

/-- A follow-up task may be named. Naming it does not realize it. -/
structure Spawn where
  parent : String
  child : String
  fresh : child ≠ parent

theorem spawned_child_is_fresh (s : Spawn) : s.child ≠ s.parent :=
  s.fresh

end Semioverse
