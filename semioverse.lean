-- semioverse.lean — Formal Theory of Software Artifacts, Part 1
namespace Semioverse

-- ====================================================================
-- §1. DEFINITIONS
-- ====================================================================

abbrev NodeId := Nat

structure Property where
  key   : String
  value : String
  deriving DecidableEq, Repr

structure TopologyGraph where
  nodes : List NodeId
  edges : List (NodeId × NodeId)
  props : List (NodeId × Property)
  deriving DecidableEq, Repr

structure State where
  desired  : Nat
  actual   : Nat
  topology : TopologyGraph
  deriving DecidableEq, Repr

def PolicyPredicate := State → Prop

def ValidTopologyPolicy (s : State) : Prop :=
  !s.topology.nodes.isEmpty ∧ s.desired >= s.actual

inductive Delta where
  | stepToward (target : Nat)
  | addNode    (id : NodeId)
  | noop
  deriving DecidableEq, Repr

def stepTowardState (s : State) (target : Nat) : State :=
  if s.actual < target then { s with actual := s.actual + 1 }
  else if s.actual > target then { s with actual := s.actual - 1 }
  else s

def applyDelta (s : State) : Delta → State
  | .stepToward target => stepTowardState s target
  | .addNode id =>
      { s with topology := { s.topology with nodes := id :: s.topology.nodes } }
  | .noop => s

def Trace (α : Type) := Nat → α

def Always {α : Type} (P : Trace α → Prop) (σ : Trace α) : Prop :=
  ∀ n : Nat, P (fun k => σ (n + k))

def Eventually {α : Type} (P : Trace α → Prop) (σ : Trace α) : Prop :=
  ∃ n : Nat, P (fun k => σ (n + k))

def LeadsTo {α : Type} (P Q : Trace α → Prop) (σ : Trace α) : Prop :=
  Always (fun τ => P τ → Eventually Q τ) σ

def DesireAt (d : Nat) : Trace State → Prop :=
  fun τ => (τ 0).desired = d

def MatchAt (d : Nat) : Trace State → Prop :=
  fun τ => (τ 0).actual = d

def EventuallyStableReconcile (d : Nat) (σ : Trace State) : Prop :=
  LeadsTo (Always (DesireAt d)) (Always (MatchAt d)) σ

structure TelemetrySummary where
  sampleCount : Nat
  lastActual  : Nat
  deriving DecidableEq, Repr

def O_Observe (σ : Trace State) (samples : Nat) : TelemetrySummary :=
  { sampleCount := samples, lastActual := (σ samples).actual }

structure Lens (A B : Type) where
  get    : A × B → A
  put    : A × B → A → A × B
  getPut : ∀ c : A × B, put c (get c) = c
  putGet : ∀ (c : A × B) (a : A), get (put c a) = a

def brokenPut {A B : Type} (b0 : B) (_c : A × B) (a : A) : A × B :=
  (a, b0)

theorem brokenPut_violates_getPut {A B : Type} (a : A) (b b0 : B) (h : b ≠ b0) :
    brokenPut b0 (a, b) a ≠ (a, b) := by
  intro hEq
  have hb : b0 = b := congrArg Prod.snd hEq
  exact h hb.symm

structure BuildTask (K V : Type) where
  key  : K
  deps : List K

def BuildStore (K V : Type) := K → Option V

def runTask {K V : Type} [DecidableEq K]
    (store : BuildStore K V) (task : BuildTask K V)
    (changedDeps : List K) (newValue : V) : BuildStore K V :=
  if changedDeps.isEmpty then store
  else fun k => if k = task.key then some newValue else store k

structure Patch (Tree : Type) where
  apply  : Tree → Option Tree
  invert : Tree → Option Tree

def Commutes {Tree : Type} (p1 p2 : Patch Tree) (t : Tree) : Prop :=
  (p1.apply t >>= p2.apply) = (p2.apply t >>= p1.apply)

structure Package where
  name    : String
  version : Nat
  deriving DecidableEq, Repr

structure DependencyHypergraph where
  packages : List Package
  requires : Package → List (List Package)

def DependencyHypergraph.Satisfiable (h : DependencyHypergraph) : Prop :=
  ∀ p, p ∈ h.packages → ∀ disj, disj ∈ h.requires p →
    ∃ q, q ∈ disj ∧ q ∈ h.packages

def DependencyHypergraph.isSatisfiable (h : DependencyHypergraph) : Bool :=
  h.packages.all fun p =>
    (h.requires p).all fun disj =>
      disj.any fun q => h.packages.contains q

def HyperGraphResolve (h : DependencyHypergraph) : Option (List Package) :=
  if h.isSatisfiable then some h.packages else none

structure DesignToken where
  name  : String
  value : String
  deriving DecidableEq, Repr

structure UITree where
  node     : String
  children : List UITree
  deriving Repr

def Pi_UI (s : State) (_tokens : List DesignToken) : UITree :=
  { node := s!"View(desired={s.desired}, actual={s.actual}, nodes={s.topology.nodes.length})",
    children := [] }

-- ====================================================================
-- §2. WELL-FORMEDNESS
-- ====================================================================

def TopologyGraph.WellFormed (g : TopologyGraph) : Prop :=
  g.nodes.Nodup ∧
  (∀ e, e ∈ g.edges → e.1 ∈ g.nodes ∧ e.2 ∈ g.nodes)

def State.WellFormed (s : State) : Prop :=
  s.topology.WellFormed

def Patch.WellFormed {Tree : Type} (p : Patch Tree) : Prop :=
  ∀ (t t' : Tree), p.apply t = some t' → p.invert t' = some t

def BuildTask.WellFormed {K V : Type} (task : BuildTask K V) : Prop :=
  task.key ∉ task.deps

def DependencyHypergraph.WellFormed (h : DependencyHypergraph) : Prop :=
  ∀ p, p ∈ h.packages → ∀ disj, disj ∈ h.requires p →
    ∀ q, q ∈ disj → q ∈ h.packages

-- ====================================================================
-- §3. NON-VACUITY
-- ====================================================================

def exampleTopo : TopologyGraph :=
  { nodes := [0], edges := [], props := [] }

theorem exampleTopo_well_formed : exampleTopo.WellFormed := by
  refine ⟨?_, ?_⟩
  · simp [exampleTopo]
  · intro e he
    simp [exampleTopo] at he

def exampleState : State :=
  { desired := 10, actual := 5, topology := exampleTopo }

theorem exampleState_well_formed : exampleState.WellFormed :=
  exampleTopo_well_formed

def idLens (A B : Type) : Lens A B where
  get    := fun (a, _) => a
  put    := fun (_, b) a' => (a', b)
  getPut := by intro c; cases c; rfl
  putGet := by intro c a; rfl

theorem idLens_exists (A B : Type) : Nonempty (Lens A B) :=
  ⟨idLens A B⟩

def idPatch (Tree : Type) : Patch Tree :=
  { apply := some, invert := some }

theorem idPatch_well_formed (Tree : Type) : (idPatch Tree).WellFormed := by
  intro t t' h
  simp [idPatch] at h
  subst h
  rfl

def exampleTask : BuildTask String Unit :=
  { key := "build", deps := ["parse", "typecheck"] }

theorem exampleTask_well_formed : exampleTask.WellFormed := by
  unfold BuildTask.WellFormed
  decide

def examplePkg : Package := { name := "core", version := 1 }

def exampleHypergraph : DependencyHypergraph :=
  { packages := [examplePkg],
    requires := fun _ => [] }

theorem exampleHypergraph_well_formed : exampleHypergraph.WellFormed := by
  intro p hp disj hd q hq
  simp [exampleHypergraph] at hd

theorem runTask_preserves_on_no_change {K V : Type} [DecidableEq K]
    (store : BuildStore K V) (task : BuildTask K V) (newValue : V) :
    runTask store task [] newValue = store := by
  simp [runTask]

theorem HyperGraphResolve_some_iff (h : DependencyHypergraph) :
    HyperGraphResolve h = some h.packages ↔ h.isSatisfiable = true := by
  unfold HyperGraphResolve
  split <;> simp_all

-- ====================================================================
-- §3.5. STEPTOWARDSTATE HELPERS
-- ====================================================================

theorem stepTowardState_desired (s : State) (target : Nat) :
    (stepTowardState s target).desired = s.desired := by
  unfold stepTowardState
  split
  · rfl
  · split <;> rfl

theorem stepTowardState_topology (s : State) (target : Nat) :
    (stepTowardState s target).topology = s.topology := by
  unfold stepTowardState
  split
  · rfl
  · split <;> rfl

theorem stepTowardState_le (s : State) (target : Nat) (h : s.actual ≤ target) :
    (stepTowardState s target).actual ≤ target := by
  unfold stepTowardState
  split
  · omega
  · split <;> omega

theorem applyDelta_stepToward_eq (s : State) (target : Nat) :
    applyDelta s (Delta.stepToward target) = stepTowardState s target := rfl

theorem applyDelta_stepToward_preserves_desired (s : State) (target : Nat) :
    (applyDelta s (Delta.stepToward target)).desired = s.desired := by
  rw [applyDelta_stepToward_eq]
  exact stepTowardState_desired s target

theorem applyDelta_stepToward_preserves_topology (s : State) (target : Nat) :
    (applyDelta s (Delta.stepToward target)).topology = s.topology := by
  rw [applyDelta_stepToward_eq]
  exact stepTowardState_topology s target

theorem applyDelta_stepToward_le (s : State) (target : Nat) (h : s.actual ≤ target) :
    (applyDelta s (Delta.stepToward target)).actual ≤ target := by
  rw [applyDelta_stepToward_eq]
  exact stepTowardState_le s target h

theorem stepToward_increases_when_below (s : State) (h : s.actual < s.desired) :
    (applyDelta s (.stepToward s.desired)).actual = s.actual + 1 := by
  rw [applyDelta_stepToward_eq]
  unfold stepTowardState
  simp [h]

-- ====================================================================
-- §4. COMPOSITION THEOREM
-- ====================================================================

def stepTrace (s0 : State) : Trace State
  | 0     => s0
  | n + 1 => applyDelta (stepTrace s0 n) (.stepToward (stepTrace s0 n).desired)

theorem stepTrace_step (s0 : State) (n : Nat) :
    stepTrace s0 (n+1) = stepTowardState (stepTrace s0 n) (stepTrace s0 n).desired := by
  simp [stepTrace, applyDelta_stepToward_eq]

theorem stepTrace_desired_constant (s0 : State) (n : Nat) :
    (stepTrace s0 n).desired = s0.desired := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [stepTrace]
    rw [applyDelta_stepToward_preserves_desired]
    exact ih

theorem stepTrace_topology_constant (s0 : State) (n : Nat) :
    (stepTrace s0 n).topology = s0.topology := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [stepTrace]
    rw [applyDelta_stepToward_preserves_topology]
    exact ih

theorem stepTrace_actual_le_desired (s0 : State) (h : s0.actual ≤ s0.desired) (n : Nat) :
    (stepTrace s0 n).actual ≤ s0.desired := by
  induction n with
  | zero => exact h
  | succ n ih =>
    dsimp [stepTrace]
    rw [stepTrace_desired_constant s0 n]
    exact applyDelta_stepToward_le (stepTrace s0 n) s0.desired ih

theorem reconciliation_composition
    (s0 : State)
    (_h_wf  : s0.WellFormed)
    (h_pol : ValidTopologyPolicy s0) :
    (∀ n, ValidTopologyPolicy (stepTrace s0 n)) ∧
    (∀ n, (stepTrace s0 (n+1)).actual = (stepTrace s0 n).actual + 1
          ∨ (stepTrace s0 n).actual = s0.desired) := by
  constructor
  · intro n
    refine ⟨?_, ?_⟩
    · rw [stepTrace_topology_constant]; exact h_pol.1
    · rw [stepTrace_desired_constant]
      exact stepTrace_actual_le_desired s0 h_pol.2 n
  · intro n
    have h_le := stepTrace_actual_le_desired s0 h_pol.2 n
    rcases Nat.lt_trichotomy (stepTrace s0 n).actual s0.desired with hlt | heq | hgt
    · left
      have h_des := stepTrace_desired_constant s0 n
      rw [stepTrace_step]
      unfold stepTowardState
      rw [h_des]
      rw [if_pos hlt]
    · right; exact heq
    · omega

-- ====================================================================
-- §5. TRACKED STUBS (see residuals.csv)
-- ====================================================================

theorem stepTrace_eventually_stable (s0 : State) (h : s0.actual ≤ s0.desired) :
    EventuallyStableReconcile s0.desired (stepTrace s0) := by
  sorry -- R-2

theorem isSatisfiable_iff_Satisfiable (h : DependencyHypergraph) :
    h.isSatisfiable = true ↔ h.Satisfiable := by
  sorry -- R-3

def Patch.compose {T : Type} (p q : Patch T) : Patch T :=
  sorry -- R-4

theorem patch_commutation_disjoint {T : Type} (p q : Patch T) (t : T)
    (h : Patch.WellFormed p) (h' : Patch.WellFormed q) :
    Commutes p q t := by
  sorry -- R-5

def stateActualLens : Lens Nat State :=
  sorry -- R-6

theorem runBuild_minimal {K V : Type} [DecidableEq K]
    (store : BuildStore K V) (task : BuildTask K V) (newValue : V) :
    runTask store task [] newValue = store := by
  sorry -- R-7

theorem Pi_UI_homomorphism (s₁ s₂ : State) (tokens : List DesignToken) :
    Pi_UI { s₁ with actual := s₂.actual } tokens = Pi_UI s₂ tokens := by
  sorry -- R-8

theorem O_preserves_diagnostic (σ : Trace State) (samples : Nat) :
    (O_Observe σ samples).lastActual = (σ samples).actual := by
  sorry -- R-9

-- ====================================================================
-- §6. CUSTODY
-- Where an artifact lives, and where a policy is decided.
-- Independent of the reconciliation clock in §1–§4.
-- A tool is a witness that one of these properties holds, not an axiom.
-- `replica` is a copy on another device you hold (the VM, a phone, a USB).
-- `offbox` is a copy the acting node cannot rewrite (the second restic repo).
-- ====================================================================

inductive Locus where
  | here
  | replica
  | offbox
  deriving DecidableEq, Repr

inductive Encoding where
  | sqlite
  | file
  | git
  | opaqueServer
  deriving DecidableEq, Repr

def ReadableWithoutDaemon (e : Encoding) : Prop :=
  e = .sqlite ∨ e = .file ∨ e = .git

structure Artifact where
  name     : String
  encoding : Encoding
  replicas : List Locus
  deriving DecidableEq, Repr

/-- Survives the loss of `lost` when some other replica still holds it. -/
def Artifact.survives (a : Artifact) (lost : Locus) : Prop :=
  ∃ loc, loc ∈ a.replicas ∧ loc ≠ lost

theorem sole_replica_dies (a : Artifact) (loc : Locus)
    (h : a.replicas = [loc]) : ¬ a.survives loc := by
  intro hs
  rcases hs with ⟨loc', hmem, hne⟩
  rw [h] at hmem
  exact hne (List.mem_singleton.mp hmem)

theorem other_replica_survives (a : Artifact) (lost kept : Locus)
    (hmem : kept ∈ a.replicas) (hne : kept ≠ lost) : a.survives lost :=
  ⟨kept, hmem, hne⟩

/-- A gate holds only when both the decision and the opener sit off the actor. -/
structure Gate where
  decidedAt : Locus
  actedAt   : Locus
  openerAt  : Locus
  deriving DecidableEq, Repr

def Gate.holds (g : Gate) : Prop :=
  g.decidedAt ≠ g.actedAt ∧ g.openerAt ≠ g.actedAt

theorem colocated_not_boundary (g : Gate) (h : g.decidedAt = g.actedAt) :
    ¬ g.holds := by
  intro hg
  exact hg.1 h

theorem opener_on_actor_not_gate (g : Gate) (h : g.openerAt = g.actedAt) :
    ¬ g.holds := by
  intro hg
  exact hg.2 h

-- Witnesses. The name is the role. Products stay outside the proof.

/-- Tasks: one sqlite file here, and a copy on a removable replica. -/
def exTasks : Artifact where
  name := "tasks"
  encoding := .sqlite
  replicas := [.here, .replica]

/-- Passwords: a file, plus a copy the server cannot rewrite. -/
def exPasswords : Artifact where
  name := "passwords"
  encoding := .file
  replicas := [.here, .replica, .offbox]

/-- Server-only vault. Dies with that replica, and needs its daemon to read. -/
def exVaultOnly : Artifact where
  name := "vault-server"
  encoding := .opaqueServer
  replicas := [.replica]

theorem exTasks_readable : ReadableWithoutDaemon exTasks.encoding := by
  decide

theorem exPasswords_readable : ReadableWithoutDaemon exPasswords.encoding := by
  decide

theorem exVaultOnly_not_readable : ¬ ReadableWithoutDaemon exVaultOnly.encoding := by
  intro h
  simp [ReadableWithoutDaemon, exVaultOnly] at h
  rcases h with h | h | h <;> cases h

theorem exTasks_survives_laptop : exTasks.survives .here :=
  other_replica_survives exTasks .here .replica (by decide) (by decide)

theorem exPasswords_survives_server : exPasswords.survives .replica :=
  other_replica_survives exPasswords .replica .offbox (by decide) (by decide)

theorem exVaultOnly_dies_with_server : ¬ exVaultOnly.survives .replica :=
  sole_replica_dies exVaultOnly .replica rfl

/-- Local filter: the laptop both acts and decides. -/
def gateLocal : Gate where
  decidedAt := .here
  actedAt := .here
  openerAt := .here

/-- Off-box filter, but the key that opens it is on the laptop. -/
def gateSameKey : Gate where
  decidedAt := .offbox
  actedAt := .here
  openerAt := .here

/-- Off-box filter, opener on another device. -/
def gateSeparate : Gate where
  decidedAt := .offbox
  actedAt := .here
  openerAt := .replica

theorem gateLocal_fails : ¬ gateLocal.holds :=
  colocated_not_boundary gateLocal rfl

theorem gateSameKey_fails : ¬ gateSameKey.holds :=
  opener_on_actor_not_gate gateSameKey rfl

theorem gateSeparate_holds : gateSeparate.holds := by
  constructor <;> decide

-- ====================================================================
-- §7. FIREWALL
-- From Syntra-Labs/test-gov (ConstitutionalSEF). Kept:
--   one named deficiency per realization, and no realization unless the
--   invariant holds.
-- Left there on purpose: the C++ runtime, protobuf contract, PromQL
-- stream, and the GitHub workflow. Those are witnesses of applyDelta,
-- the schema, and O_Observe, not further axioms.
-- The "exactly one issue" rule is the single `deficiency` field.
-- ====================================================================

/-- A candidate is realized only with a holding gate, one named deficiency,
    and a proof of the invariant. Absence of a Realization is the block. -/
structure Realization {α : Type} (P : α → Prop) where
  gate       : Gate
  gateHolds  : gate.holds
  deficiency : String
  named      : deficiency ≠ ""
  candidate  : α
  invariant  : P candidate

theorem realization_not_colocated {α : Type} {P : α → Prop}
    (r : Realization P) (h : r.gate.decidedAt = r.gate.actedAt) : False :=
  colocated_not_boundary r.gate h r.gateHolds

theorem realization_not_same_key {α : Type} {P : α → Prop}
    (r : Realization P) (h : r.gate.openerAt = r.gate.actedAt) : False :=
  opener_on_actor_not_gate r.gate h r.gateHolds

theorem realization_needs_invariant {α : Type} {P : α → Prop}
    (r : Realization P) {c : α} (hc : r.candidate = c) (h : ¬ P c) : False := by
  apply h
  rw [← hc]
  exact r.invariant

/-- Tasks file, admitted only through the off-box gate. -/
def exTasksOk : Realization (fun a : Artifact => ReadableWithoutDaemon a.encoding) where
  gate := gateSeparate
  gateHolds := gateSeparate_holds
  deficiency := "tasks"
  named := by decide
  candidate := exTasks
  invariant := exTasks_readable

end Semioverse
