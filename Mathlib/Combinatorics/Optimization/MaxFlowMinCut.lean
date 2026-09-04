/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.LeastGreatest
public import Mathlib.Logic.Relation
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

/-!

# Single-commodity max-flow–min-cut theorem (weak + strong duality)

A *flow network* is a finite set of vertices with a source `s`, a sink `t`, and a *capacity*
`cap u v` on each ordered pair of vertices. A *flow* routes material from `s` to `t` obeying two
rules: it never exceeds capacity on any edge, and at every *internal* vertex whatever flows in
also flows out (conservation). The *value* of a flow is the net amount leaving the source. A
*cut* is a way of splitting the vertices into a source side `S` (containing `s`) and a sink side
`Sᶜ` (containing `t`); its *capacity* is the total capacity of edges crossing from `S` to `Sᶜ`.

The classical **max-flow–min-cut theorem** says: the largest achievable flow value equals the
smallest cut capacity. Capacities and flows here are integers (`ℤ`), which is exactly the case
relevant to combinatorial applications and makes existence of a maximum flow clean: the
achievable-value set is a nonempty subset of `ℤ` bounded above (by a cut capacity, via weak
duality), and `Int.exists_greatest_of_bdd` extracts a greatest attained value with no
completeness/compactness and no Ford–Fulkerson termination argument.

## Main definitions

* `MaxFlowMinCut.Network`: a flow network — a non-negative capacity on each ordered pair of
  vertices, with a distinguished source and sink.
* `MaxFlowMinCut.Network.IsFlow`: a flow (non-negative, capacity-respecting, conservative).
* `MaxFlowMinCut.Network.flowValue`: the value of a flow (net out-flow of the source).
* `MaxFlowMinCut.Network.IsCut`: an `s`–`t` cut (a vertex set containing `s` but not `t`).
* `MaxFlowMinCut.Network.cutCapacity`: the capacity of a cut.
* `MaxFlowMinCut.Network.residual`, `MaxFlowMinCut.Network.reachSet`: the residual network and the
  set of vertices residual-reachable from the source (the augmenting-path machinery).

## Main results

* `MaxFlowMinCut.Network.flowValue_le_cutCapacity`: **weak duality**, the value of any flow is at
  most the capacity of any cut.
* `MaxFlowMinCut.Network.exists_maxFlow`: a maximum flow exists (attained).
* `MaxFlowMinCut.Network.maxFlow_eq_minCut`: **strong duality** — there exist a maximum flow `f`
  and a minimum cut `S` with `flowValue f = cutCapacity S`.

## Implementation notes

Mathlib does not currently contain a network-flow / max-flow / min-cut / Menger development
(`Mathlib/Combinatorics/SimpleGraph/Connectivity/EdgeConnectivity.lean` defines a
`k`-edge-connectivity predicate but proves no min-cut = max-flow theorem, and Menger's theorem is
listed in `docs/1000.yaml` without a `decl:` field), so this file builds the `Network` model from
scratch. The augmenting-path crux (a maximum flow's residual-reachable set is a saturating cut)
pushes **one whole unit** of flow along a simple positive-residual path: over `ℤ`,
`0 < residual ↔ 1 ≤ residual`, so a unit always fits and no `min`/`Finset.min'` bookkeeping is
needed.

## References

* [L. R. Ford, D. R. Fulkerson, *Maximal flow through a network*][ford1956]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, C. Stein,
  *Introduction to Algorithms*][cormen2009] (Chapter 26)

-/

@[expose] public section

namespace MaxFlowMinCut

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A **flow network**: a capacity `cap u v ≥ 0` on each ordered pair of vertices, together with
a distinguished source `s` and sink `t`, `s ≠ t`. -/
structure Network (V : Type*) [Fintype V] [DecidableEq V] where
  /-- Capacity of the ordered edge `u → v`. -/
  cap : V → V → ℤ
  /-- Capacities are non-negative. -/
  cap_nonneg : ∀ u v, 0 ≤ cap u v
  /-- The source vertex. -/
  s : V
  /-- The sink vertex. -/
  t : V
  /-- Source and sink are distinct. -/
  s_ne_t : s ≠ t

namespace Network

variable (N : Network V)

/-- `f` is a **flow** on the network `N` when it is non-negative, respects capacities, and
conserves material at every vertex other than the source and the sink (net out-flow zero, i.e.
`∑ w, f v w = ∑ w, f w v`). -/
structure IsFlow (f : V → V → ℤ) : Prop where
  /-- Flows are non-negative on every edge. -/
  nonneg : ∀ u v, 0 ≤ f u v
  /-- Flows never exceed capacity. -/
  le_cap : ∀ u v, f u v ≤ N.cap u v
  /-- Conservation at internal vertices: outflow equals inflow. -/
  conservation : ∀ v, v ≠ N.s → v ≠ N.t → ∑ w, f v w = ∑ w, f w v

/-- The **value** of a flow: the net amount leaving the source, `(outflow of s) − (inflow to s)`. -/
def flowValue (f : V → V → ℤ) : ℤ := (∑ w, f N.s w) - (∑ w, f w N.s)

/-- `S` is a **cut** (an `s`–`t` cut) when the source is inside `S` and the sink is outside. -/
structure IsCut (S : Finset V) : Prop where
  /-- The source lies on the `S` side. -/
  s_mem : N.s ∈ S
  /-- The sink lies on the complement side. -/
  t_not_mem : N.t ∉ S

/-- The **capacity of a cut** `S`: the total capacity of edges crossing from `S` to its
complement `Sᶜ`. -/
def cutCapacity (S : Finset V) : ℤ := ∑ u ∈ S, ∑ v ∈ Sᶜ, N.cap u v

/-- The **net flow across a cut** `S`: forward flow (`S → Sᶜ`) minus backward flow (`Sᶜ → S`).
(The network `N` is carried only so this reads with dot-notation `N.flowAcross`; the value does
not depend on `N`.) -/
def flowAcross (_N : Network V) (f : V → V → ℤ) (S : Finset V) : ℤ :=
    (∑ u ∈ S, ∑ v ∈ Sᶜ, f u v) - (∑ u ∈ S, ∑ v ∈ Sᶜ, f v u)

/-!
### Key lemma: net flow across a cut equals the flow value

For any `s`–`t` cut `S`, the net flow crossing `S` equals the value of the flow. Intuitively:
summing the "net out-flow" of every vertex in `S`, the internal vertices contribute `0` (by
conservation) and `t ∉ S`, so only `s` survives, giving `flowValue`. The internal `S`–`S`
edges cancel in pairs.
-/

/-- For a vertex `v` inside the cut `S`, its total outflow `∑ w, f v w` splits over the whole
vertex set as flow to `S` plus flow to `Sᶜ`; likewise its inflow. This is just `∑` over `univ`
split as `S ∪ Sᶜ`. -/
private lemma sum_split (f : V → V → ℤ) (v : V) (S : Finset V) :
    ∑ w, f v w = (∑ w ∈ S, f v w) + ∑ w ∈ Sᶜ, f v w := by
  rw [← Finset.sum_add_sum_compl S (fun w => f v w)]

/-- **Flow across any cut equals the flow value.** `flowValue f = flowAcross f S` for every
`s`–`t` cut `S`. Proved by summing net out-flow over `S`: internal vertices vanish by
conservation, `t ∉ S`, and the `S`–`S` block cancels. -/
theorem flowValue_eq_flow_across_cut {S : Finset V} (hS : N.IsCut S)
    {f : V → V → ℤ} (hf : N.IsFlow f) :
    N.flowValue f = N.flowAcross f S := by
  -- net out-flow of a vertex v
  set g : V → ℤ := fun v => (∑ w, f v w) - (∑ w, f w v) with hg
  -- Sum of net out-flow over S. Every internal vertex contributes 0; t ∉ S; only s remains.
  have hsum : ∑ v ∈ S, g v = N.flowValue f := by
    have hsingle : ∑ v ∈ S, g v = g N.s := by
      apply Finset.sum_eq_single_of_mem N.s hS.s_mem
      intro v hvS hvs
      have hvt : v ≠ N.t := by rintro rfl; exact hS.t_not_mem hvS
      simp only [hg, hf.conservation v hvs hvt, sub_self]
    rw [hsingle, hg]; rfl
  -- Now expand ∑ v∈S, g v via the S / Sᶜ split and cancel the S–S block.
  have hexpand : ∑ v ∈ S, g v = N.flowAcross f S := by
    have hstep : ∀ v ∈ S, g v =
        ((∑ w ∈ S, f v w) + ∑ w ∈ Sᶜ, f v w) - ((∑ w ∈ S, f w v) + ∑ w ∈ Sᶜ, f w v) := by
      intro v _
      rw [hg]; simp only []
      rw [sum_split f v S]
      congr 1
      rw [← Finset.sum_add_sum_compl S (fun w => f w v)]
    rw [Finset.sum_congr rfl hstep]
    -- distribute the sum over S
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    -- The two S–S double sums are ∑ v∈S ∑ w∈S f v w and ∑ v∈S ∑ w∈S f w v; equal by sum_comm.
    have hcancel : (∑ v ∈ S, ∑ w ∈ S, f v w) = ∑ v ∈ S, ∑ w ∈ S, f w v := by
      rw [Finset.sum_comm]
    unfold Network.flowAcross
    -- rearrange: (A_SS + A_SSc) - (B_SS + B_SSc) = A_SSc - B_SSc  since A_SS = B_SS
    rw [hcancel]
    ring
  rw [← hsum, hexpand]

/-!
### Weak duality

The forward flow across a cut is bounded above by the cut capacity (each edge `f u v ≤ cap u v`),
and the backward flow is non-negative, so the *net* flow across is `≤ cutCapacity`. Combined
with the previous theorem, `flowValue f ≤ cutCapacity S`.
-/

/-- **Weak duality.** For any flow `f` and any `s`–`t` cut `S`, `flowValue f ≤ cutCapacity S`.
This is the tractable half of max-flow–min-cut. -/
theorem flowValue_le_cutCapacity {S : Finset V} (hS : N.IsCut S)
    {f : V → V → ℤ} (hf : N.IsFlow f) :
    N.flowValue f ≤ N.cutCapacity S := by
  rw [flowValue_eq_flow_across_cut N hS hf]
  unfold Network.flowAcross Network.cutCapacity
  -- flowAcross = forward − backward ≤ forward ≤ cutCapacity
  have hback_nonneg : 0 ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, f v u := by
    apply Finset.sum_nonneg; intro u _
    apply Finset.sum_nonneg; intro v _
    exact hf.nonneg v u
  have hforward_le : (∑ u ∈ S, ∑ v ∈ Sᶜ, f u v) ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, N.cap u v := by
    apply Finset.sum_le_sum; intro u _
    apply Finset.sum_le_sum; intro v _
    exact hf.le_cap u v
  linarith

/-- Corollary: the value of any flow is at most the capacity of every cut, so in particular it is
at most the *minimum* cut capacity (once a min cut is exhibited). Restated here as: any flow
value is a lower bound candidate that the min cut dominates. -/
theorem flowValue_le_of_forall_cut {f : V → V → ℤ} (hf : N.IsFlow f)
    {c : ℤ} {S : Finset V} (hS : N.IsCut S) (hc : N.cutCapacity S = c) :
    N.flowValue f ≤ c := by
  rw [← hc]; exact flowValue_le_cutCapacity N hS hf

/-!
### Existence of a maximum flow

Integrality makes attainment clean. The achievable-value set `{ N.flowValue f | N.IsFlow f }`
is a set of integers that is (a) nonempty — the zero flow is a flow of value `0`, and
(b) bounded above — by the capacity of the cut `{N.s}` (weak duality). `Int.exists_greatest_of_bdd`
then hands back a greatest achievable value, attained by an actual flow: the maximum flow.
No Ford–Fulkerson termination argument is needed.
-/

/-- The **zero flow** `fun _ _ => 0` is a genuine flow (existence seed): non-negative, under any
non-negative capacity, and trivially conservative (both sides `0`). -/
theorem zeroFlow_isFlow : N.IsFlow (fun _ _ => 0) where
  nonneg := by intro u v; exact le_refl 0
  le_cap := by intro u v; exact N.cap_nonneg u v
  conservation := by intro v _ _; simp

/-- The singleton `{N.s}` is an `s`–`t` cut (source inside, sink outside since `s ≠ t`). This is
the fixed cut whose capacity bounds every flow value from above. -/
theorem singleton_source_isCut : N.IsCut {N.s} where
  s_mem := Finset.mem_singleton_self N.s
  t_not_mem := by
    simp only [Finset.mem_singleton]
    exact fun h => N.s_ne_t h.symm

/-- **Maximum-flow existence.** There is a flow `f` whose value is `≥` that of every other
flow. Proof: the set of achievable values is nonempty (zero flow, value `0`) and bounded above
(by `cutCapacity {N.s}`, weak duality); `Int.exists_greatest_of_bdd` extracts a greatest attained
value, and any flow realizing it is a maximum flow. -/
theorem exists_maxFlow :
    ∃ f, N.IsFlow f ∧ ∀ g, N.IsFlow g → N.flowValue g ≤ N.flowValue f := by
  -- The predicate "v is an achievable flow value".
  set P : ℤ → Prop := fun v => ∃ f, N.IsFlow f ∧ N.flowValue f = v with hP
  -- (a) nonempty: the zero flow achieves value flowValue 0 = 0.
  have hne : ∃ v, P v := ⟨N.flowValue (fun _ _ => 0), (fun _ _ => 0), N.zeroFlow_isFlow, rfl⟩
  -- (b) bounded above: every achievable value ≤ cutCapacity {N.s}.
  have hbdd : ∃ b, ∀ v, P v → v ≤ b := by
    refine ⟨N.cutCapacity {N.s}, ?_⟩
    rintro v ⟨f, hf, rfl⟩
    exact N.flowValue_le_cutCapacity N.singleton_source_isCut hf
  -- greatest achievable value v*, attained by some flow.
  obtain ⟨vstar, hvstar_P, hvstar_max⟩ := Int.exists_greatest_of_bdd hbdd hne
  obtain ⟨fstar, hfstar, hfstar_val⟩ := hvstar_P
  refine ⟨fstar, hfstar, ?_⟩
  intro g hg
  rw [hfstar_val]
  exact hvstar_max (N.flowValue g) ⟨g, hg, rfl⟩

/-!
### Saturation ⇒ tightness, and the conditional strong-duality package

A flow **saturates** a cut `S` when every forward crossing edge is at capacity and every backward
crossing edge carries no flow. Saturation forces `flowValue f = cutCapacity S` (a direct corollary
of `flowValue_eq_flow_across_cut`). Combined with weak duality, any *saturating pair* `(f, S)` is
automatically a max-flow / min-cut pair with equal value — the strong-duality conclusion,
conditional on the existence of such a pair (whose unconditional construction from a max flow's
residual-reachable cut follows below).
-/

/-- **Saturation ⇒ tightness.** If a flow `f` saturates the cut `S` — forward crossing
edges at capacity, backward crossing edges zero — then `flowValue f = cutCapacity S`. Immediate
from `flowValue_eq_flow_across_cut`: the backward sum vanishes and the forward sum is exactly the
cut capacity term by term. -/
theorem flowValue_eq_cutCapacity_of_saturated {S : Finset V} (hS : N.IsCut S)
    {f : V → V → ℤ} (hf : N.IsFlow f)
    (hfwd : ∀ u ∈ S, ∀ v ∈ Sᶜ, f u v = N.cap u v)
    (hbwd : ∀ u ∈ S, ∀ v ∈ Sᶜ, f v u = 0) :
    N.flowValue f = N.cutCapacity S := by
  rw [flowValue_eq_flow_across_cut N hS hf]
  unfold Network.flowAcross Network.cutCapacity
  have hb : (∑ u ∈ S, ∑ v ∈ Sᶜ, f v u) = 0 := by
    rw [Finset.sum_eq_zero]; intro u hu
    rw [Finset.sum_eq_zero]; intro v hv
    exact hbwd u hu v hv
  have hfw : (∑ u ∈ S, ∑ v ∈ Sᶜ, f u v) = ∑ u ∈ S, ∑ v ∈ Sᶜ, N.cap u v := by
    apply Finset.sum_congr rfl; intro u hu
    apply Finset.sum_congr rfl; intro v hv
    exact hfwd u hu v hv
  rw [hb, hfw, sub_zero]

/-- **Strong duality, conditional on a saturating pair.** If some flow `f` saturates some
cut `S`, then `flowValue f = cutCapacity S`, `f` is a maximum flow, and `S` is a minimum cut. So
the maximum flow value equals the minimum cut capacity. (The saturating pair is supplied
unconditionally below: the residual-reachable cut of a maximum flow. Given that, this is the
packaged theorem.) -/
theorem strongDuality_of_saturating {S : Finset V} (hS : N.IsCut S)
    {f : V → V → ℤ} (hf : N.IsFlow f)
    (hfwd : ∀ u ∈ S, ∀ v ∈ Sᶜ, f u v = N.cap u v)
    (hbwd : ∀ u ∈ S, ∀ v ∈ Sᶜ, f v u = 0) :
    N.flowValue f = N.cutCapacity S ∧
      (∀ g, N.IsFlow g → N.flowValue g ≤ N.flowValue f) ∧
      (∀ T, N.IsCut T → N.cutCapacity S ≤ N.cutCapacity T) := by
  have heq : N.flowValue f = N.cutCapacity S :=
    N.flowValue_eq_cutCapacity_of_saturated hS hf hfwd hbwd
  refine ⟨heq, ?_, ?_⟩
  · -- f is a max flow: any g has value ≤ cutCapacity S = flowValue f.
    intro g hg
    rw [heq]
    exact N.flowValue_le_cutCapacity hS hg
  · -- S is a min cut: any cut T has capacity ≥ flowValue f = cutCapacity S.
    intro T hT
    rw [← heq]
    exact N.flowValue_le_cutCapacity hT hf

/-!
### Residual reachability and the augmenting-path argument

Strong duality reduces to ONE unconditional lemma: *a maximum flow's residual-reachable set is a
saturating cut*.

`residual f u v = cap u v − f u v + f v u` is the spare capacity of the edge `u → v` in the
residual network: room `cap − f ≥ 0` to push more forward, plus the backward flow `f v u ≥ 0`
that could be cancelled. It is always `≥ 0`. `reachSet f` is the set of vertices reachable from
the source `s` along positive-residual edges (`Relation.ReflTransGen`).

The proof has three parts:
* **PART A (saturation half).** If `u` is reachable and `v` is not, the crossing residual must be
  `0` (else closure of reachability would pull `v` in), forcing `f u v = cap u v` and `f v u = 0`.
* **PART B (`reachSet f` is a cut).** `s ∈ reachSet f` by reflexivity; `t ∉ reachSet f` from
  Part C; so `IsCut (reachSet f)`.
* **PART C (crux).** For a *maximum* flow, `t ∉ reachSet f`: otherwise a positive-residual path
  `s ⇝ t` lets us push `δ = 1 > 0` along it, producing a flow of strictly larger value,
  contradicting maximality.
-/

/-- **Residual capacity** of the ordered edge `u → v` under flow `f`: spare forward capacity
`cap u v − f u v` plus the backward flow `f v u` that could be cancelled. Always `≥ 0` for a
flow. Positive residual means the edge can carry more net flow toward `v`. -/
def residual (f : V → V → ℤ) (u v : V) : ℤ := N.cap u v - f u v + f v u

/-- The residual is non-negative for any flow: `cap − f ≥ 0` (capacity bound) and `f v u ≥ 0`. -/
theorem residual_nonneg {f : V → V → ℤ} (hf : N.IsFlow f) (u v : V) :
    0 ≤ N.residual f u v := by
  unfold Network.residual
  have h1 : 0 ≤ N.cap u v - f u v := by linarith [hf.le_cap u v]
  have h2 : 0 ≤ f v u := hf.nonneg v u
  linarith

open scoped Classical in
/-- The **residual-reachable set**: all vertices reachable from the source `N.s` along edges of
strictly positive residual (reflexive–transitive closure). `noncomputable` — membership is decided
classically; that is fine, the set is a genuine `Finset` and we only reason about it. -/
noncomputable def reachSet (f : V → V → ℤ) : Finset V :=
  Finset.univ.filter (fun v => Relation.ReflTransGen (fun x y => 0 < N.residual f x y) N.s v)

open scoped Classical in
/-- Membership in `reachSet` unfolds to reachability from the source. -/
theorem mem_reachSet {f : V → V → ℤ} {v : V} :
    v ∈ N.reachSet f ↔ Relation.ReflTransGen (fun x y => 0 < N.residual f x y) N.s v := by
  unfold Network.reachSet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ v, h⟩⟩

/-- The source is always residual-reachable (reflexivity). -/
theorem s_mem_reachSet (f : V → V → ℤ) : N.s ∈ N.reachSet f :=
  N.mem_reachSet.mpr Relation.ReflTransGen.refl

/-- **Closure of reachability.** If `u` is reachable and the edge `u → v` has positive residual,
then `v` is reachable. (This is `ReflTransGen.tail`.) -/
theorem reachSet_closed {f : V → V → ℤ} {u v : V}
    (hu : u ∈ N.reachSet f) (huv : 0 < N.residual f u v) : v ∈ N.reachSet f := by
  rw [mem_reachSet] at hu ⊢
  exact hu.tail huv

/-!
#### PART A — the saturation half (unconditional, pure arithmetic + closure)
-/

/-- **PART A (forward saturation).** On a crossing edge of the reachable set — `u` reachable,
`v` not — the forward flow is at capacity: `f u v = cap u v`. Because a positive residual would
force `v ∈ reachSet f` by closure (contradiction), so `residual f u v ≤ 0`; but it is `≥ 0`, hence
`= 0`; and `residual = (cap − f) + (f v u)` is a sum of two non-negatives, so each is `0`. -/
theorem reachSet_forward_saturated {f : V → V → ℤ} (hf : N.IsFlow f) {u v : V}
    (hu : u ∈ N.reachSet f) (hv : v ∉ N.reachSet f) :
    f u v = N.cap u v := by
  have hle : ¬ (0 < N.residual f u v) := fun hpos => hv (N.reachSet_closed hu hpos)
  have hnn : 0 ≤ N.residual f u v := N.residual_nonneg hf u v
  have hzero : N.residual f u v = 0 := le_antisymm (not_lt.mp hle) hnn
  -- residual = (cap - f) + (f v u), both summands ≥ 0 ⇒ each is 0
  have hcap : 0 ≤ N.cap u v - f u v := by linarith [hf.le_cap u v]
  have hbwd : 0 ≤ f v u := hf.nonneg v u
  unfold Network.residual at hzero
  linarith

/-- **PART A (backward zero).** On the same crossing edge, the backward flow vanishes:
`f v u = 0`. Same argument: `residual f u v = 0` and both non-negative summands must vanish. -/
theorem reachSet_backward_zero {f : V → V → ℤ} (hf : N.IsFlow f) {u v : V}
    (hu : u ∈ N.reachSet f) (hv : v ∉ N.reachSet f) :
    f v u = 0 := by
  have hle : ¬ (0 < N.residual f u v) := fun hpos => hv (N.reachSet_closed hu hpos)
  have hnn : 0 ≤ N.residual f u v := N.residual_nonneg hf u v
  have hzero : N.residual f u v = 0 := le_antisymm (not_lt.mp hle) hnn
  have hcap : 0 ≤ N.cap u v - f u v := by linarith [hf.le_cap u v]
  have hbwd : 0 ≤ f v u := hf.nonneg v u
  unfold Network.residual at hzero
  linarith

/-!
#### PART C — the augmenting-path argument (the crux)

We show that for a **maximum** flow `f`, the sink is *not* residual-reachable: `N.t ∉ reachSet f`.
Suppose it were. Then there is a positive-residual path `s ⇝ t`. Since capacities and flows are
integers, positive residual means residual `≥ 1`, so we can push **one whole unit** along the
path. Pushing a unit along an edge `(a, b)` — cancelling a unit of backward flow if any is
present, otherwise adding a unit of forward flow — keeps `0 ≤ f' ≤ cap` (the residual `≥ 1`
guarantees room) and shifts the *net out-flow* by `+1` at `a` and `−1` at `b`. Composing these
pushes along a **simple** (`Nodup`) path from `s` to `t`, every internal vertex gains `+1` on its
in-edge and `−1` on its out-edge (net `0`, conservation preserved), while `s` gains `+1` and `t`
loses `1`. The result is a genuine flow of value `flowValue f + 1 > flowValue f`, contradicting
maximality. The simple path is extracted from the `ReflTransGen` reachability witness by a
duplicate-removing induction (`aug_nodup_path`), and the flow is built by an induction over that
path (`augment_exists`) using the single-edge push `pushEdge`.
-/

/-- **Single-edge unit push.** Push one unit of net flow from `a` to `b` in `g`: cancel a unit of
backward flow `g b a` if present (`g b a ≥ 1`), otherwise add a unit of forward flow `g a b`. Only
the entries `(a, b)` and `(b, a)` are ever touched. -/
def pushEdge (g : V → V → ℤ) (a b : V) : V → V → ℤ :=
  fun u v =>
    if g b a ≥ 1 then
      if u = b ∧ v = a then g b a - 1 else g u v
    else
      if u = a ∧ v = b then g a b + 1 else g u v

/-- Net out-flow of a vertex `x` under `g`: `(∑ w, g x w) − (∑ w, g w x)`. -/
def netOut (g : V → V → ℤ) (x : V) : ℤ := (∑ w, g x w) - (∑ w, g w x)

/-- `pushEdge` raises the net out-flow at the source endpoint `a` by exactly `1` (`a ≠ b`). -/
theorem push_neta (g : V → V → ℤ) (a b : V) (hab : a ≠ b) :
    (∑ w, pushEdge g a b a w) - (∑ w, pushEdge g a b w a)
      = (∑ w, g a w) - (∑ w, g w a) + 1 := by
  unfold pushEdge
  split_ifs with h
  · have hrow : (∑ w, (if a = b ∧ w = a then g b a - 1 else g a w)) = ∑ w, g a w := by
      apply Finset.sum_congr rfl; intro w _; rw [ite_eq_right]; rintro ⟨rfl, _⟩; exact hab rfl
    have hcol : (∑ w, (if w = b ∧ a = a then g b a - 1 else g w a)) = (∑ w, g w a) - 1 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b)]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b)]
      have hb : (if b = b ∧ a = a then g b a - 1 else g b a) = g b a - 1 := by simp
      rw [hb]
      have herase : (∑ w ∈ univ.erase b, (if w = b ∧ a = a then g b a - 1 else g w a))
          = ∑ w ∈ univ.erase b, g w a := by
        apply Finset.sum_congr rfl; intro w hw
        rw [ite_eq_right]; rintro ⟨rfl, _⟩; exact (Finset.mem_erase.mp hw).1 rfl
      rw [herase]; ring
    rw [hrow, hcol]; ring
  · have hrow : (∑ w, (if a = a ∧ w = b then g a b + 1 else g a w)) = (∑ w, g a w) + 1 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b)]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ b)]
      have hb : (if a = a ∧ b = b then g a b + 1 else g a b) = g a b + 1 := by simp
      rw [hb]
      have herase : (∑ w ∈ univ.erase b, (if a = a ∧ w = b then g a b + 1 else g a w))
          = ∑ w ∈ univ.erase b, g a w := by
        apply Finset.sum_congr rfl; intro w hw
        rw [ite_eq_right]; rintro ⟨_, rfl⟩; exact (Finset.mem_erase.mp hw).1 rfl
      rw [herase]; ring
    have hcol : (∑ w, (if w = a ∧ a = b then g a b + 1 else g w a)) = ∑ w, g w a := by
      apply Finset.sum_congr rfl; intro w _; rw [ite_eq_right]; rintro ⟨_, hb⟩; exact hab hb
    rw [hrow, hcol]; ring

/-- `pushEdge` lowers the net out-flow at the sink endpoint `b` by exactly `1` (`a ≠ b`). -/
theorem push_netb (g : V → V → ℤ) (a b : V) (hab : a ≠ b) :
    (∑ w, pushEdge g a b b w) - (∑ w, pushEdge g a b w b)
      = (∑ w, g b w) - (∑ w, g w b) - 1 := by
  unfold pushEdge
  split_ifs with h
  · have hrow : (∑ w, (if b = b ∧ w = a then g b a - 1 else g b w)) = (∑ w, g b w) - 1 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
      have ha : (if b = b ∧ a = a then g b a - 1 else g b a) = g b a - 1 := by simp
      rw [ha]
      have herase : (∑ w ∈ univ.erase a, (if b = b ∧ w = a then g b a - 1 else g b w))
          = ∑ w ∈ univ.erase a, g b w := by
        apply Finset.sum_congr rfl; intro w hw
        rw [ite_eq_right]; rintro ⟨_, rfl⟩; exact (Finset.mem_erase.mp hw).1 rfl
      rw [herase]; ring
    have hcol : (∑ w, (if w = b ∧ b = a then g b a - 1 else g w b)) = ∑ w, g w b := by
      apply Finset.sum_congr rfl; intro w _; rw [ite_eq_right]; rintro ⟨_, hb⟩; exact hab hb.symm
    rw [hrow, hcol]; ring
  · have hrow : (∑ w, (if b = a ∧ w = b then g a b + 1 else g b w)) = ∑ w, g b w := by
      apply Finset.sum_congr rfl; intro w _; rw [ite_eq_right]; rintro ⟨hb, _⟩; exact hab hb.symm
    have hcol : (∑ w, (if w = a ∧ b = b then g a b + 1 else g w b)) = (∑ w, g w b) + 1 := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
      have ha : (if a = a ∧ b = b then g a b + 1 else g a b) = g a b + 1 := by simp
      rw [ha]
      have herase : (∑ w ∈ univ.erase a, (if w = a ∧ b = b then g a b + 1 else g w b))
          = ∑ w ∈ univ.erase a, g w b := by
        apply Finset.sum_congr rfl; intro w hw
        rw [ite_eq_right]; rintro ⟨rfl, _⟩; exact (Finset.mem_erase.mp hw).1 rfl
      rw [herase]; ring
    rw [hrow, hcol]; ring

/-- `pushEdge` leaves the net out-flow at every *other* vertex unchanged (`a ≠ b`, `x ∉ {a,b}`). -/
theorem push_netother (g : V → V → ℤ) (a b : V) (hab : a ≠ b) (x : V) (hxa : x ≠ a) (hxb : x ≠ b) :
    (∑ w, pushEdge g a b x w) - (∑ w, pushEdge g a b w x)
      = (∑ w, g x w) - (∑ w, g w x) := by
  unfold pushEdge
  split_ifs with h
  · congr 1
    · apply Finset.sum_congr rfl; intro w _; rw [ite_eq_right]; rintro ⟨rfl, _⟩; exact hxb rfl
    · apply Finset.sum_congr rfl; intro w _; rw [ite_eq_right]; rintro ⟨_, rfl⟩; exact hxa rfl
  · congr 1
    · apply Finset.sum_congr rfl; intro w _; rw [ite_eq_right]; rintro ⟨rfl, _⟩; exact hxa rfl
    · apply Finset.sum_congr rfl; intro w _; rw [ite_eq_right]; rintro ⟨_, rfl⟩; exact hxb rfl

omit [Fintype V] in
/-- `pushEdge` preserves non-negativity of the flow. -/
theorem push_nonneg (g : V → V → ℤ) (a b : V)
    (hg : ∀ u v, 0 ≤ g u v) (u v : V) : 0 ≤ pushEdge g a b u v := by
  unfold pushEdge
  split_ifs with h h1 h2
  · omega
  · exact hg u v
  · have := hg a b; omega
  · exact hg u v

omit [Fintype V] in
/-- `pushEdge` preserves the capacity bound, given the edge has residual `≥ 1`. -/
theorem push_lecap (cap g : V → V → ℤ) (a b : V)
    (hle : ∀ u v, g u v ≤ cap u v) (hres : 1 ≤ cap a b - g a b + g b a)
    (u v : V) : pushEdge g a b u v ≤ cap u v := by
  unfold pushEdge
  split_ifs with h h1 h2
  · obtain ⟨rfl, rfl⟩ := h1; have := hle u v; omega
  · exact hle u v
  · obtain ⟨rfl, rfl⟩ := h2; omega
  · exact hle u v

omit [Fintype V] in
/-- `pushEdge` changes no entry other than `(a, b)` and `(b, a)`. -/
theorem push_eq_of (g : V → V → ℤ) (a b u v : V)
    (h : ¬(u = a ∧ v = b)) (h2 : ¬(u = b ∧ v = a)) :
    pushEdge g a b u v = g u v := by
  unfold pushEdge
  split_ifs <;> rfl

omit [Fintype V] in
/-- **Simple-path extraction from residual reachability.** From a `ReflTransGen` reachability
witness we extract a duplicate-free (`Nodup`) vertex list `p` with `p.head? = some a`,
`p.getLast? = some b`, and consecutive edges chained by `r`. Duplicates are removed by truncating
to the suffix at the first re-encounter. -/
theorem aug_nodup_path (r : V → V → Prop) (a b : V) (h : Relation.ReflTransGen r a b) :
    ∃ l : List V, l.head? = some a ∧ l.getLast? = some b ∧ l.IsChain r ∧ l.Nodup := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[b], rfl, rfl, List.IsChain.singleton b, List.nodup_singleton b⟩
  | @head x c hxc _ ih =>
    obtain ⟨l, hhead, hlast, hchain, hnodup⟩ := ih
    by_cases hx : x ∈ l
    · obtain ⟨s1, s2, hsplit⟩ := List.append_of_mem hx
      subst hsplit
      refine ⟨x :: s2, rfl, ?_, ?_, ?_⟩
      · rw [← List.getLast?_append_cons s1 x s2]; exact hlast
      · exact List.IsChain.right_of_append hchain
      · exact List.Nodup.of_append_right hnodup
    · refine ⟨x :: l, rfl, ?_, ?_, ?_⟩
      · cases l with
        | nil => simp at hhead
        | cons y t => rw [List.getLast?_cons_cons]; exact hlast
      · refine hchain.cons ?_
        intro y hy
        rw [hhead] at hy
        simp only [Option.mem_some_iff] at hy
        subst hy; exact hxc
      · exact List.nodup_cons.mpr ⟨hx, hnodup⟩

/-- **Augmenting flow existence (core induction).** Given a simple (`Nodup`) positive-residual
path `p` from its head `c` to the global sink `t` (residual measured in the base flow `f`), there
is a flow `g` (`0 ≤ g ≤ cap`) whose net out-flow is `+1` at `c`, `−1` at `t`, unchanged elsewhere,
and which agrees with `f` on every entry touching a vertex off `p`. Built by pushing one unit
along each path edge (`pushEdge`), inducting on `p`. -/
theorem augment_exists (cap f : V → V → ℤ)
    (hnn : ∀ u v, 0 ≤ f u v) (hle : ∀ u v, f u v ≤ cap u v) (t : V) :
    ∀ (p : List V), ∀ c ∈ p.head?, p.getLast? = some t →
      p.IsChain (fun x y => 1 ≤ cap x y - f x y + f y x) → p.Nodup → c ≠ t →
      ∃ g : V → V → ℤ,
        (∀ u v, 0 ≤ g u v) ∧ (∀ u v, g u v ≤ cap u v) ∧
        netOut g c = netOut f c + 1 ∧ netOut g t = netOut f t - 1 ∧
        (∀ x, x ≠ c → x ≠ t → netOut g x = netOut f x) ∧
        (∀ u v, (u ∉ p ∨ v ∉ p) → g u v = f u v) := by
  intro p
  induction p with
  | nil => intro c hc; simp at hc
  | cons a l ih =>
    intro c hc hlast hchain hnodup hct
    rw [List.head?_cons, Option.mem_some_iff] at hc
    subst hc
    cases l with
    | nil => rw [List.getLast?_singleton, Option.some_inj] at hlast; exact absurd hlast hct
    | cons c' rest =>
      have hedge : 1 ≤ cap a c' - f a c' + f c' a := by
        rw [List.isChain_cons] at hchain; exact hchain.1 c' (by simp)
      have htailchain : (c' :: rest).IsChain (fun x y => 1 ≤ cap x y - f x y + f y x) := by
        rw [List.isChain_cons] at hchain; exact hchain.2
      have htailnodup : (c' :: rest).Nodup := (List.nodup_cons.mp hnodup).2
      have hanotin : a ∉ (c' :: rest) := (List.nodup_cons.mp hnodup).1
      have hc'nea : c' ≠ a := fun h => hanotin (h ▸ List.mem_cons_self)
      have htaillast : (c' :: rest).getLast? = some t := by
        rw [List.getLast?_cons_cons] at hlast; exact hlast
      by_cases hc't : c' = t
      · subst hc't
        refine ⟨pushEdge f a c', push_nonneg f a c' hnn, push_lecap cap f a c' hle hedge,
          ?_, ?_, ?_, ?_⟩
        · rw [netOut, netOut]; exact push_neta f a c' (Ne.symm hc'nea)
        · rw [netOut, netOut]; exact push_netb f a c' (Ne.symm hc'nea)
        · intro x hxa hxc'; rw [netOut, netOut]
          exact push_netother f a c' (Ne.symm hc'nea) x hxa hxc'
        · intro u v huv
          apply push_eq_of
          · rintro ⟨rfl, rfl⟩; rcases huv with h | h <;> exact h (by simp)
          · rintro ⟨rfl, rfl⟩; rcases huv with h | h <;> exact h (by simp)
      · obtain ⟨g, hg_nn, hg_le, hg_c', hg_t, hg_other, hg_agree⟩ :=
          ih c' (by simp) htaillast htailchain htailnodup hc't
        have hres_g : 1 ≤ cap a c' - g a c' + g c' a := by
          have h1 : g a c' = f a c' := hg_agree a c' (Or.inl hanotin)
          have h2 : g c' a = f c' a := hg_agree c' a (Or.inr hanotin)
          rw [h1, h2]; exact hedge
        refine ⟨pushEdge g a c', push_nonneg g a c' hg_nn, push_lecap cap g a c' hg_le hres_g,
          ?_, ?_, ?_, ?_⟩
        · rw [netOut, netOut, push_neta g a c' (Ne.symm hc'nea)]
          have := hg_other a (Ne.symm hc'nea) hct
          rw [netOut, netOut] at this; rw [this]
        · rw [netOut, netOut, push_netother g a c' (Ne.symm hc'nea) t (Ne.symm hct) (Ne.symm hc't)]
          rw [netOut, netOut] at hg_t; exact hg_t
        · intro x hxa hxt
          by_cases hxc' : x = c'
          · subst hxc'
            rw [netOut, netOut, push_netb g a x (Ne.symm hc'nea)]
            rw [netOut, netOut] at hg_c'; rw [hg_c']; ring
          · rw [netOut, netOut, push_netother g a c' (Ne.symm hc'nea) x hxa hxc']
            have := hg_other x hxc' hxt
            rw [netOut, netOut] at this; rw [this]
        · intro u v huv
          rw [push_eq_of g a c' u v ?_ ?_]
          · apply hg_agree
            rcases huv with h | h
            · exact Or.inl (fun hu => h (List.mem_cons_of_mem a hu))
            · exact Or.inr (fun hv => h (List.mem_cons_of_mem a hv))
          · rintro ⟨rfl, rfl⟩
            rcases huv with h | h
            · exact h (by simp)
            · exact h (by simp)
          · rintro ⟨rfl, rfl⟩
            rcases huv with h | h
            · exact h (by simp)
            · exact h (by simp)

/-- **PART C (no augmenting path at a maximum).** For a **maximum** flow, the sink is not
residual-reachable: `N.t ∉ reachSet f`. Otherwise a positive-residual `s ⇝ t` path yields (via
`aug_nodup_path` + `augment_exists`) a flow of value `flowValue f + 1`, contradicting maximality. -/
theorem reachSet_t_not_mem {f : V → V → ℤ} (hf : N.IsFlow f)
    (hmax : ∀ g, N.IsFlow g → N.flowValue g ≤ N.flowValue f) :
    N.t ∉ N.reachSet f := by
  intro htmem
  -- reachability witness s ⇝ t along positive residual
  rw [mem_reachSet] at htmem
  -- convert positive-integer residual to `≥ 1`
  have hrel : Relation.ReflTransGen (fun x y => 1 ≤ N.cap x y - f x y + f y x) N.s N.t := by
    revert htmem
    generalize N.t = w
    intro htmem
    induction htmem with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
        refine ih.tail ?_
        unfold Network.residual at hbc; omega
  obtain ⟨p, hhead, hlast, hchain, hnodup⟩ :=
    aug_nodup_path (fun x y => 1 ≤ N.cap x y - f x y + f y x) N.s N.t hrel
  obtain ⟨g, hg_nn, hg_le, hg_s, hg_t, hg_other, _⟩ :=
    augment_exists N.cap f hf.nonneg hf.le_cap N.t p N.s (hhead ▸ rfl) hlast hchain hnodup N.s_ne_t
  -- g is a flow: conservation from netOut unchanged off s,t
  have hg_flow : N.IsFlow g := by
    refine ⟨hg_nn, hg_le, ?_⟩
    intro v hvs hvt
    have := hg_other v hvs hvt
    unfold netOut at this
    -- ∑ g v w - ∑ g w v = ∑ f v w - ∑ f w v; f conserves at v ⇒ so does g
    have hf_cons := hf.conservation v hvs hvt
    -- from `this` : (∑ g v w) - (∑ g w v) = (∑ f v w) - (∑ f w v) = 0
    have : (∑ w, g v w) - (∑ w, g w v) = 0 := by rw [this]; omega
    omega
  -- flowValue g = netOut g s = netOut f s + 1 = flowValue f + 1
  have hval : N.flowValue g = N.flowValue f + 1 := by
    show (∑ w, g N.s w) - (∑ w, g w N.s) = ((∑ w, f N.s w) - (∑ w, f w N.s)) + 1
    have := hg_s; unfold netOut at this; rw [this]
  have := hmax g hg_flow
  omega

/-!
#### The saturating cut and the headline
-/

/-- **The single crux lemma: a maximum flow's residual-reachable set is a saturating cut.**
`reachSet f` is an `s`–`t` cut (source in by reflexivity — Part B — sink out by Part C), and every
forward crossing edge is at capacity with zero backward flow (Part A). -/
theorem maxflow_reachSet_isSaturatingCut {f : V → V → ℤ} (hf : N.IsFlow f)
    (hmax : ∀ g, N.IsFlow g → N.flowValue g ≤ N.flowValue f) :
    N.IsCut (N.reachSet f) ∧
      (∀ u ∈ N.reachSet f, ∀ v ∈ (N.reachSet f)ᶜ, f u v = N.cap u v) ∧
      (∀ u ∈ N.reachSet f, ∀ v ∈ (N.reachSet f)ᶜ, f v u = 0) := by
  have ht : N.t ∉ N.reachSet f := N.reachSet_t_not_mem hf hmax
  refine ⟨⟨N.s_mem_reachSet f, ht⟩, ?_, ?_⟩
  · intro u hu v hv
    rw [Finset.mem_compl] at hv
    exact N.reachSet_forward_saturated hf hu hv
  · intro u hu v hv
    rw [Finset.mem_compl] at hv
    exact N.reachSet_backward_zero hf hu hv

/-- **Max-flow–min-cut (strong duality), unconditional.** There exist a flow `f` and a cut `S`
with `flowValue f = cutCapacity S`, `f` a maximum flow, and `S` a minimum cut. Obtained by taking
`f` from `exists_maxFlow`, `S = reachSet f` the saturating cut of `maxflow_reachSet_isSaturatingCut`,
and packaging with `strongDuality_of_saturating`. -/
theorem maxFlow_eq_minCut :
    ∃ f S, N.IsFlow f ∧ N.IsCut S ∧
      N.flowValue f = N.cutCapacity S ∧
      (∀ g, N.IsFlow g → N.flowValue g ≤ N.flowValue f) ∧
      (∀ T, N.IsCut T → N.cutCapacity S ≤ N.cutCapacity T) := by
  obtain ⟨f, hf, hmax⟩ := N.exists_maxFlow
  obtain ⟨hcut, hfwd, hbwd⟩ := N.maxflow_reachSet_isSaturatingCut hf hmax
  obtain ⟨heq, hmax', hmin⟩ := N.strongDuality_of_saturating hcut hf hfwd hbwd
  exact ⟨f, N.reachSet f, hf, hcut, heq, hmax', hmin⟩

end Network

end MaxFlowMinCut

/-!
## Anti-vacuity witness: a concrete tight instance

A `Fin 4` network `s=0, a=1, b=2, t=3` realizing a bottleneck path `s→a→t`:
`cap 0 1 = 2` and `cap 1 3 = 2`, all other capacities `0`.

We exhibit the flow `f`: `f 0 1 = 2, f 1 3 = 2` (push `2` units along `s→a→t`), value `2`, and
the cut `S = {0,1}` (source side, sink side `{2,3}`). The only edge crossing from `S` to `Sᶜ`
is `1→3` (cap `2`); the others (`0→2, 0→3, 1→2`) have cap `0`. So `cutCapacity S = 2`, matching
`flowValue f = 2`. Weak duality is therefore tight here — `flowValue f = cutCapacity S = 2 > 0`
— so `S` is in fact a minimum cut and `f` a maximum flow, and the framework is nonvacuous with
positive nondegenerate values.
-/

namespace MaxFlowMinCut.Witness

open MaxFlowMinCut Finset

/-- Capacity function of the witness network on `Fin 4` (`s=0`, `t=3`): a bottleneck path
`0→1→3` of capacity `2`. The only edge crossing out of `S = {0,1}` is `1→3` (cap 2), so
`cutCapacity {0,1} = 2`, matching the flow value `2`. -/
def wcap : Fin 4 → Fin 4 → ℤ := fun u v =>
  if u = 0 ∧ v = 1 then 2
  else if u = 1 ∧ v = 3 then 2
  else 0

/-- The witness network. -/
def wNet : Network (Fin 4) where
  cap := wcap
  cap_nonneg := by
    intro u v
    unfold wcap
    split_ifs <;> norm_num
  s := 0
  t := 3
  s_ne_t := by decide

/-- The witness flow: push `2` units along `0 → 1 → 3`. -/
def wflow : Fin 4 → Fin 4 → ℤ := fun u v =>
  if u = 0 ∧ v = 1 then 2
  else if u = 1 ∧ v = 3 then 2
  else 0

/-- The witness flow is a genuine flow on `wNet`. -/
theorem wflow_isFlow : wNet.IsFlow wflow where
  nonneg := by intro u v; unfold wflow; split_ifs <;> norm_num
  le_cap := by
    intro u v; unfold wflow wNet wcap
    fin_cases u <;> fin_cases v <;> simp_all
  conservation := by
    intro v hvs hvt
    simp only [wNet] at hvs hvt
    -- internal vertices are 1 and 2; only 1 carries flow, in=out=2, vertex 2 in=out=0
    fin_cases v <;> simp_all [wflow]

/-- The source side cut `S = {0,1}`. -/
def wcut : Finset (Fin 4) := {0, 1}

/-- `{0,1}` is an `s`–`t` cut for the witness network. -/
theorem wcut_isCut : wNet.IsCut wcut where
  s_mem := by unfold wcut wNet; decide
  t_not_mem := by unfold wcut wNet; decide

/-- The witness flow has value `2` (positive, nondegenerate). -/
theorem wflow_value : wNet.flowValue wflow = 2 := by
  show (∑ w, wflow (0 : Fin 4) w) - (∑ w, wflow w (0 : Fin 4)) = 2
  simp only [Fin.sum_univ_four, wflow, Fin.reduceEq, and_false, false_and,
    and_self, reduceIte]
  norm_num

/-- The witness cut has capacity `2`. -/
theorem wcut_capacity : wNet.cutCapacity wcut = 2 := by
  have hcompl : (wcut : Finset (Fin 4))ᶜ = {2, 3} := by decide
  show (∑ u ∈ wcut, ∑ v ∈ wcutᶜ, wcap u v) = 2
  rw [hcompl]
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  simp only [wcut, Finset.sum_pair h01, Finset.sum_pair h23]
  simp only [wcap, Fin.reduceEq, and_true, and_false, and_self, reduceIte]
  norm_num

/-- **Anti-vacuity, tight instance.** For the witness, weak duality holds with equality and the
common value is positive: `flowValue = cutCapacity = 2`. Hence the framework is nonvacuous and
the weak-duality bound is achievable (this cut is in fact a minimum cut). -/
theorem witness_tight :
    wNet.flowValue wflow = wNet.cutCapacity wcut ∧ 0 < wNet.flowValue wflow := by
  refine ⟨?_, ?_⟩
  · rw [wflow_value, wcut_capacity]
  · rw [wflow_value]; norm_num

/-- Sanity: weak duality (the general theorem) instantiated at the witness gives `2 ≤ 2`. -/
example : wNet.flowValue wflow ≤ wNet.cutCapacity wcut :=
  Network.flowValue_le_cutCapacity wNet wcut_isCut wflow_isFlow

/-- The witness flow **saturates** the witness cut `{0,1}`: every forward crossing edge is at
capacity and every backward crossing edge is zero. The complement is `{2,3}`; the only nonzero
crossing capacity/flow is `1→3 = 2`. -/
theorem wflow_saturates_forward :
    ∀ u ∈ wcut, ∀ v ∈ wcutᶜ, wflow u v = wNet.cap u v := by
  have hcompl : (wcut : Finset (Fin 4))ᶜ = {2, 3} := by decide
  intro u hu v hv
  rw [hcompl] at hv
  simp only [wcut, Finset.mem_insert, Finset.mem_singleton] at hu hv
  show wflow u v = wcap u v
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rfl

/-- Backward crossing edges of the witness carry no flow. -/
theorem wflow_saturates_backward :
    ∀ u ∈ wcut, ∀ v ∈ wcutᶜ, wflow v u = 0 := by
  have hcompl : (wcut : Finset (Fin 4))ᶜ = {2, 3} := by decide
  intro u hu v hv
  rw [hcompl] at hv
  simp only [wcut, Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> rfl

/-- **Strong duality on the witness (anti-vacuity).** The witness flow saturates the
witness cut, so by the general `strongDuality_of_saturating` the flow value equals the cut
capacity, the flow is a maximum flow, and the cut is a minimum cut — with the common value `2`.
This exhibits the strong-duality conclusion on a concrete nondegenerate instance. -/
theorem witness_strongDuality :
    wNet.flowValue wflow = wNet.cutCapacity wcut ∧
      (∀ g, wNet.IsFlow g → wNet.flowValue g ≤ wNet.flowValue wflow) ∧
      (∀ T, wNet.IsCut T → wNet.cutCapacity wcut ≤ wNet.cutCapacity T) :=
  wNet.strongDuality_of_saturating wcut_isCut wflow_isFlow
    wflow_saturates_forward wflow_saturates_backward

/-- The witness's max flow value and min cut capacity are both the positive integer `2`. -/
theorem witness_maxFlow_eq_minCut_eq_two :
    wNet.flowValue wflow = 2 ∧ wNet.cutCapacity wcut = 2 :=
  ⟨wflow_value, wcut_capacity⟩

/-- **The unconditional headline instantiated at the witness.** `maxFlow_eq_minCut` applied
to `wNet` produces *some* max-flow / min-cut pair with `flowValue = cutCapacity`; combined with weak
duality that common value is forced to be `2` (the witness flow attains `2`, so the max is `≥ 2`,
and the min cut `{0,1}` has capacity `2`, so the max is `≤ 2`). This confirms the general theorem
agrees with the hand-computed witness (max flow = min cut = `2`). -/
theorem witness_headline_value_two :
    ∃ f S, wNet.IsFlow f ∧ wNet.IsCut S ∧
      wNet.flowValue f = wNet.cutCapacity S ∧
      (∀ g, wNet.IsFlow g → wNet.flowValue g ≤ wNet.flowValue f) ∧
      (∀ T, wNet.IsCut T → wNet.cutCapacity S ≤ wNet.cutCapacity T) ∧
      wNet.flowValue f = 2 := by
  obtain ⟨f, S, hf, hS, heq, hmax, hmin⟩ := wNet.maxFlow_eq_minCut
  refine ⟨f, S, hf, hS, heq, hmax, hmin, ?_⟩
  -- max ≥ 2 (witness flow attains 2) and max ≤ 2 (min cut {0,1} has capacity 2)
  have hge : 2 ≤ wNet.flowValue f := by
    have := hmax wflow wflow_isFlow; rw [wflow_value] at this; exact this
  have hle : wNet.flowValue f ≤ 2 := by
    have := Network.flowValue_le_cutCapacity wNet wcut_isCut hf
    rw [wcut_capacity] at this; exact this
  omega

end MaxFlowMinCut.Witness
