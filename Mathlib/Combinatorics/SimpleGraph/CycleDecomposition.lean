/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib.Data.List.Rotate
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Data.Multiset.Count
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel

/-!
# Cycle decomposition of `2`-regular chord multisets and `2`-edge-colouring of even cycles

A **chord list** is a `List (α × α)`: a multiset of undirected edges stored as ordered pairs on a
vertex type `α`.  Because chords are stored with an orientation but represent *undirected* edges,
every statement here is made orientation-free by phrasing it through the **endpoint multiset**
`endpoints M`, which counts *both* projections of every chord.  This models a **multigraph** with
parallel edges and self-loops — something `SimpleGraph` cannot express — so these results are not
available elsewhere in the library.

This file proves two self-contained combinatorial facts, over an arbitrary type `α` with
`DecidableEq`, resting only on `List`/`Multiset` combinatorics:

## Main results

* `decompose_twoRegular` — **any** `2`-regular chord multiset is a permutation of the concatenation
  of a list of closed walks (each a cycle, up to per-chord reversal).  This is the multigraph
  analogue of the classical fact that a `2`-regular graph is a disjoint union of cycles, proven by
  the maximal-simple-path (Euler) peel specialised to the exactly-`2`-regular case.
* `even_cycle_two_perfect_matchings` — an even cycle `walkChords vs` (a closed walk on a `Nodup`
  vertex list of even length) is `2`-edge-colourable: its edges split into **two perfect matchings**
  of the vertex set — the two alternating "sides".

## Implementation notes

The degree of a vertex `v` is `deg M v = (endpoints M).count v`.  A chord `(a, b)` contributes one
endpoint at `a` and one at `b`; a self-loop `(a, a)` contributes two at `a`.  "`2`-regular" means
every present vertex has degree exactly `2` (`IsTwoRegular`).

The closed walk on a vertex sequence `vs = [x₀, …, x_{n-1}]` is `walkChords vs`, the chord list
`(x₀,x₁), …, (x_{n-1},x₀)` built as `vs.zip (vs.rotate 1)`.  A chord list is *shaped like* a closed
walk, `IsClosedWalk M`, when its endpoint multiset equals that of some `walkChords vs` with
`vs ≠ []` — an **orientation-free** contract: it is satisfied by any per-chord reversal, in
particular by the parallel `2`-cycle `[(0,1),(0,1)]` whose chords are stored non-alternating.

The decomposition is assembled from a single **peel** step: `decompose_of_peel` shows that once one
closed walk can be peeled off any nonempty `2`-regular chord list leaving a strictly smaller
`2`-regular remainder (`Peelable`), a full decomposition exists by strong induction on the chord
multiset.  The peel's bookkeeping half (`remainder_regular`, strict smallness) is free from a single
degree computation; the graph-theoretic content is `walkSplit_of_twoRegular`, the maximal-path
existence.
-/

@[expose] public section

open scoped List

namespace Multigraph.CycleDecomp

variable {α : Type*} [DecidableEq α]

/-- The multiset of all chord-endpoints of a chord list: each chord `(a, b)` contributes both
`a` and `b`.  Self-loops `(a, a)` contribute `a` twice. -/
def endpoints (M : List (α × α)) : Multiset α :=
  (M.map Prod.fst : Multiset α) + (M.map Prod.snd : Multiset α)

/-- The **degree** of a vertex `v` in a chord list: the number of chord-endpoints equal to `v`. -/
def deg (M : List (α × α)) (v : α) : ℕ := (endpoints M).count v

omit [DecidableEq α] in
@[simp] theorem endpoints_nil : endpoints ([] : List (α × α)) = 0 := rfl

omit [DecidableEq α] in
@[simp] theorem endpoints_cons (e : α × α) (M : List (α × α)) :
    endpoints (e :: M) = {e.1} + {e.2} + endpoints M := by
  classical
  unfold endpoints
  simp only [List.map_cons]
  ext x
  simp only [Multiset.count_add, Multiset.coe_count, List.count_cons,
    Multiset.count_singleton, beq_iff_eq]
  by_cases h1 : x = e.1 <;> by_cases h2 : x = e.2 <;>
    simp_all [eq_comm] <;> ring

omit [DecidableEq α] in
@[simp] theorem endpoints_append (M N : List (α × α)) :
    endpoints (M ++ N) = endpoints M + endpoints N := by
  classical
  unfold endpoints
  simp only [List.map_append]
  ext x
  simp only [Multiset.count_add, ← Multiset.coe_add, Multiset.coe_count]
  ring

omit [DecidableEq α] in
/-- `endpoints` depends only on the chord multiset (permutation-invariant). -/
theorem endpoints_perm {M N : List (α × α)} (h : M.Perm N) : endpoints M = endpoints N := by
  unfold endpoints
  have h1 : (M.map Prod.fst : Multiset α) = (N.map Prod.fst : Multiset α) :=
    Multiset.coe_eq_coe.mpr (h.map Prod.fst)
  have h2 : (M.map Prod.snd : Multiset α) = (N.map Prod.snd : Multiset α) :=
    Multiset.coe_eq_coe.mpr (h.map Prod.snd)
  rw [h1, h2]

@[simp] theorem deg_nil (v : α) : deg ([] : List (α × α)) v = 0 := rfl

theorem deg_cons (e : α × α) (M : List (α × α)) (v : α) :
    deg (e :: M) v = (if v = e.1 then 1 else 0) + (if v = e.2 then 1 else 0) + deg M v := by
  unfold deg
  rw [endpoints_cons]
  simp only [Multiset.count_add, Multiset.count_singleton]

theorem deg_append (M N : List (α × α)) (v : α) : deg (M ++ N) v = deg M v + deg N v := by
  unfold deg; rw [endpoints_append, Multiset.count_add]

theorem deg_perm {M N : List (α × α)} (h : M.Perm N) (v : α) : deg M v = deg N v := by
  unfold deg; rw [endpoints_perm h]

/-- A vertex is **present** in a chord list iff it has positive degree. -/
theorem deg_pos_iff (M : List (α × α)) (v : α) : 0 < deg M v ↔ v ∈ endpoints M :=
  Multiset.count_pos

/-- **Incident-edge existence.**  Every positive-degree vertex is an endpoint of some chord of the
list.  The first step of any walk-following peel: from a present vertex there is an edge to
follow. -/
theorem exists_incident (M : List (α × α)) (v : α) (h : 0 < deg M v) :
    ∃ e ∈ M, e.1 = v ∨ e.2 = v := by
  have hv : v ∈ endpoints M := (deg_pos_iff M v).mp h
  unfold endpoints at hv
  rw [Multiset.mem_add] at hv
  rcases hv with h1 | h2
  · obtain ⟨e, he, hev⟩ := List.mem_map.mp (Multiset.mem_coe.mp h1)
    exact ⟨e, he, Or.inl hev⟩
  · obtain ⟨e, he, hev⟩ := List.mem_map.mp (Multiset.mem_coe.mp h2)
    exact ⟨e, he, Or.inr hev⟩

/-- **Front-incident extraction.**  From any present vertex `v`, an incident chord can be pulled to
the front of the list (up to `Perm`), oriented either as `(v, w)` or `(w, v)`.  The follow-a-step
primitive of the walk peel: it exposes the next vertex `w` and the remaining chords `R`. -/
theorem exists_front_incident (M : List (α × α)) (v : α) (h : 0 < deg M v) :
    ∃ (w : α) (R : List (α × α)), M.Perm ((v, w) :: R) ∨ M.Perm ((w, v) :: R) := by
  obtain ⟨e, he, hev⟩ := exists_incident M v h
  have hR : M.Perm (e :: M.erase e) := List.perm_cons_erase he
  rcases hev with h1 | h2
  · refine ⟨e.2, M.erase e, Or.inl ?_⟩
    have : ((v, e.2) : α × α) = e := by subst h1; rfl
    rw [this]; exact hR
  · refine ⟨e.1, M.erase e, Or.inr ?_⟩
    have : ((e.1, v) : α × α) = e := by subst h2; rfl
    rw [this]; exact hR

/-- **`2`-regularity**: every present vertex has degree exactly `2`. -/
def IsTwoRegular (M : List (α × α)) : Prop := ∀ v, deg M v = 0 ∨ deg M v = 2

theorem isTwoRegular_perm {M N : List (α × α)} (h : M.Perm N) (hM : IsTwoRegular M) :
    IsTwoRegular N := fun v => by rw [← deg_perm h]; exact hM v

@[simp] theorem isTwoRegular_nil : IsTwoRegular ([] : List (α × α)) := fun _ => Or.inl rfl

/-! ### Closed walks and their `2`-regularity

A **closed walk** on a vertex sequence `vs = [x₀, x₁, …, x_{n-1}]` is the chord list
`(x₀,x₁), (x₁,x₂), …, (x_{n-1},x₀)` — each vertex joined to its cyclic successor.  We build it
as `vs.zip (vs.rotate 1)` (rotating by one supplies the successors, cyclically). -/

/-- The chord list of the closed walk on vertex sequence `vs`: each vertex to its cyclic
successor. -/
def walkChords (vs : List α) : List (α × α) := vs.zip (vs.rotate 1)

omit [DecidableEq α] in
@[simp] theorem walkChords_nil : walkChords ([] : List α) = [] := rfl

omit [DecidableEq α] in
/-- The endpoint multiset of a closed walk on `vs` is `vs + vs` (each vertex appears with
multiplicity `2·(its count in vs)`): as a chord list, the first-projections enumerate `vs` and
the second-projections enumerate the cyclic-successor list, which is a rotation of `vs`, hence
the same multiset. -/
theorem endpoints_walkChords (vs : List α) :
    endpoints (walkChords vs) = (vs : Multiset α) + (vs : Multiset α) := by
  unfold endpoints walkChords
  have hlen : vs.length = (vs.rotate 1).length := by rw [List.length_rotate]
  have hfst : (vs.zip (vs.rotate 1)).map Prod.fst = vs := by
    rw [List.map_fst_zip]; rw [hlen]
  have hsnd : (vs.zip (vs.rotate 1)).map Prod.snd = vs.rotate 1 := by
    rw [List.map_snd_zip]; rw [← hlen]
  rw [hfst, hsnd]
  have hrot : (vs.rotate 1 : Multiset α) = (vs : Multiset α) :=
    Multiset.coe_eq_coe.mpr (vs.rotate_perm 1)
  rw [hrot]

/-- **Degree in a closed walk = twice the vertex's multiplicity in `vs`.**  Holds for ANY vertex
sequence (no distinctness assumed).  In particular, on a `Nodup` `vs` every present vertex has
degree exactly `2`. -/
theorem deg_walkChords (vs : List α) (v : α) : deg (walkChords vs) v = 2 * vs.count v := by
  unfold deg
  rw [endpoints_walkChords, Multiset.count_add, Multiset.coe_count]
  ring

/-- A closed walk on a **distinct** (`Nodup`) vertex sequence is `2`-regular: each present vertex
appears exactly once in `vs`, hence has degree `2·1 = 2`; absent vertices have degree `0`. -/
theorem isTwoRegular_walkChords_of_nodup {vs : List α} (h : vs.Nodup) :
    IsTwoRegular (walkChords vs) := by
  intro v
  rw [deg_walkChords]
  by_cases hv : v ∈ vs
  · right; rw [List.count_eq_one_of_mem h hv]
  · left; rw [List.count_eq_zero_of_not_mem hv]

/-- **`IsClosedWalk M`** — an orientation-free contract.  `M` is a single closed alternating walk
on some nonempty vertex sequence *up to per-chord reversal*: it has the same undirected shape as
`walkChords vs` for some nonempty `vs`, certified orientation-freely by equality of the endpoint
multisets `endpoints M = endpoints (walkChords vs)`.

The endpoint-multiset form is orientation-free: `endpoints` counts *both* projections of every
chord, so it is invariant under reversing any chord `(a,b) ↦ (b,a)`.  This makes the predicate
satisfiable by a genuine sub-multiset of `M` regardless of how its chords are stored — in
particular by the parallel `2`-cycle `[(0,1),(0,1)]`, for which no all-forward `walkChords vs` is a
`Perm` (see `closedWalkSplit_parallel`). -/
def IsClosedWalk (M : List (α × α)) : Prop :=
  ∃ vs : List α, vs ≠ [] ∧ endpoints M = endpoints (walkChords vs)

/-! ### The decomposition, reduced to a single peel step

`decompose_of_peel` shows: **once one closed walk can be peeled off any nonempty `2`-regular chord
list leaving a strictly-smaller `2`-regular remainder** (`Peelable`), a full decomposition into
closed walks exists, by strong induction on the chord multiset. -/

/-- **The peel hypothesis**: every nonempty `2`-regular chord list splits (up to `Perm`) as a
nonempty closed walk `W` followed by a `2`-regular remainder `R`, with `R` strictly smaller. -/
def Peelable (α : Type*) [DecidableEq α] : Prop :=
  ∀ M : List (α × α), IsTwoRegular M → M ≠ [] →
    ∃ W R : List (α × α), M.Perm (W ++ R) ∧ IsClosedWalk W ∧ IsTwoRegular R ∧
      R.length < M.length

/-- **Decomposition from peelability.**  If `Peelable α`, then every `2`-regular chord list is a
`Perm` of the concatenation of a list of closed walks.  Strong induction on `M.length`. -/
theorem decompose_of_peel (hpeel : Peelable α) :
    ∀ M : List (α × α), IsTwoRegular M →
      ∃ cs : List (List (α × α)), (∀ c ∈ cs, IsClosedWalk c) ∧ M.Perm cs.flatten := by
  -- Strong induction on the number of chords.
  suffices h : ∀ n : ℕ, ∀ M : List (α × α), M.length ≤ n → IsTwoRegular M →
      ∃ cs : List (List (α × α)), (∀ c ∈ cs, IsClosedWalk c) ∧ M.Perm cs.flatten by
    intro M hreg; exact h M.length M le_rfl hreg
  intro n
  induction n with
  | zero =>
    intro M hlen _
    have : M = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    exact ⟨[], by simp, by simp [this]⟩
  | succ n ih =>
    intro M hlen hreg
    by_cases hM : M = []
    · exact ⟨[], by simp, by simp [hM]⟩
    · obtain ⟨W, R, hperm, hW, hRreg, hRlt⟩ := hpeel M hreg hM
      have hRlen : R.length ≤ n := by
        have : M.length ≤ n + 1 := hlen
        omega
      obtain ⟨cs, hcs, hRperm⟩ := ih R hRlen hRreg
      refine ⟨W :: cs, ?_, ?_⟩
      · intro c hc
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact hW
        · exact hcs c hc'
      · refine hperm.trans (List.Perm.trans (hRperm.append_left W) ?_)
        simp

/-! ### Non-vacuity of the decomposition interface

We certify the abstract objects are genuinely inhabited: a closed walk on a `Nodup` nonempty vertex
list is an `IsClosedWalk` and is `2`-regular, its `decompose` output is the singleton list
containing it, and `Peelable`'s conclusion is satisfiable on it (peel the whole walk, empty
remainder).  So none of `IsClosedWalk`, `IsTwoRegular`, nor the peel conclusion is vacuous. -/

omit [DecidableEq α] in
/-- A closed walk on a `Nodup` nonempty vertex list is itself an `IsClosedWalk` (endpoint multisets
are literally equal). -/
theorem isClosedWalk_walkChords {vs : List α} (hne : vs ≠ []) :
    IsClosedWalk (walkChords vs) := ⟨vs, hne, rfl⟩

omit [DecidableEq α] in
/-- **`IsClosedWalk` is orientation-free / `Perm`-invariant.**  Any `Perm` of a closed walk (in
particular any per-chord reversal, which preserves `endpoints`) is again an `IsClosedWalk`. -/
theorem isClosedWalk_of_endpoints_eq {W W' : List (α × α)}
    (h : endpoints W = endpoints W') (hW : IsClosedWalk W) : IsClosedWalk W' := by
  obtain ⟨vs, hne, hep⟩ := hW
  exact ⟨vs, hne, by rw [← h, hep]⟩

/-- **Non-vacuity: any single `2`-regular closed walk peels (whole walk, empty remainder).**  If
`M` is a `Perm` of a closed walk on a nonempty `Nodup` vertex list, then the `Peelable` conclusion
holds for `M` with `W = M`, `R = []`. -/
theorem peel_of_single_walk {M : List (α × α)} {vs : List α}
    (hne : vs ≠ []) (hperm : M.Perm (walkChords vs)) :
    ∃ W R : List (α × α), M.Perm (W ++ R) ∧ IsClosedWalk W ∧ IsTwoRegular R ∧
      R.length < M.length := by
  refine ⟨M, [], by simp, ⟨vs, hne, endpoints_perm hperm⟩, isTwoRegular_nil, ?_⟩
  have : 0 < M.length := by
    rw [List.length_pos_iff]
    intro hMnil
    rw [hMnil] at hperm
    have := hperm.length_eq
    simp only [List.length_nil] at this
    -- walkChords vs has length vs.length ≥ 1
    have hlen : (walkChords vs).length = vs.length := by
      unfold walkChords; rw [List.length_zip, List.length_rotate, min_self]
    rw [hlen] at this
    exact hne (List.length_eq_zero_iff.mp this.symm)
  simpa using this

omit [DecidableEq α] in
/-- **Non-vacuity of `decompose_of_peel`**: fed the single-walk peel witness, a `2`-regular
closed walk decomposes into the singleton list `[itself]`. -/
theorem decompose_single_walk_nonvacuous {vs : List α} (hne : vs ≠ []) :
    ∃ cs : List (List (α × α)),
      (∀ c ∈ cs, IsClosedWalk c) ∧ (walkChords vs).Perm cs.flatten := by
  refine ⟨[walkChords vs], ?_, by simp⟩
  intro c hc
  rw [List.mem_singleton.mp hc]
  exact isClosedWalk_walkChords hne

/-! ### The full standalone decomposition, modulo the peel -/

/-- **The full standalone decomposition, modulo the peel.**  Alias of `decompose_of_peel`,
recording the headline shape of the standalone lemma: assuming the (non-vacuous, purely
combinatorial) peel, every `2`-regular chord list is a `Perm` of a concatenation of closed
walks. -/
theorem decompose (hpeel : Peelable α) (M : List (α × α)) (hreg : IsTwoRegular M) :
    ∃ cs : List (List (α × α)), (∀ c ∈ cs, IsClosedWalk c) ∧ M.Perm cs.flatten :=
  decompose_of_peel hpeel M hreg

/-! ### Peelability reduces to finding one closed-walk split (remainder regularity is free)

The remainder `2`-regularity and strict smallness in `Peelable` come **for free** from a single
degree computation, once one exhibits a `Nodup` nonempty vertex list `vs` and remainder `R` with
`M.Perm (W ++ R)` and `endpoints W = endpoints (walkChords vs)`. -/

/-- **Remainder regularity (the free half of the peel).**  If `M` is `2`-regular and splits (up to
`Perm`) as an extracted walk `W` of the undirected shape of the closed walk on a `Nodup` vertex list
`vs` (`endpoints W = endpoints (walkChords vs)`) plus a remainder `R`, then `R` is `2`-regular. -/
theorem remainder_regular {M W : List (α × α)} {vs : List α} {R : List (α × α)}
    (hreg : IsTwoRegular M) (hnodup : vs.Nodup) (hperm : M.Perm (W ++ R))
    (hshape : endpoints W = endpoints (walkChords vs)) :
    IsTwoRegular R := by
  intro v
  have hdegW : deg W v = deg (walkChords vs) v := by unfold deg; rw [hshape]
  have hM : deg M v = deg (walkChords vs) v + deg R v := by
    rw [deg_perm hperm, deg_append, hdegW]
  rw [deg_walkChords] at hM
  by_cases hv : v ∈ vs
  · rw [List.count_eq_one_of_mem hnodup hv] at hM
    rcases hreg v with h0 | h2
    · omega
    · left; omega
  · rw [List.count_eq_zero_of_not_mem hv] at hM
    rcases hreg v with h0 | h2
    · left; omega
    · right; omega

/-- **A closed-walk split** — an orientation-free contract.  A `Nodup` nonempty vertex list `vs`, an
extracted walk `W` that is a GENUINE sub-multiset of `M` (its chords appear in `M` with their real
orientations, `M.Perm (W ++ R)`), and a remainder `R`, such that `W` has the undirected shape of the
closed walk on `vs` (`endpoints W = endpoints (walkChords vs)`).  This is the pure combinatorial
residue of the peel — from it, `peel_of_split` recovers the full `Peelable` conclusion. -/
def HasClosedWalkSplit (M : List (α × α)) : Prop :=
  ∃ (vs : List α) (W R : List (α × α)),
    vs ≠ [] ∧ vs.Nodup ∧ M.Perm (W ++ R) ∧ endpoints W = endpoints (walkChords vs)

/-- **Peel from a closed-walk split.**  A closed-walk split of a nonempty `2`-regular `M` yields the
full `Peelable` conclusion: `W` is a nonempty closed walk, `R` is `2`-regular (by
`remainder_regular`) and strictly smaller (the walk is nonempty, so `R.length < M.length`). -/
theorem peel_of_split {M : List (α × α)} (hreg : IsTwoRegular M) (_hM : M ≠ [])
    (hsplit : HasClosedWalkSplit M) :
    ∃ W R : List (α × α), M.Perm (W ++ R) ∧ IsClosedWalk W ∧ IsTwoRegular R ∧
      R.length < M.length := by
  obtain ⟨vs, W, R, hne, hnodup, hperm, hshape⟩ := hsplit
  refine ⟨W, R, hperm, ⟨vs, hne, hshape⟩,
    remainder_regular hreg hnodup hperm hshape, ?_⟩
  -- R.length < M.length: M.length = W.length + R.length, and W nonempty (it has the same nonempty
  -- endpoint multiset as walkChords vs, whose cardinality is 2·|vs| > 0).
  have hlenM : M.length = W.length + R.length := by
    rw [hperm.length_eq, List.length_append]
  have hwpos : 0 < W.length := by
    rw [List.length_pos_iff]
    intro hWnil
    -- W = [] ⟹ endpoints W = 0, but endpoints (walkChords vs) = vs + vs ≠ 0 since vs ≠ [].
    have h0 : endpoints (walkChords vs) = 0 := by rw [← hshape, hWnil]; rfl
    rw [endpoints_walkChords] at h0
    have hcard := congrArg Multiset.card h0
    simp only [Multiset.card_add, Multiset.card_zero, Multiset.coe_card] at hcard
    exact hne (List.length_eq_zero_iff.mp (by omega))
  omega

/-- **`Peelable` from a uniform closed-walk split supplier.**  If every nonempty `2`-regular chord
list has a closed-walk split, then `Peelable α` holds — hence (`decompose_of_peel`) the full
decomposition.  This isolates the SOLE remaining obligation to
`∀ M, IsTwoRegular M → M ≠ [] → HasClosedWalkSplit M`. -/
theorem peelable_of_split
    (hsupply : ∀ M : List (α × α), IsTwoRegular M → M ≠ [] → HasClosedWalkSplit M) :
    Peelable α :=
  fun M hreg hM => peel_of_split hreg hM (hsupply M hreg hM)

/-! ### The maximal-path peel: proving `HasClosedWalkSplit` for `2`-regular chord lists

We prove that any nonempty exactly-`2`-regular chord list contains a `Nodup` closed walk, by the
classic *maximal simple path* argument, specialised to the `2`-regular case:

* Grow a `Nodup` **open path** `p = [v₀, v₁, …, vₖ]` whose consecutive chords `pathChords p`
  are a sub-multiset of `M`, tracking the remainder `Rem` with `M.Perm (pathChords p ++ Rem)`.
* At the endpoint `e = vₖ`, a degree count (`deg M e = 2`, of which `pathChords p` consumes at most
  one) forces a fresh incident chord in `Rem`, to some `w`.
* **`2`-regularity kills the interior case**: an interior vertex already has degree `2` in
  `pathChords p`, hence degree `0` in `Rem`, so the fresh chord cannot land on an interior vertex.
  It lands on a NEW vertex (extend the path) or on the START `v₀` (close the WHOLE path into a
  `Nodup` cycle).  The remainder strictly shrinks each extension, giving termination. -/

/-- The **open path chords** of a vertex sequence `vs = [v₀, …, vₖ]`: the consecutive chords
`(v₀,v₁), (v₁,v₂), …, (v_{k-1},vₖ)` — one fewer than `walkChords`, omitting the closing edge. -/
def pathChords (vs : List α) : List (α × α) := vs.zip vs.tail

omit [DecidableEq α] in
@[simp] theorem pathChords_nil : pathChords ([] : List α) = [] := rfl

omit [DecidableEq α] in
@[simp] theorem pathChords_singleton (v : α) : pathChords [v] = [] := rfl

omit [DecidableEq α] in
theorem pathChords_cons_cons (a b : α) (vs : List α) :
    pathChords (a :: b :: vs) = (a, b) :: pathChords (b :: vs) := by
  unfold pathChords
  simp [List.zip_cons_cons]

omit [DecidableEq α] in
/-- The first-projections of `pathChords p` enumerate `p.dropLast` (all vertices but the last). -/
theorem pathChords_map_fst (p : List α) : (pathChords p).map Prod.fst = p.dropLast := by
  unfold pathChords
  induction p with
  | nil => rfl
  | cons a rest ih =>
    match rest with
    | [] => rfl
    | b :: rest' =>
      simp only [List.tail_cons, List.zip_cons_cons, List.map_cons, List.dropLast_cons_cons]
      simp only [List.tail_cons] at ih
      rw [ih]

omit [DecidableEq α] in
/-- The second-projections of `pathChords p` enumerate `p.tail` (all vertices but the first). -/
theorem pathChords_map_snd (p : List α) : (pathChords p).map Prod.snd = p.tail := by
  unfold pathChords
  induction p with
  | nil => rfl
  | cons a rest ih =>
    match rest with
    | [] => rfl
    | b :: rest' =>
      simp only [List.tail_cons, List.zip_cons_cons, List.map_cons]
      simp only [List.tail_cons] at ih
      rw [ih]

omit [DecidableEq α] in
/-- **Endpoint multiset of the open path chords.**  `endpoints (pathChords p) = p.dropLast + p.tail`
(as multisets): the first-projections enumerate `dropLast`, the seconds enumerate `tail`. -/
theorem endpoints_pathChords (p : List α) :
    endpoints (pathChords p) = (p.dropLast : Multiset α) + (p.tail : Multiset α) := by
  unfold endpoints
  rw [pathChords_map_fst, pathChords_map_snd]

/-- **Degree in the open path chords** = `dropLast`-count + `tail`-count. -/
theorem deg_pathChords (p : List α) (v : α) :
    deg (pathChords p) v = p.dropLast.count v + p.tail.count v := by
  unfold deg
  rw [endpoints_pathChords, Multiset.count_add, Multiset.coe_count, Multiset.coe_count]

/-- **Endpoint degree bound**: in the open path chords, the LAST vertex has degree at most `1`.
This is what lets the walk always leave the current endpoint: its consumed path-degree is
`≤ 1 < 2 = deg M`. -/
theorem deg_pathChords_getLast_le_one {p : List α} (hne : p ≠ []) (hnd : p.Nodup) :
    deg (pathChords p) (p.getLast hne) ≤ 1 := by
  rw [deg_pathChords]
  have htail : p.tail.count (p.getLast hne) ≤ 1 :=
    List.nodup_iff_count_le_one.mp (hnd.sublist (List.tail_sublist p)) _
  have hdrop : p.dropLast.count (p.getLast hne) = 0 := by
    rw [List.count_eq_zero]
    intro hmem
    -- getLast ∉ dropLast for a Nodup list (it would repeat with the last element)
    have hnd' : (p.dropLast ++ [p.getLast hne]).Nodup := by
      rw [List.dropLast_append_getLast hne]; exact hnd
    rw [List.nodup_append] at hnd'
    exact hnd'.2.2 _ hmem _ (List.mem_singleton_self _) rfl
  omega

omit [DecidableEq α] in
/-- A member of a list distinct from its last element lies in `dropLast`. -/
theorem mem_dropLast_of_ne_getLast {p : List α} {w : α} (hne : p ≠ [])
    (hmem : w ∈ p) (hlast : w ≠ p.getLast hne) : w ∈ p.dropLast := by
  have hsplit : p.dropLast ++ [p.getLast hne] = p := List.dropLast_append_getLast hne
  rw [← hsplit, List.mem_append] at hmem
  rcases hmem with h | h
  · exact h
  · exact absurd (List.mem_singleton.mp h) hlast

omit [DecidableEq α] in
/-- A member of a list distinct from its head lies in `tail`. -/
theorem mem_tail_of_ne_head {p : List α} {w : α} (hne : p ≠ [])
    (hmem : w ∈ p) (hhead : w ≠ p.head hne) : w ∈ p.tail := by
  match p, hne with
  | a :: rest, _ =>
    simp only [List.head_cons] at hhead
    rcases List.mem_cons.mp hmem with h | h
    · exact absurd h hhead
    · simpa using h

/-- **Interior degree in the open path chords.**  For a `Nodup` path `p`, any vertex `w ∈ p`
distinct from BOTH the head and the last has degree exactly `2` in `pathChords p` (it is joined to
its predecessor and its successor).  This forbids the growing walk from re-entering an interior
vertex in a `2`-regular graph: interior vertices are already saturated. -/
theorem deg_pathChords_interior {p : List α} {w : α} (hnd : p.Nodup) (hne : p ≠ [])
    (hmem : w ∈ p) (hhead : w ≠ p.head hne) (hlast : w ≠ p.getLast hne) :
    deg (pathChords p) w = 2 := by
  rw [deg_pathChords]
  have hd : p.dropLast.count w = 1 :=
    List.count_eq_one_of_mem (hnd.sublist (List.dropLast_sublist p))
      (mem_dropLast_of_ne_getLast hne hmem hlast)
  have ht : p.tail.count w = 1 :=
    List.count_eq_one_of_mem (hnd.sublist (List.tail_sublist p))
      (mem_tail_of_ne_head hne hmem hhead)
  omega

omit [DecidableEq α] in
/-- **Zip-with-tail-plus-tail lemma.**  For a nonempty list `l = v :: rest` and any element `x`,
zipping `l` against `(l.tail ++ [x])` equals `pathChords l` (which zips `l` against `l.tail`)
extended by the single pair `(l.getLast, x)`.  This is the "append a successor for the last vertex"
identity. -/
theorem zip_tail_append_eq_pathChords_close (x : α) :
    ∀ (v : α) (rest : List α),
      (v :: rest).zip (rest ++ [x]) = pathChords (v :: rest) ++ [((v :: rest).getLast (by simp), x)]
  | _, [] => by simp [pathChords]
  | v, c :: cs => by
    -- (v :: c :: cs).zip ((c :: cs) ++ [x]) = (v,c) :: (c :: cs).zip (cs ++ [x])
    simp only [List.cons_append, List.zip_cons_cons]
    rw [pathChords_cons_cons]
    have hgl : (v :: c :: cs).getLast (by simp) = (c :: cs).getLast (by simp) :=
      List.getLast_cons (by simp)
    rw [hgl, zip_tail_append_eq_pathChords_close x c cs, List.cons_append]

omit [DecidableEq α] in
/-- **`walkChords` = `pathChords` plus the closing edge** (up to `Perm`).  For a nonempty vertex
list `vs` with head `h` and last `l`, the closed walk's chords are the open-path chords together
with the single closing chord `(l, h)`. -/
theorem walkChords_perm_pathChords_close {vs : List α} (hne : vs ≠ []) :
    (walkChords vs).Perm (pathChords vs ++ [(vs.getLast hne, vs.head hne)]) := by
  match vs, hne with
  | [_], _ => simp [walkChords, pathChords]
  | a :: b :: rest, _ =>
    have hrot : (a :: b :: rest).rotate 1 = (b :: rest) ++ [a] := by
      rw [List.rotate_cons_succ, List.rotate_zero]
    unfold walkChords
    rw [hrot, List.cons_append, List.zip_cons_cons, pathChords_cons_cons]
    have hgl : (a :: b :: rest).getLast (by simp) = (b :: rest).getLast (by simp) :=
      List.getLast_cons (by simp)
    rw [hgl]
    simp only [List.head_cons]
    apply List.Perm.cons
    -- Goal: (b :: rest).zip (rest ++ [a]) ~ pathChords (b :: rest) ++ [((b::rest).getLast _, a)]
    rw [zip_tail_append_eq_pathChords_close a b rest]
    exact List.Perm.refl _

omit [DecidableEq α] in
/-- **Appending one vertex extends the open-path chords by the closing edge from the old last.**
`pathChords (p ++ [w]) = pathChords p ++ [(p.getLast, w)]` for nonempty `p`. -/
theorem pathChords_append_singleton :
    ∀ (p : List α) (hne : p ≠ []) (w : α),
      pathChords (p ++ [w]) = pathChords p ++ [(p.getLast hne, w)]
  | [_], _, w => by simp [pathChords]
  | v :: c :: cs, _, w => by
    have hgl : (v :: c :: cs).getLast (by simp) = (c :: cs).getLast (by simp) :=
      List.getLast_cons (by simp)
    have ih := pathChords_append_singleton (c :: cs) (by simp) w
    simp only [List.cons_append] at *
    rw [pathChords_cons_cons, pathChords_cons_cons, hgl, ih, List.cons_append]

/-! ### The maximal-path existence — `walkSplit_of_twoRegular`

We grow a `Nodup` open path `p`, tracking the **genuinely-oriented** consumed chords `W` (a
sub-multiset of `M`) and remainder `Rem` with `M.Perm (W ++ Rem)` and the orientation-free shape
invariant `endpoints W = endpoints (pathChords p)`.  A degree count at the endpoint forces a fresh
incident chord in `Rem` (`2`-regularity), which either CLOSES the walk (neighbour = path head) or
EXTENDS it to a new vertex (`2`-regularity kills re-entry to any interior/last vertex).  Strong
induction on `Rem.length`. -/

omit [DecidableEq α] in
/-- Endpoint multiset of a single chord `(a,b)` is `{a} + {b}` (orientation-symmetric). -/
theorem endpoints_singleton (a b : α) : endpoints [(a, b)] = {a} + {b} := by
  rw [endpoints_cons]; simp [endpoints]

/-- `deg W v = deg (pathChords p) v` from equality of the endpoint multisets. -/
theorem deg_eq_of_endpoints {W : List (α × α)} {p : List α}
    (h : endpoints W = endpoints (pathChords p)) (v : α) : deg W v = deg (pathChords p) v := by
  unfold deg; rw [h]

/-- If `v` is an endpoint of the chord `c`, then `v` has positive degree in `c :: R'`. -/
theorem deg_cons_pos_of_mem {c : α × α} {R' : List (α × α)} {w : α}
    (hw : w ∈ endpoints [c]) : 0 < deg (c :: R') w := by
  unfold deg; rw [endpoints_cons]
  have hc : endpoints [c] = {c.1} + {c.2} := by rw [endpoints_cons]; simp [endpoints]
  rw [hc] at hw
  rw [Multiset.count_add]
  have : 0 < Multiset.count w ({c.1} + {c.2}) := Multiset.count_pos.mpr hw
  omega

omit [DecidableEq α] in
/-- **Endpoint multiset of a closed walk = open-path endpoints + closing edge endpoints.**  A direct
corollary of `walkChords_perm_pathChords_close` read through `endpoints`.  This is the identity that
makes the closing step of the maximal-path recursion land exactly on `endpoints (walkChords vs)`. -/
theorem endpoints_walkChords_eq (vs : List α) (hne : vs ≠ []) :
    endpoints (walkChords vs)
      = endpoints (pathChords vs) + ({vs.getLast hne} + {vs.head hne}) := by
  rw [endpoints_perm (walkChords_perm_pathChords_close hne), endpoints_append, endpoints_singleton]

omit [DecidableEq α] in
/-- `getLast ≠ head` for a `Nodup` list of length `≥ 2`. -/
theorem getLast_ne_head {p : List α} (hne : p ≠ []) (hnd : p.Nodup) (_h2 : 2 ≤ p.length) :
    p.getLast hne ≠ p.head hne := by
  match p, hne, hnd with
  | a :: b :: rest, _, hnd =>
    simp only [List.head_cons]
    have hgl : (a :: b :: rest).getLast (by simp) = (b :: rest).getLast (by simp) :=
      List.getLast_cons (by simp)
    rw [hgl]
    have hmem : (b :: rest).getLast (by simp) ∈ (b :: rest) := List.getLast_mem (by simp)
    intro hc
    exact (List.nodup_cons.mp hnd).1 (hc ▸ hmem)

/-- **Endpoint path-degree = exactly `1`** for a `Nodup` path of length `≥ 2` (the last vertex is
incident to exactly the last chord).  Companion of `deg_pathChords_getLast_le_one`; used to rule out
a self-loop landing back on the endpoint. -/
theorem deg_pathChords_getLast_eq_one {p : List α} (hne : p ≠ []) (hnd : p.Nodup)
    (h2 : 2 ≤ p.length) : deg (pathChords p) (p.getLast hne) = 1 := by
  rw [deg_pathChords]
  have hdrop : p.dropLast.count (p.getLast hne) = 0 := by
    rw [List.count_eq_zero]
    intro hmem
    have hnd' : (p.dropLast ++ [p.getLast hne]).Nodup := by
      rw [List.dropLast_append_getLast hne]; exact hnd
    rw [List.nodup_append] at hnd'
    exact hnd'.2.2 _ hmem _ (List.mem_singleton_self _) rfl
  have htail : p.tail.count (p.getLast hne) = 1 :=
    List.count_eq_one_of_mem (hnd.sublist (List.tail_sublist p))
      (mem_tail_of_ne_head hne (List.getLast_mem hne) (getLast_ne_head hne hnd h2))
  omega

/-- **The maximal-path recursion (invariant-carrying).**  Given a `Nodup` open path `p` in a
nonempty `2`-regular `M`, with all path vertices of degree `2` in `M`, a genuine sub-multiset `W` of
`M` of the shape of `pathChords p`, and remainder `Rem` with `M.Perm (W ++ Rem)`, a closed-walk
split of `M` exists.  Strong induction on `Rem.length`: at the endpoint a degree count forces a
fresh `Rem`-chord (`2`-regularity), which either CLOSES (neighbour = head) or EXTENDS to a genuinely
new vertex (`2`-regularity forbids re-entry to any interior vertex and, for `|p| ≥ 2`, to the
endpoint via a self-loop). -/
theorem walkExtend : ∀ (n : ℕ) (M : List (α × α)), IsTwoRegular M →
    ∀ (p : List α) (W Rem : List (α × α)),
      p ≠ [] → p.Nodup → (∀ v ∈ p, deg M v = 2) →
      M.Perm (W ++ Rem) → endpoints W = endpoints (pathChords p) → Rem.length ≤ n →
      HasClosedWalkSplit M := by
  intro n
  induction n with
  | zero =>
    intro M _ p W Rem hpne hpnd hdegp hperm hshape hlen
    exfalso
    have hRnil : Rem = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
    have hdegMe : deg M (p.getLast hpne) = 2 := hdegp _ (List.getLast_mem hpne)
    have hdegWe : deg W (p.getLast hpne) ≤ 1 := by
      rw [deg_eq_of_endpoints hshape]; exact deg_pathChords_getLast_le_one hpne hpnd
    have hsum : deg M (p.getLast hpne)
        = deg W (p.getLast hpne) + deg Rem (p.getLast hpne) := by
      rw [deg_perm hperm, deg_append]
    have hpos : 0 < deg Rem (p.getLast hpne) := by omega
    rw [hRnil] at hpos; simp [deg, endpoints] at hpos
  | succ n ih =>
    intro M hreg p W Rem hpne hpnd hdegp hperm hshape _hlen
    have hdegMe : deg M (p.getLast hpne) = 2 := hdegp _ (List.getLast_mem hpne)
    have hdegWe : deg W (p.getLast hpne) ≤ 1 := by
      rw [deg_eq_of_endpoints hshape]; exact deg_pathChords_getLast_le_one hpne hpnd
    have hsum : deg M (p.getLast hpne)
        = deg W (p.getLast hpne) + deg Rem (p.getLast hpne) := by
      rw [deg_perm hperm, deg_append]
    have hRemPos : 0 < deg Rem (p.getLast hpne) := by omega
    obtain ⟨w, R', hchord⟩ := exists_front_incident Rem _ hRemPos
    obtain ⟨c, hcRem, hcep⟩ :
        ∃ c : α × α, Rem.Perm (c :: R') ∧ endpoints [c] = {p.getLast hpne} + {w} := by
      rcases hchord with h | h
      · exact ⟨(p.getLast hpne, w), h, endpoints_singleton _ _⟩
      · exact ⟨(w, p.getLast hpne), h, by
          rw [endpoints_singleton]; exact add_comm ({w} : Multiset α) {p.getLast hpne}⟩
    have hpermNew : M.Perm ((c :: W) ++ R') := by
      refine hperm.trans ((List.Perm.append_left W hcRem).trans ?_)
      simp
    have hshapeNew :
        endpoints (c :: W) = endpoints (pathChords p) + ({p.getLast hpne} + {w}) := by
      rw [endpoints_cons, hshape]
      have hc1 : ({c.1} + {c.2} : Multiset α) = {p.getLast hpne} + {w} := by
        have hc : endpoints [c] = {c.1} + {c.2} := by rw [endpoints_cons]; simp [endpoints]
        rw [hc] at hcep; exact hcep
      rw [hc1]; exact add_comm ({p.getLast hpne} + {w}) (endpoints (pathChords p))
    have hR'len : R'.length ≤ n := by
      have : Rem.length = R'.length + 1 := by simpa using hcRem.length_eq
      omega
    have hwRem : 0 < deg Rem w := by
      rw [deg_perm hcRem]; exact deg_cons_pos_of_mem (by rw [hcep]; simp)
    have hdegMw : deg M w = 2 := by
      have hpos : 0 < deg M w := by rw [deg_perm hperm, deg_append]; omega
      rcases hreg w with h | h
      · omega
      · exact h
    by_cases hclose : w = p.head hpne
    · refine ⟨p, c :: W, R', hpne, hpnd, hpermNew, ?_⟩
      rw [hshapeNew, endpoints_walkChords_eq p hpne, hclose]
    · have hwnotp : w ∉ p := by
        intro hwp
        by_cases hwlast : w = p.getLast hpne
        · have hcep2 : endpoints [c] = {p.getLast hpne} + {p.getLast hpne} := by
            rw [hcep, hwlast]
          have hdegRemLast : 2 ≤ deg Rem (p.getLast hpne) := by
            rw [deg_perm hcRem]; unfold deg; rw [endpoints_cons]
            have hc : endpoints [c] = {c.1} + {c.2} := by rw [endpoints_cons]; simp [endpoints]
            rw [hc] at hcep2
            rw [Multiset.count_add]
            have hcnt : Multiset.count (p.getLast hpne) ({c.1} + {c.2}) = 2 := by
              rw [hcep2]; simp
            omega
          rcases Nat.lt_or_ge p.length 2 with hlt | hge
          · have hp1 : p.length = 1 := by
              have : 0 < p.length := List.length_pos_iff.mpr hpne
              omega
            have hhg : p.head hpne = p.getLast hpne := by
              match p, hpne, hp1 with
              | [_], _, _ => simp
            exact hclose (by rw [hwlast, ← hhg])
          · have hd1 : deg (pathChords p) (p.getLast hpne) = 1 :=
              deg_pathChords_getLast_eq_one hpne hpnd hge
            have hWlast : deg W (p.getLast hpne) = 1 := by rw [deg_eq_of_endpoints hshape, hd1]
            omega
        · have hint : deg (pathChords p) w = 2 :=
            deg_pathChords_interior hpnd hpne hwp hclose hwlast
          have hWw : deg W w = 2 := by rw [deg_eq_of_endpoints hshape, hint]
          have hMw : deg M w = deg W w + deg Rem w := by rw [deg_perm hperm, deg_append]
          omega
      have hp'nd : (p ++ [w]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hpnd, List.nodup_singleton w, ?_⟩
        intro x hx y hy
        rw [List.mem_singleton] at hy; subst hy
        intro h; exact hwnotp (h ▸ hx)
      have hp'ne : p ++ [w] ≠ [] := by simp
      have hdegp' : ∀ v ∈ (p ++ [w]), deg M v = 2 := by
        intro v hv
        rw [List.mem_append] at hv
        rcases hv with h | h
        · exact hdegp v h
        · rw [List.mem_singleton.mp h]; exact hdegMw
      have hshape' : endpoints (c :: W) = endpoints (pathChords (p ++ [w])) := by
        rw [pathChords_append_singleton p hpne w, endpoints_append, hshapeNew,
          endpoints_singleton]
      exact ih M hreg (p ++ [w]) (c :: W) R' hp'ne hp'nd hdegp' hpermNew hshape' hR'len

/-- **`walkSplit_of_twoRegular` — the orientation-free existence, UNCONDITIONAL.**  Any nonempty
exactly-`2`-regular chord list has a closed-walk split.  Proof: start the maximal-path recursion
`walkExtend` from the singleton path `[v₀]` at any present vertex `v₀` (degree `2`), empty consumed
walk `W = []`, `Rem = M`.  This discharges the sole remaining obligation: with it,
`peelable_of_split walkSplit_of_twoRegular` gives `Peelable α`, hence `decompose` gives the full
alternating-cycle decomposition of ANY `2`-regular chord multiset, unconditionally. -/
theorem walkSplit_of_twoRegular (M : List (α × α)) (hreg : IsTwoRegular M) (hne : M ≠ []) :
    HasClosedWalkSplit M := by
  obtain ⟨e, heM⟩ : ∃ e, e ∈ M := by
    match M, hne with
    | e :: rest, _ => exact ⟨e, by simp⟩
  have hv₀pos : 0 < deg M e.1 := by
    rw [deg_pos_iff]
    have : e.1 ∈ (M.map Prod.fst) := List.mem_map.mpr ⟨e, heM, rfl⟩
    unfold endpoints; rw [Multiset.mem_add]; exact Or.inl (Multiset.mem_coe.mpr this)
  have hdegMv₀ : deg M e.1 = 2 := by
    rcases hreg e.1 with h | h
    · omega
    · exact h
  refine walkExtend M.length M hreg [e.1] [] M (by simp) (by simp) ?_ (by simp) ?_ le_rfl
  · intro v hv; rw [List.mem_singleton.mp hv]; exact hdegMv₀
  · simp [pathChords, endpoints]

/-! ### `CycleDecomp` closed — the unconditional decomposition -/

/-- **`Peelable α`, UNCONDITIONAL.**  Every nonempty `2`-regular chord list peels off one nonempty
closed walk leaving a strictly-smaller `2`-regular remainder. -/
theorem peelable_twoRegular : Peelable α :=
  peelable_of_split (fun M hreg hM => walkSplit_of_twoRegular M hreg hM)

/-- **The standalone alternating-cycle decomposition — CLOSED, UNCONDITIONAL.**  ANY `2`-regular
chord multiset is a permutation of the concatenation of a list of closed walks (each a cycle, up to
per-chord reversal).  The multigraph analogue of "`2`-regular graph = disjoint union of cycles",
resting only on `List`/`Multiset`/`deg` combinatorics. -/
theorem decompose_twoRegular (M : List (α × α)) (hreg : IsTwoRegular M) :
    ∃ cs : List (List (α × α)), (∀ c ∈ cs, IsClosedWalk c) ∧ M.Perm cs.flatten :=
  decompose_of_peel peelable_twoRegular M hreg

/-! ### Orientation tolerance: the parallel `2`-cycle is a positive witness

The all-forward contract `M.Perm (walkChords vs)` PINS the orientation of every chord (its closing
edge is `(vs.getLast, vs.head)`).  A `2`-regular chord list can store a chord reversed — the minimal
witness is the parallel `2`-cycle `[(0,1),(0,1)]` — for which no all-forward `walkChords vs` is a
`Perm`.  The endpoint-multiset contract used throughout is the orientation-free correction, which
MAKES this list a positive witness. -/

/-- The parallel `2`-cycle with both chords oriented `(0,1)`.  A positive witness of the
orientation-free `HasClosedWalkSplit`. -/
def parallelTwoCycle : List (ℕ × ℕ) := [(0, 1), (0, 1)]

/-- `parallelTwoCycle` is nonempty. -/
theorem parallelTwoCycle_ne : parallelTwoCycle ≠ [] := by decide

/-- `parallelTwoCycle` is exactly `2`-regular: `deg 0 = deg 1 = 2`, every other vertex `0`. -/
theorem parallelTwoCycle_twoRegular : IsTwoRegular parallelTwoCycle := by
  intro v
  unfold deg endpoints parallelTwoCycle
  simp only [List.map_cons, List.map_nil]
  by_cases h : v = 0
  · subst h; right; decide
  · by_cases h1 : v = 1
    · subst h1; right; decide
    · left
      simp only [Multiset.count_add]
      rw [Multiset.count_eq_zero.mpr, Multiset.count_eq_zero.mpr]
      · simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil,
          or_false]; tauto
      · simp only [Multiset.mem_coe, List.mem_cons, List.not_mem_nil,
          or_false]; tauto

/-- **The parallel `2`-cycle is a positive witness of the orientation-free `HasClosedWalkSplit`.**
The parallel `2`-cycle `[(0,1),(0,1)]` DOES satisfy the orientation-free contract: with
`vs = [0,1]`, `W = parallelTwoCycle`, `R = []`, the walk `W` is a genuine sub-multiset of `M`
(`M.Perm (W ++ [])`) whose UNDIRECTED shape matches the closed walk on `vs`
(`endpoints parallelTwoCycle = endpoints (walkChords [0,1])`), even though its chords are stored
reversed relative to `walkChords`.  This confirms the orientation tolerance of the contract. -/
theorem closedWalkSplit_parallel : HasClosedWalkSplit parallelTwoCycle := by
  refine ⟨[0, 1], parallelTwoCycle, [], by decide, by decide, by simp, ?_⟩
  -- endpoints [(0,1),(0,1)] = {0,0,1,1} = endpoints (walkChords [0,1]) = {0,1} + {0,1}.
  unfold endpoints walkChords parallelTwoCycle
  rw [show ([0, 1] : List ℕ).rotate 1 = [1, 0] by decide]
  simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons, List.map_nil]
  decide

/-- **The general existence, as a corollary applied to the parallel `2`-cycle.**  A second
confirmation: the general theorem indeed produces a split for the minimal witness. -/
theorem closedWalkSplit_parallel' : HasClosedWalkSplit parallelTwoCycle :=
  walkSplit_of_twoRegular parallelTwoCycle parallelTwoCycle_twoRegular parallelTwoCycle_ne

/-! ### The even-cycle two-perfect-matchings split (`2`-edge-colouring of even cycles)

An even alternating cycle `walkChords vs` on a `Nodup` vertex list `vs` of even length `2k` is
`2`-edge-colourable: its `2k` edges split into TWO perfect matchings of `vs` — the two alternating
"sides".  With `vs = [x₀, x₁, …, x_{2k-1}]`,

* `walkChords vs = [(x₀,x₁), (x₁,x₂), …, (x_{2k-2},x_{2k-1}), (x_{2k-1},x₀)]`,
* **side A** = the even-position edges `[(x₀,x₁), (x₂,x₃), …, (x_{2k-2},x_{2k-1})]`, and
* **side B** = the odd-position edges `[(x₁,x₂), (x₃,x₄), …, (x_{2k-1},x₀)]`,

and `walkChords vs` is a `Perm` of `sideA ++ sideB`, with `endpoints sideA = endpoints sideB = vs`
(each side matches every vertex exactly once).  Side A is `pairUp vs`; side B is
`pairUp (vs.rotate 1)`. -/

/-- **Consecutive pairing** of a vertex list: pair the 1st with the 2nd, the 3rd with the 4th, ….
For an even-length list this is a perfect matching of its elements (`endpoints_pairUp_of_even`). -/
def pairUp : List α → List (α × α)
  | [] => []
  | [_] => []
  | a :: b :: rest => (a, b) :: pairUp rest

omit [DecidableEq α] in
@[simp] theorem pairUp_nil : pairUp ([] : List α) = [] := rfl

omit [DecidableEq α] in
@[simp] theorem pairUp_singleton (a : α) : pairUp [a] = [] := rfl

omit [DecidableEq α] in
@[simp] theorem pairUp_cons_cons (a b : α) (rest : List α) :
    pairUp (a :: b :: rest) = (a, b) :: pairUp rest := rfl

omit [DecidableEq α] in
/-- The endpoint multiset of `pairUp vs` on an even-length list is exactly `vs` (each element
matched once).  By induction pairing off two elements at a time. -/
theorem endpoints_pairUp_of_even {vs : List α} (hlen : Even vs.length) :
    endpoints (pairUp vs) = (vs : Multiset α) := by
  induction vs using pairUp.induct with
  | case1 => simp
  | case2 a =>
    -- length 1 is odd, contradiction
    simp only [List.length_singleton] at hlen
    exact absurd hlen (by decide)
  | case3 a b rest ih =>
    have hrest : Even rest.length := by
      simp only [List.length_cons] at hlen
      rcases hlen with ⟨j, hj⟩
      exact ⟨j - 1, by omega⟩
    rw [pairUp_cons_cons, endpoints_cons, ih hrest]
    have h1 : ((a :: b :: rest : List α) : Multiset α)
        = {a} + ({b} + (rest : Multiset α)) := by
      rw [← Multiset.cons_coe, ← Multiset.cons_coe]
      rw [Multiset.singleton_add, Multiset.singleton_add]
    rw [h1]; exact add_assoc ({a} : Multiset α) {b} (rest : Multiset α)

omit [DecidableEq α] in
/-- **Length of `pairUp`**: half the (even) input length. -/
theorem length_pairUp_of_even {vs : List α} (hlen : Even vs.length) :
    (pairUp vs).length = vs.length / 2 := by
  induction vs using pairUp.induct with
  | case1 => simp
  | case2 a =>
    simp only [List.length_singleton] at hlen
    exact absurd hlen (by decide)
  | case3 a b rest ih =>
    have hrest : Even rest.length := by
      simp only [List.length_cons] at hlen
      rcases hlen with ⟨j, hj⟩
      exact ⟨j - 1, by omega⟩
    rw [pairUp_cons_cons, List.length_cons, ih hrest]
    simp only [List.length_cons]
    omega

/-- **Linear "link" chords** with an explicit closing partner `z`: pair each vertex of `vs` with the
NEXT one in `vs.tail ++ [z]`.  For a nonempty `vs`, `vs.tail ++ [vs.head]` is exactly `vs.rotate 1`,
so `linkChords vs vs.head = walkChords vs` (`linkChords_eq_walkChords`).  Generalising the closing
element `z` is what makes the two-at-a-time recursion go through (the closing partner shifts as we
peel two vertices), threading the wrap-around cleanly. -/
def linkChords (vs : List α) (z : α) : List (α × α) := vs.zip (vs.tail ++ [z])

omit [DecidableEq α] in
/-- The chord MULTISET of a `linkChords` splits into the two alternating sides
`pairUp vs` (even-position edges) and `pairUp (vs.tail ++ [z])` (odd-position edges), for
even-length `vs`. -/
theorem linkChords_multiset_sides (z : α) {vs : List α} (hlen : Even vs.length) :
    (linkChords vs z : Multiset (α × α))
      = (pairUp vs : Multiset (α × α)) + (pairUp (vs.tail ++ [z]) : Multiset (α × α)) := by
  induction vs using pairUp.induct generalizing z with
  | case1 => simp [linkChords]
  | case2 a =>
    simp only [List.length_singleton] at hlen
    exact absurd hlen (by decide)
  | case3 a b rest ih =>
    have hrest : Even rest.length := by
      simp only [List.length_cons] at hlen
      rcases hlen with ⟨j, hj⟩
      exact ⟨j - 1, by omega⟩
    -- Peel two chords (a,b) and (b, head of (rest ++ [z])) off linkChords.
    have hlink : linkChords (a :: b :: rest) z
        = (a, b) :: (b :: rest).zip (rest ++ [z]) := by
      simp only [linkChords, List.tail_cons, List.zip_cons_cons, List.cons_append]
    cases rest with
    | nil =>
      -- rest = [] : then vs = [a,b] length 2, tail++[z] = [b,z]; both sides = {(a,b)} + {(b,z)}.
      simp only [linkChords, List.tail_cons, List.nil_append, List.zip_cons_cons,
        List.zip_nil_right, pairUp_cons_cons, pairUp_nil, List.cons_append]
      simp only [← Multiset.cons_coe, Multiset.coe_nil]
      rfl
    | cons c rest' =>
      have hpeel2 : (b :: c :: rest').zip (c :: rest' ++ [z])
          = (b, c) :: linkChords (c :: rest') z := by
        simp only [linkChords, List.tail_cons, List.zip_cons_cons, List.cons_append]
      have hihrest := ih (z := z) hrest
      simp only [List.tail_cons] at hihrest
      -- hihrest : ↑(linkChords (c::rest') z) = ↑(pairUp (c::rest')) + ↑(pairUp (rest'++[z]))
      rw [hlink]
      rw [show ((b :: c :: rest').zip ((c :: rest') ++ [z]))
            = (b, c) :: linkChords (c :: rest') z from by
        simpa using hpeel2]
      simp only [pairUp_cons_cons, List.tail_cons, List.cons_append]
      simp only [← Multiset.cons_coe]
      rw [hihrest]
      simp only [Multiset.cons_add, Multiset.add_cons, Multiset.cons_swap]

omit [DecidableEq α] in
/-- `linkChords (a :: t) a = walkChords (a :: t)` for nonempty `vs`:
`vs.tail ++ [vs.head] = vs.rotate 1`. -/
theorem linkChords_eq_walkChords {a : α} (t : List α) :
    linkChords (a :: t) a = walkChords (a :: t) := by
  simp only [linkChords, walkChords, List.tail_cons]
  congr 1
  rw [List.rotate_cons_succ, List.rotate_zero]

omit [DecidableEq α] in
/-- **The even-cycle two-sides split.**  For an even-length NONEMPTY vertex list `vs`, the closed
walk `walkChords vs` is a `Perm` of the concatenation of its two alternating sides
`pairUp vs ++ pairUp (vs.rotate 1)`.  (No `Nodup` needed for the `Perm`; distinctness is only used
downstream to make each side a genuine PERFECT matching.) -/
theorem walkChords_perm_sides {a : α} (t : List α) (hlen : Even (a :: t).length) :
    (walkChords (a :: t)).Perm (pairUp (a :: t) ++ pairUp ((a :: t).rotate 1)) := by
  have hrot : (a :: t).rotate 1 = t ++ [a] := by
    rw [List.rotate_cons_succ, List.rotate_zero]
  have hms : (walkChords (a :: t) : Multiset (α × α))
      = ((pairUp (a :: t) ++ pairUp ((a :: t).rotate 1) : List (α × α)) : Multiset (α × α)) := by
    rw [← linkChords_eq_walkChords t]
    rw [linkChords_multiset_sides a hlen, List.tail_cons, hrot, ← Multiset.coe_add]
  exact Multiset.coe_eq_coe.mp hms

omit [DecidableEq α] in
/-- The odd side `pairUp (vs.rotate 1)` of an even cycle also has support exactly `vs` (each vertex
matched once): `vs.rotate 1` is a `Perm` of `vs`, so `endpoints_pairUp_of_even` gives
`endpoints (pairUp (vs.rotate 1)) = (vs.rotate 1 : Multiset) = vs`. -/
theorem endpoints_pairUp_rotate_of_even {vs : List α} (hlen : Even vs.length) :
    endpoints (pairUp (vs.rotate 1)) = (vs : Multiset α) := by
  have hlen' : Even (vs.rotate 1).length := by rw [List.length_rotate]; exact hlen
  rw [endpoints_pairUp_of_even hlen']
  exact Multiset.coe_eq_coe.mpr (vs.rotate_perm 1)

omit [DecidableEq α] in
/-- **The even cycle splits into TWO perfect matchings of its vertex set.**  For a `Nodup` NONEMPTY
vertex list `vs` of even length, `walkChords vs` is a `Perm` of `M₁ ++ M₂` where `M₁ = pairUp vs`
and `M₂ = pairUp (vs.rotate 1)` are BOTH perfect matchings of `vs` (each vertex appears exactly once
in each — `endpoints Mᵢ = (vs : Multiset)`, and `Nodup` makes every count `1`).  This is the
standalone `2`-edge-colourability of even cycles, resting only on `List`/`Multiset`
combinatorics. -/
theorem even_cycle_two_perfect_matchings {a : α} (t : List α)
    (hlen : Even (a :: t).length) :
    ∃ M₁ M₂ : List (α × α),
      (walkChords (a :: t)).Perm (M₁ ++ M₂) ∧
      endpoints M₁ = ((a :: t : List α) : Multiset α) ∧
      endpoints M₂ = ((a :: t : List α) : Multiset α) := by
  refine ⟨pairUp (a :: t), pairUp ((a :: t).rotate 1), walkChords_perm_sides t hlen, ?_, ?_⟩
  · exact endpoints_pairUp_of_even hlen
  · exact endpoints_pairUp_rotate_of_even hlen

/-- **Anti-vacuity for the two-perfect-matchings split.**  On the 4-cycle `vs = [0,1,2,3]` the split
gives the two genuine perfect matchings `M₁ = [(0,1),(2,3)]` and `M₂ = [(1,2),(3,0)]`, each covering
all four vertices once; `walkChords [0,1,2,3] ~ M₁ ++ M₂`.  A concrete non-empty instance that the
split FIRES (not vacuous). -/
theorem even_cycle_two_perfect_matchings_nonvacuous :
    ∃ M₁ M₂ : List (ℕ × ℕ),
      (walkChords [0, 1, 2, 3]).Perm (M₁ ++ M₂) ∧
      endpoints M₁ = ({0, 1, 2, 3} : Multiset ℕ) ∧
      endpoints M₂ = ({0, 1, 2, 3} : Multiset ℕ) := by
  obtain ⟨M₁, M₂, hperm, h1, h2⟩ :=
    even_cycle_two_perfect_matchings (a := 0) [1, 2, 3] (by decide)
  exact ⟨M₁, M₂, hperm, by rw [h1]; rfl, by rw [h2]; rfl⟩

end Multigraph.CycleDecomp
