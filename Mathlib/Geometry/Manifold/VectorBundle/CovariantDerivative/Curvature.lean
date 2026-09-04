/-
Copyright (c) 2025 The Mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib.Topology.FiberBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorField.LieBracket
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-! # Riemann curvature of a covariant derivative

We define the Riemann curvature of a covariant derivative (Koszul connection) `∇` on a vector
bundle `V` over a manifold `M`. In the standard notation, where `∇_X σ` denotes the covariant
derivative of a section `σ` in the direction of a vector field `X`, the curvature is
`R(X, Y) σ = ∇_X ∇_Y σ − ∇_Y ∇_X σ − ∇_{[X, Y]} σ`, where `[X, Y]` is the Lie bracket of the
vector fields `X` and `Y`.

Unlike `∇` itself — which is only a derivation in its section argument (it satisfies the Leibniz
rule) — the curvature is *tensorial*: `R(X, Y) σ` at a point `x` depends only on the values of `X`,
`Y` and `σ` at `x` (it is `C^∞`-function-linear in each of the three arguments). The Leibniz-rule
terms produced by the two covariant derivatives cancel across the three summands. This is the
defining algebraic property of the curvature, and the mathematically substantial part of this file.

## Main definitions and results

* `IsCovariantDerivativeOn.curvatureAux`: the curvature of an unbundled covariant derivative, as a
  bare function `X Y σ x`. Prefer the tensoriality lemmas below to work with it.
* `IsCovariantDerivativeOn.curvatureAux_antisymm`: the curvature is antisymmetric in its two
  vector-field arguments, `R(X, Y) σ = − R(Y, X) σ`. This holds unconditionally.
* `IsCovariantDerivativeOn.curvatureAux_self`: `R(X, X) σ = 0`.
* `IsCovariantDerivativeOn.curvatureAux_add_section`,
  `IsCovariantDerivativeOn.curvatureAux_add_left`,
  `IsCovariantDerivativeOn.curvatureAux_add_right`: additivity in each argument.
* `IsCovariantDerivativeOn.curvatureAux_smul_left`,
  `IsCovariantDerivativeOn.curvatureAux_smul_right`: `C^∞`-function-linearity (tensoriality)
  in the two vector-field arguments: `R(f • X, Y) σ = f • R(X, Y) σ` and
  `R(X, f • Y) σ = f • R(X, Y) σ`.
* `IsCovariantDerivativeOn.curvatureAux_smul_section`: `C^∞`-function-linearity (tensoriality) in
  the *section* argument, `R(X, Y) (f • σ) = f • R(X, Y) σ`. This is the second-order tensoriality
  statement; its proof exhibits the cancellation of the second-order derivative term in `f` against
  the action of the Lie bracket on functions.
* `IsCovariantDerivativeOn.curvatureAux_add_section'`,
  `IsCovariantDerivativeOn.curvatureAux_smul_section''`: the section-argument additivity and
  tensoriality with every *once-covariantly-differentiated* section hypothesis discharged from the
  smoothness of the connection (`ContMDiffCovariantDerivativeOn`) and of `σ`, isolating the two
  irreducible obstructions to the full `(1, 3)`-tensor bundling (the *global* section
  differentiability and the *directional-derivative smoothness* of `z ↦ (d% f z) (Y z)`).

### Ricci curvature (trace of the curvature, on the tangent bundle `TM`)

Specialising `V = TM`, the endomorphism `X ↦ R(X, Y) Z` of the tangent space is well-defined and
its trace is the **Ricci curvature** `Ric(Y, Z) = tr(X ↦ R(X, Y) Z)`, a `(0, 2)`-tensor.

* `IsCovariantDerivativeOn.ricciAux`: the Ricci curvature of an unbundled affine connection on `TM`,
  as a bare function `Y Z x`. Built as the `LinearMap.trace` of the (algebraic) endomorphism
  extracted from the bundled vector-field curvature `curvatureVF` (which packages the proven
  vector-field-slot tensoriality); the endomorphism is formed as a plain `LinearMap` (via
  `ContinuousLinearMap.coeLM` and `LinearMap.flip`), so the trace needs no norm on `TM_x`.
* `IsCovariantDerivativeOn.ricciAux_apply`: `Ric(Y, Z) x = tr (X₀ ↦ R(extend X₀, Y) Z x)`, expressing
  the trace directly in terms of `curvatureAux`.
* `IsCovariantDerivativeOn.ricciAux_smul_left`, `IsCovariantDerivativeOn.ricciAux_add_left`:
  `C^∞`-function-linearity (tensoriality) in the `Y` slot, `Ric(f • Y, Z) = f • Ric(Y, Z)` and
  additivity. This is *clean* (no differentiability hypotheses beyond those already baked into
  `curvatureVF`), inherited from the vector-field-slot linearity of the curvature through the trace.
* `IsCovariantDerivativeOn.ricciAux_smul_right`, `IsCovariantDerivativeOn.ricciAux_add_right`:
  tensoriality in the `Z` (section) slot. These *inherit* the section-slot hypotheses of
  `curvatureAux_smul_section''`/`curvatureAux_add_section` (a residual smoothness hypothesis: global section
  differentiability and directional-derivative smoothness), stated honestly.

## Implementation notes

We follow the conventions of `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion`,
which defines the torsion `T(X, Y) = ∇_X Y − ∇_Y X − [X, Y]` — the first-order analogue of the
curvature. Recall (see the module docstring of `CovariantDerivative.Basic`) that the covariant
derivative is stored with a nonstandard argument order: `cov σ x (X x)` is `(∇_X σ) x`. In
particular the covariant derivative in the direction of a vector field `X`, as a section, is
`fun x ↦ cov σ x (X x)`, and the curvature involves the *iterated* covariant derivative of this
section, making it a genuinely second-order construction.

Because the curvature is genuinely second-order, its tensoriality lemmas carry differentiability
hypotheses that go strictly beyond the two fields of `TensorialAt` (which records only additivity
and germ-scaling from `MDiffAt` of the section): they additionally require the differentiability of
the once-covariantly-differentiated sections `∇_X σ` (`hcov...`), and, in the section slot, the
manifold *action of the Lie bracket on functions* (`hlie`, the manifold analogue of
`VectorField.fderiv_apply_lieBracket`, currently only available in the vector-space `fderiv`
setting). Consequently the bundled `(1, 3)`-tensor upgrade — packaging `curvatureAux` into a
`TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] V x →L[𝕜] V x` via the `TensorialAt.mkHom`/`mkHom₂`
machinery (as `Torsion.torsion` does with `mkHom₂` for the first-order, section-free torsion) — is
*not yet* available: it needs (a) an auto-differentiability bridge `∇_X σ` is `C^k` for a `C^k`
connection on smooth data (the TODO recorded on `ContMDiffCovariantDerivativeOn` in
`CovariantDerivative.Basic`), so that the `hcov...` hypotheses discharge automatically, and (b) the
manifold Lie-bracket-on-functions identity to discharge `hlie` from mere `MDiffAt`. With those two
prerequisites the `TensorialAt` instances for `curvatureAux` follow and the `mkHom₂` (vector-field
slots) then `mkHom` (section slot) nesting produces the `(1, 3)`-tensor. The pointwise linearity
lemmas below are exactly the multilinearity data those instances would consume.

-/

@[expose] public noncomputable section

open Bundle Set NormedSpace FiberBundle
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {x : M}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V]

namespace IsCovariantDerivativeOn

/-- The covariant derivative of a section `σ` in the direction of a vector field `X`, as a section
of `V`. This is `(∇_X σ)` on paper; unfolding, `covDir cov X σ x = cov σ x (X x)`. -/
def covDir
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  fun x ↦ cov σ x (X x)

/-- The Riemann curvature of a covariant derivative on a vector bundle `V`, as a bare function
`X Y σ x`, where `X` and `Y` are vector fields, `σ` is a section of `V`, and `x` is a point.
On paper this is `R(X, Y) σ = ∇_X ∇_Y σ − ∇_Y ∇_X σ − ∇_{[X, Y]} σ`.
Prefer to use the tensoriality lemmas to work with this: it is `C^∞`-function-linear (and hence
pointwise) in each of `X`, `Y` and `σ`. -/
def curvatureAux
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  fun x ↦ cov (covDir cov Y σ) x (X x) - cov (covDir cov X σ) x (Y x)
    - cov σ x (VectorField.mlieBracket I X Y x)

variable {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
  {X Y : Π x : M, TangentSpace I x} {σ : Π x : M, V x}

-- The purely-algebraic curvature lemmas do not use the fibrewise topological-module structure.
omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)] in
lemma curvatureAux_apply (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) :
    curvatureAux cov X Y σ x =
      cov (covDir cov Y σ) x (X x) - cov (covDir cov X σ) x (Y x)
        - cov σ x (VectorField.mlieBracket I X Y x) :=
  rfl

omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)] in
/-- The curvature is antisymmetric in its two vector-field arguments:
`R(X, Y) σ = − R(Y, X) σ`. This holds for any function `cov`, without any assumption. -/
lemma curvatureAux_antisymm (cov) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    curvatureAux cov X Y σ = - curvatureAux cov Y X σ := by
  ext x
  rw [curvatureAux_apply, Pi.neg_apply, curvatureAux_apply,
    VectorField.mlieBracket_swap_apply, map_neg]
  abel

section
omit [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]

/-- The curvature vanishes on the diagonal: `R(X, X) σ = 0`. -/
@[simp]
lemma curvatureAux_self (cov) (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    curvatureAux cov X X σ = 0 := by
  ext x
  simp [curvatureAux_apply]

/-! ### Behaviour of `∇_X σ` under scaling of the direction

The covariant derivative in the direction `f • X` is `f • (∇_X σ)`, since `cov σ x` is linear in
the tangent vector. This requires no hypotheses and is the engine behind the
`C^∞`-linearity of the curvature in its vector-field arguments. -/

@[simp]
lemma covDir_smul_dir (cov) (f : M → 𝕜) (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    covDir cov (f • X) σ = f • covDir cov X σ := by
  ext x
  simp [covDir, map_smul]

@[simp]
lemma covDir_add_dir (cov) (X X' : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    covDir cov (X + X') σ = covDir cov X σ + covDir cov X' σ := by
  ext x
  simp [covDir, map_add]

/-! ### Tensoriality in the vector-field arguments

The curvature is `C^∞`-function-linear in each of its two vector-field arguments (unlike `∇`,
which is only a derivation in the section argument). The proof exhibits the cancellation of the
two Leibniz derivative terms produced by the two covariant derivatives. The differentiability
hypothesis `hcovX : MDiffAt (T% (covDir cov X σ)) x` is exactly the statement that `∇_X σ` is a
differentiable section at `x`; for a `C^k` connection applied to smooth data this is automatic. -/

end

/-! ### Auto-differentiability of `∇_X σ`

The `hcov...` hypotheses appearing in the tensoriality lemmas below — that the once-covariantly-
differentiated section `∇_X σ = covDir cov X σ` is differentiable at `x` — are *not* ad-hoc: they
follow automatically from the regularity of the connection together with smoothness of the data.
Concretely, if the connection is `C^n` in the sense of `ContMDiffCovariantDerivativeOn` (so that
`cov σ`, viewed as a section of `Hom(TM, V)`, is `C^n` whenever `σ` is `C^{n+1}`) and the vector
field `X` is differentiable, then `∇_X σ x = (cov σ x) (X x)` is a `C^n` section applied to a
differentiable vector field, hence differentiable. This discharges the `hcov...` hypotheses of the
tensoriality lemmas and unblocks the `(1, 3)`-tensor bundling. -/

section auto_mdiff

variable [IsManifold I 1 M] [VectorBundle 𝕜 F V]

/-- **Auto-differentiability of the directional covariant derivative** (within-a-set form).
If the connection `cov` is `C^n` on `u` (in the sense of `ContMDiffCovariantDerivativeOn`) with
`n ≠ 0`, the section `σ` is `C^{n+1}` on `u`, the vector field `X` is differentiable at `x`, and
`u` is a neighbourhood of `x`, then `∇_X σ = covDir cov X σ` is differentiable at `x`.

The proof applies the `C^n` `Hom(TM, V)`-bundle section `cov σ` (obtained from the connection
regularity) to the differentiable vector field `X`, via `MDifferentiableAt.clm_bundle_apply`. -/
lemma covDir_mdifferentiableWithinAt {u : Set M} {n : ℕ∞ω}
    (Hcov : ContMDiffCovariantDerivativeOn F n cov u) (hn : n ≠ 0)
    (hσ : CMDiff[u] (n + 1) (T% σ)) (hX : MDiffAt (T% X) x) (hu : u ∈ 𝓝 x) :
    MDiffAt (T% (covDir cov X σ)) x := by
  have hcovσ_on := (Hcov.contMDiff hσ).mdifferentiableOn hn
  have hcovσ_at := (hcovσ_on x (mem_of_mem_nhds hu)).mdifferentiableAt hu
  exact hcovσ_at.clm_bundle_apply hX

/-- **Auto-differentiability of the directional covariant derivative** (global/`univ` form).
If the connection `cov` is a `C^n` connection with `n ≠ 0`, the section `σ` is `C^{n+1}`, and the
vector field `X` is differentiable at `x`, then `∇_X σ = covDir cov X σ` is differentiable at `x`.
This is exactly the `MDiffAt (T% (covDir cov X σ)) x` hypothesis carried by the curvature
tensoriality lemmas, now discharged from connection + section smoothness. -/
lemma covDir_mdifferentiableAt {n : ℕ∞ω}
    (Hcov : ContMDiffCovariantDerivativeOn F n cov univ) (hn : n ≠ 0)
    (hσ : CMDiff (n + 1) (T% σ)) (hX : MDiffAt (T% X) x) :
    MDiffAt (T% (covDir cov X σ)) x :=
  covDir_mdifferentiableWithinAt Hcov hn hσ.contMDiffOn hX Filter.univ_mem

end auto_mdiff

variable [IsManifold I 2 M] [CompleteSpace E]

/-- `C^∞`-function-linearity (tensoriality) of the curvature in its first (left) vector-field
argument: `R(f • X, Y) σ = f • R(X, Y) σ`, pointwise at `x`.

The two Leibniz derivative terms — one from the iterated covariant derivative `∇_Y (∇_{f•X} σ)`,
the other from `∇_{[f•X, Y]} σ` via the product rule for the Lie bracket — cancel exactly. -/
lemma curvatureAux_smul_left (hcov : IsCovariantDerivativeOn F cov univ)
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x)
    (hcovX : MDiffAt (T% (covDir cov X σ)) x) :
    curvatureAux cov (f • X) Y σ x = f x • curvatureAux cov X Y σ x := by
  rw [curvatureAux_apply, curvatureAux_apply]
  -- First term: linearity of `cov _ x` in the tangent-vector slot.
  rw [show (f • X) x = f x • X x from rfl, map_smul]
  -- Second term: the direction `f • X` pulls out as `f • (∇_X σ)`, then apply Leibniz.
  rw [covDir_smul_dir, hcov.leibniz hcovX hf]
  -- Third term: product rule for the Lie bracket `[f • X, Y]`.
  rw [VectorField.mlieBracket_smul_left hf hX]
  -- Evaluate the applied continuous-linear maps; `covDir cov X σ x` is `cov σ x (X x)` by defeq.
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul, covDir]
  -- The two Leibniz derivative terms cancel.
  module

/-- `C^∞`-function-linearity (tensoriality) of the curvature in its second (right) vector-field
argument: `R(X, f • Y) σ = f • R(X, Y) σ`, pointwise at `x`.
This follows from antisymmetry and linearity in the left argument. -/
lemma curvatureAux_smul_right (hcov : IsCovariantDerivativeOn F cov univ)
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x)
    (hcovY : MDiffAt (T% (covDir cov Y σ)) x) :
    curvatureAux cov X (f • Y) σ x = f x • curvatureAux cov X Y σ x := by
  have h := hcov.curvatureAux_smul_left f Y X σ hf hY hcovY
  rw [curvatureAux_antisymm cov (f • Y) X σ, curvatureAux_antisymm cov Y X σ,
    Pi.neg_apply, Pi.neg_apply, smul_neg, neg_inj] at h
  exact h

/-- Additivity of the curvature in its first (left) vector-field argument. -/
lemma curvatureAux_add_left (hcov : IsCovariantDerivativeOn F cov univ)
    (X X' Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hcovX : MDiffAt (T% (covDir cov X σ)) x) (hcovX' : MDiffAt (T% (covDir cov X' σ)) x) :
    curvatureAux cov (X + X') Y σ x
      = curvatureAux cov X Y σ x + curvatureAux cov X' Y σ x := by
  rw [curvatureAux_apply, curvatureAux_apply, curvatureAux_apply]
  rw [Pi.add_apply, map_add, covDir_add_dir, hcov.add hcovX hcovX',
    VectorField.mlieBracket_add_left hX hX', map_add]
  simp only [add_apply]
  abel

/-- Additivity of the curvature in its second (right) vector-field argument. -/
lemma curvatureAux_add_right (hcov : IsCovariantDerivativeOn F cov univ)
    (X Y Y' : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x)
    (hcovY : MDiffAt (T% (covDir cov Y σ)) x) (hcovY' : MDiffAt (T% (covDir cov Y' σ)) x) :
    curvatureAux cov X (Y + Y') σ x
      = curvatureAux cov X Y σ x + curvatureAux cov X Y' σ x := by
  have h := hcov.curvatureAux_add_left Y Y' X σ hY hY' hcovY hcovY'
  rw [curvatureAux_antisymm cov (Y + Y') X σ, curvatureAux_antisymm cov Y X σ,
    curvatureAux_antisymm cov Y' X σ, Pi.neg_apply, Pi.neg_apply, Pi.neg_apply,
    ← neg_add, neg_inj] at h
  exact h

/-! ### Tensoriality in the vector-field arguments, with the differentiability of `∇_X σ` discharged

The following are variants of the tensoriality lemmas above whose `MDiffAt (T% (covDir cov X σ)) x`
hypotheses are discharged automatically from the smoothness of the connection (as a
`ContMDiffCovariantDerivativeOn`) and of the section `σ`, via `covDir_mdifferentiableAt`. These are
the forms consumed by the bundled `(1, 3)`-tensor upgrade (`TensorialAt.mkHom₂` on the two
vector-field slots): the caller supplies connection + data smoothness once, rather than the
per-direction differentiability of each `∇_X σ`. -/

section contMDiff_discharge

variable [VectorBundle 𝕜 F V] {n : ℕ∞ω}
  (Hcov : ContMDiffCovariantDerivativeOn F n cov univ) (hn : n ≠ 0)

include Hcov hn

/-- `C^∞`-function-linearity of the curvature in its first (left) vector-field argument,
`R(f • X, Y) σ = f • R(X, Y) σ`, with the differentiability of `∇_X σ` discharged from the
smoothness of the connection and of `σ`. -/
lemma curvatureAux_smul_left' (hcov : IsCovariantDerivativeOn F cov univ)
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hσ : CMDiff (n + 1) (T% σ)) :
    curvatureAux cov (f • X) Y σ x = f x • curvatureAux cov X Y σ x :=
  hcov.curvatureAux_smul_left f X Y σ hf hX (covDir_mdifferentiableAt Hcov hn hσ hX)

/-- `C^∞`-function-linearity of the curvature in its second (right) vector-field argument,
`R(X, f • Y) σ = f • R(X, Y) σ`, with the differentiability of `∇_Y σ` discharged from the
smoothness of the connection and of `σ`. -/
lemma curvatureAux_smul_right' (hcov : IsCovariantDerivativeOn F cov univ)
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) (hσ : CMDiff (n + 1) (T% σ)) :
    curvatureAux cov X (f • Y) σ x = f x • curvatureAux cov X Y σ x :=
  hcov.curvatureAux_smul_right f X Y σ hf hY (covDir_mdifferentiableAt Hcov hn hσ hY)

/-- Additivity of the curvature in its first (left) vector-field argument, with the differentiability
of `∇_X σ` and `∇_{X'} σ` discharged from the smoothness of the connection and of `σ`. -/
lemma curvatureAux_add_left' (hcov : IsCovariantDerivativeOn F cov univ)
    (X X' Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (hσ : CMDiff (n + 1) (T% σ)) :
    curvatureAux cov (X + X') Y σ x
      = curvatureAux cov X Y σ x + curvatureAux cov X' Y σ x :=
  hcov.curvatureAux_add_left X X' Y σ hX hX'
    (covDir_mdifferentiableAt Hcov hn hσ hX) (covDir_mdifferentiableAt Hcov hn hσ hX')

/-- Additivity of the curvature in its second (right) vector-field argument, with the
differentiability of `∇_Y σ` and `∇_{Y'} σ` discharged from the smoothness of the connection and
of `σ`. -/
lemma curvatureAux_add_right' (hcov : IsCovariantDerivativeOn F cov univ)
    (X Y Y' : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) (hσ : CMDiff (n + 1) (T% σ)) :
    curvatureAux cov X (Y + Y') σ x
      = curvatureAux cov X Y σ x + curvatureAux cov X Y' σ x :=
  hcov.curvatureAux_add_right X Y Y' σ hY hY'
    (covDir_mdifferentiableAt Hcov hn hσ hY) (covDir_mdifferentiableAt Hcov hn hσ hY')

end contMDiff_discharge

omit [IsManifold I 2 M] [CompleteSpace E] in
/-- The covariant derivative in a direction splits over a sum of sections: as sections,
`∇_X (σ + σ') = ∇_X σ + ∇_X σ'`. This requires the additivity of `cov` to hold at *every* point
(hence global differentiability of the two sections), since the whole section `covDir cov X (σ+σ')`
enters as an argument of an outer covariant derivative in the curvature. -/
lemma covDir_add_section (hcov : IsCovariantDerivativeOn F cov univ)
    (X : Π x : M, TangentSpace I x) (σ σ' : Π x : M, V x)
    (hσ : ∀ z, MDiffAt (T% σ) z) (hσ' : ∀ z, MDiffAt (T% σ') z) :
    covDir cov X (σ + σ') = covDir cov X σ + covDir cov X σ' := by
  ext z
  simp only [covDir, Pi.add_apply, hcov.add (hσ z) (hσ' z), add_apply]

omit [IsManifold I 2 M] [CompleteSpace E] in
/-- Leibniz rule for the covariant derivative in a direction, scaling the *section*: as sections,
`∇_X (f • σ) = f • ∇_X σ + (X f) • σ`, where `X f := fun z ↦ d% f z (X z)` is the directional
derivative of `f` along `X`. This is the section-slot Leibniz rule (the engine behind the
tensoriality of the curvature in its section argument), and requires the Leibniz rule of `cov` to
hold at *every* point (hence global differentiability of `f` and `σ`), since the whole section
enters an outer covariant derivative in the curvature. -/
lemma covDir_smul_section (hcov : IsCovariantDerivativeOn F cov univ)
    (f : M → 𝕜) (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x)
    (hf : ∀ z, MDiffAt f z) (hσ : ∀ z, MDiffAt (T% σ) z) :
    covDir cov X (f • σ) = f • covDir cov X σ + (fun z ↦ (d% f z) (X z)) • σ := by
  ext z
  show cov (f • σ) z (X z) = f z • cov σ z (X z) + (d% f z) (X z) • σ z
  rw [hcov.leibniz (hσ z) (hf z)]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]

omit [IsManifold I 2 M] [CompleteSpace E] in
/-- Additivity of the curvature in its section argument: `R(X, Y) (σ + σ') = R(X, Y) σ + R(X, Y) σ'`.

Unlike the additivity in the vector-field arguments, the section enters through an *iterated*
covariant derivative, so the outer additivity of `cov` requires its argument to be genuinely a sum
of sections. We therefore ask for the two sections to be differentiable at *every* point (so that
`covDir cov Y (σ + σ')` splits as a section, via `covDir_add_section`), together with the
differentiability of the four singly-covariant-differentiated sections at `x` (exactly as in
`curvatureAux_add_left`). -/
lemma curvatureAux_add_section (hcov : IsCovariantDerivativeOn F cov univ)
    (X Y : Π x : M, TangentSpace I x) (σ σ' : Π x : M, V x) {x : M}
    (hσ : ∀ z, MDiffAt (T% σ) z) (hσ' : ∀ z, MDiffAt (T% σ') z)
    (hcovYσ : MDiffAt (T% (covDir cov Y σ)) x) (hcovYσ' : MDiffAt (T% (covDir cov Y σ')) x)
    (hcovXσ : MDiffAt (T% (covDir cov X σ)) x) (hcovXσ' : MDiffAt (T% (covDir cov X σ')) x) :
    curvatureAux cov X Y (σ + σ') x
      = curvatureAux cov X Y σ x + curvatureAux cov X Y σ' x := by
  rw [curvatureAux_apply, curvatureAux_apply, curvatureAux_apply]
  -- Split the two iterated covariant derivatives using additivity of the outer `cov`,
  -- after rewriting `covDir cov · (σ + σ')` as a sum of sections.
  rw [hcov.covDir_add_section Y σ σ' hσ hσ', hcov.add hcovYσ hcovYσ',
    hcov.covDir_add_section X σ σ' hσ hσ', hcov.add hcovXσ hcovXσ']
  -- Split the third (bracket) term using additivity of `cov` at `x`.
  rw [hcov.add (hσ x) (hσ' x)]
  simp only [add_apply]
  abel

omit [IsManifold I 2 M] [CompleteSpace E] in
/-- `C^∞`-function-linearity (tensoriality) of the curvature in its *section* argument:
`R(X, Y) (f • σ) = f • R(X, Y) σ`, pointwise at `x`.

This is the substantive tensoriality statement: expanding the two iterated covariant derivatives via
the Leibniz rule produces both first-order derivative terms in `f` (which cancel exactly as in the
vector-field slots) and a genuinely *second-order* derivative term in `f` multiplying `σ x`. That
second-order term is `(d% (Y f) x (X x) − d% (X f) x (Y x) − d% f x ([X, Y] x)) • σ x` (with
`X f := fun z ↦ d% f z (X z)` the directional derivative of `f` along `X`), and it vanishes exactly
by the *action of the Lie bracket on functions*:
`d% f x ([X, Y] x) = d% (fun z ↦ d% f z (Y z)) x (X x) − d% (fun z ↦ d% f z (X z)) x (Y x)`.
This is the manifold analogue of `VectorField.fderiv_apply_lieBracket`; it holds for any `C²`
function `f` (symmetry of the second manifold derivative). Mathlib currently has this identity only
in the vector-space (`fderiv`) setting — see `Mathlib.Analysis.Calculus.VectorField` — so we take it
as the explicit hypothesis `hlie` here; supplying the manifold version discharges it. -/
lemma curvatureAux_smul_section (hcov : IsCovariantDerivativeOn F cov univ)
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hf : ∀ z, MDiffAt f z) (hσ : ∀ z, MDiffAt (T% σ) z)
    (hcovYσ : MDiffAt (T% (covDir cov Y σ)) x)
    (hcovXσ : MDiffAt (T% (covDir cov X σ)) x)
    (hfYσ : MDiffAt (T% ((fun z ↦ (d% f z) (Y z)) • σ)) x)
    (hfXσ : MDiffAt (T% ((fun z ↦ (d% f z) (X z)) • σ)) x)
    (hfcovYσ : MDiffAt (T% (f • covDir cov Y σ)) x)
    (hfcovXσ : MDiffAt (T% (f • covDir cov X σ)) x)
    (hYf : MDiffAt (fun z ↦ (d% f z) (Y z)) x) (hXf : MDiffAt (fun z ↦ (d% f z) (X z)) x)
    (hlie : (d% f x) (VectorField.mlieBracket I X Y x)
      = (d% fun z ↦ (d% f z) (Y z)) x (X x) - (d% fun z ↦ (d% f z) (X z)) x (Y x)) :
    curvatureAux cov X Y (f • σ) x = f x • curvatureAux cov X Y σ x := by
  rw [curvatureAux_apply, curvatureAux_apply]
  -- Expand each iterated covariant derivative: the direction-scaling of the section produces a
  -- first-order term `f • ∇σ` and a first-derivative term `(·f) • σ`.
  rw [hcov.covDir_smul_section f Y σ hf hσ, hcov.covDir_smul_section f X σ hf hσ]
  -- Split each outer covariant derivative (additivity), then apply the Leibniz rule to both pieces.
  rw [hcov.add hfcovYσ hfYσ, hcov.add hfcovXσ hfXσ,
      hcov.leibniz hcovYσ (hf x), hcov.leibniz hcovXσ (hf x),
      hcov.leibniz (hσ x) hYf, hcov.leibniz (hσ x) hXf]
  -- Also expand the bracket (third) term via Leibniz.
  rw [hcov.leibniz (hσ x) (hf x)]
  simp only [covDir, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_sub]
  -- The first-order derivative terms in `f` cancel across the antisymmetrised combination; the
  -- remaining second-order term multiplying `σ x` vanishes by the Lie-bracket-on-functions
  -- identity `hlie`.
  rw [hlie]
  module

/-- `C^∞`-function-linearity (tensoriality) of the curvature in its *section* argument,
`R(X, Y) (f • σ) = f • R(X, Y) σ`, with the manifold *action of the Lie bracket on functions*
discharged automatically. This is `curvatureAux_smul_section` with the explicit hypothesis `hlie`
replaced by the differentiability data it needs: `f` is `C²` (as a `ContMDiffAt` of order
`n ≥ minSmoothness 𝕜 2`) and the vector fields `X`, `Y` are `MDiffAt` — from which the manifold
Lie-bracket-on-functions identity `VectorField.apply_mlieBracket` produces `hlie`. -/
lemma curvatureAux_smul_section' {n : ℕ∞ω} [IsManifold I n M]
    (hcov : IsCovariantDerivativeOn F cov univ)
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hf : ∀ z, ContMDiffAt I 𝓘(𝕜, 𝕜) n f z) (hn : minSmoothness 𝕜 2 ≤ n)
    (hσ : ∀ z, MDiffAt (T% σ) z)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hcovYσ : MDiffAt (T% (covDir cov Y σ)) x)
    (hcovXσ : MDiffAt (T% (covDir cov X σ)) x)
    (hfYσ : MDiffAt (T% ((fun z ↦ (d% f z) (Y z)) • σ)) x)
    (hfXσ : MDiffAt (T% ((fun z ↦ (d% f z) (X z)) • σ)) x)
    (hfcovYσ : MDiffAt (T% (f • covDir cov Y σ)) x)
    (hfcovXσ : MDiffAt (T% (f • covDir cov X σ)) x)
    (hYf : MDiffAt (fun z ↦ (d% f z) (Y z)) x) (hXf : MDiffAt (fun z ↦ (d% f z) (X z)) x) :
    curvatureAux cov X Y (f • σ) x = f x • curvatureAux cov X Y σ x :=
  curvatureAux_smul_section hcov f X Y σ (fun z ↦ (hf z).mdifferentiableAt
    (lt_of_lt_of_le two_pos (le_minSmoothness.trans hn)).ne') hσ hcovYσ hcovXσ hfYσ hfXσ
    hfcovYσ hfcovXσ hYf hXf
    (VectorField.apply_mlieBracket hf hn hX hY hXf hYf)

/-! ### Tensoriality in the section argument, with the once-covariant-derivative differentiability
discharged

The following are variants of the second-order section lemmas `curvatureAux_add_section` and
`curvatureAux_smul_section'` in which every *once-covariantly-differentiated* section hypothesis
(`hcovYσ`, `hcovXσ`, and, in the scaling lemma, the two products `hfcovYσ`, `hfcovXσ`) is discharged
automatically from the smoothness of the connection (as a `ContMDiffCovariantDerivativeOn`) and of
`σ`, via `covDir_mdifferentiableAt`. This isolates the *genuinely irreducible* second-order data:
in the additivity lemma, only the *global* differentiability of the two sections survives (the
section enters an outer covariant derivative, so its germ — not just its value at `x` — is needed);
in the scaling lemma, the surviving hypotheses are exactly the two *directional-derivative
smoothness* facts `hYf`, `hXf` (that `z ↦ (d% f z) (Y z)` and `z ↦ (d% f z) (X z)` are
differentiable at `x`), for which Mathlib currently has no lemma in the `mvfderiv` (`d%`) form —
see the note preceding the vector-field bundle below. -/

section section_discharge

variable [VectorBundle 𝕜 F V] {n : ℕ∞ω}
  (Hcov : ContMDiffCovariantDerivativeOn F n cov univ) (hn : n ≠ 0)

include Hcov hn

/-- Additivity of the curvature in its *section* argument, with the differentiability of the four
once-covariantly-differentiated sections discharged from the smoothness of the connection and of
`σ`, `σ'`. Only the *global* differentiability of the two sections (`hσ`, `hσ'`) survives, since the
section enters an outer covariant derivative and hence its germ, not merely its value at `x`, is
required. -/
lemma curvatureAux_add_section' (hcov : IsCovariantDerivativeOn F cov univ)
    (X Y : Π x : M, TangentSpace I x) (σ σ' : Π x : M, V x) {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hσ : ∀ z, MDiffAt (T% σ) z) (hσ' : ∀ z, MDiffAt (T% σ') z)
    (hσC : CMDiff (n + 1) (T% σ)) (hσ'C : CMDiff (n + 1) (T% σ')) :
    curvatureAux cov X Y (σ + σ') x
      = curvatureAux cov X Y σ x + curvatureAux cov X Y σ' x :=
  hcov.curvatureAux_add_section X Y σ σ' hσ hσ'
    (covDir_mdifferentiableAt Hcov hn hσC hY) (covDir_mdifferentiableAt Hcov hn hσ'C hY)
    (covDir_mdifferentiableAt Hcov hn hσC hX) (covDir_mdifferentiableAt Hcov hn hσ'C hX)

/-- `C^∞`-function-linearity of the curvature in its *section* argument,
`R(X, Y) (f • σ) = f • R(X, Y) σ`, with every *once-covariantly-differentiated* section hypothesis
(`hcovYσ`, `hcovXσ`, `hfcovYσ`, `hfcovXσ`) discharged from the smoothness of the connection and of
`σ`. The surviving hypotheses are the *directional-derivative smoothness* facts `hYf`, `hXf` (from
which the two products `hfYσ`, `hfXσ` follow by `MDifferentiableAt.smul_section`), which precisely
locate the remaining Mathlib gap. -/
lemma curvatureAux_smul_section'' [IsManifold I n M]
    (hcov : IsCovariantDerivativeOn F cov univ)
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hf : ∀ z, ContMDiffAt I 𝓘(𝕜, 𝕜) n f z) (hmn : minSmoothness 𝕜 2 ≤ n)
    (hσ : ∀ z, MDiffAt (T% σ) z) (hσC : CMDiff (n + 1) (T% σ))
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hYf : MDiffAt (fun z ↦ (d% f z) (Y z)) x) (hXf : MDiffAt (fun z ↦ (d% f z) (X z)) x) :
    curvatureAux cov X Y (f • σ) x = f x • curvatureAux cov X Y σ x :=
  have hne : n ≠ 0 := (lt_of_lt_of_le two_pos (le_minSmoothness.trans hmn)).ne'
  have hfx : MDiffAt f x := (hf x).mdifferentiableAt hne
  have hσx : MDiffAt (T% σ) x := hσ x
  have hcovYσ : MDiffAt (T% (covDir cov Y σ)) x := covDir_mdifferentiableAt Hcov hn hσC hY
  have hcovXσ : MDiffAt (T% (covDir cov X σ)) x := covDir_mdifferentiableAt Hcov hn hσC hX
  hcov.curvatureAux_smul_section' f X Y σ hf hmn hσ hX hY hcovYσ hcovXσ
    (hYf.smul_section hσx) (hXf.smul_section hσx)
    (hfx.smul_section hcovYσ) (hfx.smul_section hcovXσ) hYf hXf

end section_discharge

/-! ### Bundling the two vector-field slots into a `(1, 2)`-in-vector-fields tensor

We can now package `curvatureAux cov · · σ x` — with the section `σ` held fixed as a plain argument
— into a bundled continuous bilinear map
`TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] V x`, exactly as `Torsion.torsion` does for the
first-order torsion, via `TensorialAt.mkHom₂`. The two `TensorialAt` instances feed on the
the discharged vector-field tensoriality lemmas (`curvatureAux_smul_left'`/`_right'` and
`curvatureAux_add_left'`/`_right'`), whose `MDiffAt (T% (covDir cov · σ)) x` hypotheses are
supplied automatically from the smoothness of the connection (`Hcov`, `hn`) and of `σ`
(`hσ : CMDiff (n + 1) (T% σ)`).

The remaining *section* slot cannot be folded in by the same construction: `TensorialAt` in the
section argument would require the pointwise scaling/additivity equalities from mere
`MDiffAt f x` / `MDiffAt (T% σ) x`, but the second-order section lemmas are genuinely second-order.
The `contMDiff`-discharged forms `curvatureAux_add_section'` and `curvatureAux_smul_section''`
(above) reduce the residual data to the two *irreducible* obstructions: (i) the *global*
differentiability `∀ z, MDiffAt (T% σ) z` (the section enters an outer covariant derivative, so its
germ — not just its value at `x` — is needed, and this is strictly stronger than the pointwise
`MDiffAt (T% σ) x` that the `TensorialAt.add`/`smul` fields provide); and (ii) the *directional-
derivative smoothness* facts `hYf`, `hXf` — `MDiffAt (fun z ↦ (d% f z) (Y z)) x` — for which Mathlib
currently has no lemma in the `mvfderiv` (`d%`) form. The vector-space primitive
`ContMDiffAt.mfderiv_apply` produces the *chart-transported* (`inTangentCoordinates`) bundled
derivative, which agrees with the raw pointwise `mvfderiv`-applied section only at the base point,
not on a neighbourhood; bridging the two on a neighbourhood (as in
`VectorField.mvfderiv_apply_mvfderiv_apply_eq_fderivWithin_fderivWithin`) is a self-contained
follow-up. With those two obstructions removed, the section-slot `TensorialAt` and the `mkHom`-then-
`mkHom₂` nesting produce the full `(1, 3)`-tensor `TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜]
V x →L[𝕜] V x`; see the module docstring. -/

section vectorField_bundle

variable [VectorBundle 𝕜 F V] {n : ℕ∞ω}
  (Hcov : ContMDiffCovariantDerivativeOn F n cov univ) (hn : n ≠ 0)

include Hcov hn

/-- Tensoriality of the curvature in its first (left) vector-field slot, packaged as a
`TensorialAt` instance (the section `σ` held fixed), with the differentiability of `∇_· σ`
discharged from the smoothness of the connection and of `σ`. This is the datum consumed by the
first argument of `TensorialAt.mkHom₂` when bundling the two vector-field slots. -/
lemma curvatureAux_tensorial_left (hcov : IsCovariantDerivativeOn F cov univ)
    (Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (hσ : CMDiff (n + 1) (T% σ)) (x : M) :
    TensorialAt I E (curvatureAux cov · Y σ x) x where
  smul hf hX := hcov.curvatureAux_smul_left' Hcov hn _ _ _ _ hf hX hσ
  add hX hX' := hcov.curvatureAux_add_left' Hcov hn _ _ _ _ hX hX' hσ

/-- Tensoriality of the curvature in its second (right) vector-field slot, packaged as a
`TensorialAt` instance (the section `σ` held fixed), with the differentiability of `∇_· σ`
discharged from the smoothness of the connection and of `σ`. This is the datum consumed by the
second argument of `TensorialAt.mkHom₂` when bundling the two vector-field slots. -/
lemma curvatureAux_tensorial_right (hcov : IsCovariantDerivativeOn F cov univ)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (hσ : CMDiff (n + 1) (T% σ)) (x : M) :
    TensorialAt I E (curvatureAux cov X · σ x) x where
  smul hf hY := hcov.curvatureAux_smul_right' Hcov hn _ _ _ _ hf hY hσ
  add hY hY' := hcov.curvatureAux_add_right' Hcov hn _ _ _ _ hY hY' hσ

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- The curvature of a covariant derivative on a vector bundle `V`, bundled — for a fixed section
`σ` — as a continuous bilinear map in its two vector-field arguments:
`TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] V x`. This is the `(1, 2)`-in-vector-fields tensor,
built with `TensorialAt.mkHom₂` from the vector-field tensoriality of `curvatureAux`, mirroring
`Torsion.torsion`. The full `(1, 3)`-tensor (folding in the section slot with `mkHom`) awaits the
section-slot differentiability bridges recorded in the module docstring. -/
noncomputable def curvatureVF (hcov : IsCovariantDerivativeOn F cov univ)
    (σ : Π x : M, V x) (hσ : CMDiff (n + 1) (T% σ)) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] V x :=
  TensorialAt.mkHom₂ (curvatureAux cov · · σ x) _
    (fun Y _ ↦ hcov.curvatureAux_tensorial_left Hcov hn Y σ hσ x)
    (fun X _ ↦ hcov.curvatureAux_tensorial_right Hcov hn X σ hσ x)

/-- Evaluation of the bundled vector-field curvature: `curvatureVF … x (X x) (Y x)` recovers the bare
`curvatureAux cov X Y σ x`, for differentiable vector fields `X`, `Y`. -/
lemma curvatureVF_apply (hcov : IsCovariantDerivativeOn F cov univ)
    (σ : Π x : M, V x) (hσ : CMDiff (n + 1) (T% σ)) {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x) :
    curvatureVF Hcov hn hcov σ hσ x (X x) (Y x) = curvatureAux cov X Y σ x :=
  TensorialAt.mkHom₂_apply _ _ hX hY

/-- Evaluation of the bundled vector-field curvature on `extend`ed tangent vectors. -/
lemma curvatureVF_apply_eq_extend (hcov : IsCovariantDerivativeOn F cov univ)
    (σ : Π x : M, V x) (hσ : CMDiff (n + 1) (T% σ)) {x : M} (X₀ Y₀ : TangentSpace I x) :
    curvatureVF Hcov hn hcov σ hσ x X₀ Y₀ =
      curvatureAux cov (extend E X₀) (extend E Y₀) σ x :=
  TensorialAt.mkHom₂_apply_eq_extend _ _ X₀ Y₀

end vectorField_bundle

/-! ### Ricci curvature: the trace of the curvature endomorphism on `TM`

Specialising to the tangent bundle `V = TM`, the curvature `R(X, Y) Z` lands back in `TM_x`, so for
fixed vector fields `Y`, `Z` the assignment `X ↦ R(X, Y) Z` is an endomorphism of `TM_x`, and its
trace is the Ricci curvature `Ric(Y, Z)`. We form that endomorphism as a plain `LinearMap` (the
algebraic `flip` of the bundled bilinear curvature `curvatureVF`, whose codomain `CLM` is turned
into a `LinearMap` by `ContinuousLinearMap.coeLM`); this deliberately avoids
`ContinuousLinearMap.flip`, which would demand a norm on `TM_x` that the tangent-space type synonym
does not carry. -/

section ricci

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [VectorBundle 𝕜 E (TangentSpace I : M → Type _)]
  {covT : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)}
  {n : ℕ∞ω}

/-- The endomorphism `X₀ ↦ R(X₀, Y) Z` of the tangent space `TM_x`, as a plain `LinearMap`,
extracted from the bundled vector-field curvature `curvatureVF`. The trace of this endomorphism is
`ricciAux`. Formed via `ContinuousLinearMap.coeLM` (turning the inner `CLM` into a `LinearMap`) and
the algebraic `LinearMap.flip`, so no norm on `TM_x` is required. -/
noncomputable def ricciEndo (Hcov : ContMDiffCovariantDerivativeOn E n covT univ) (hn : n ≠ 0)
    (hcov : IsCovariantDerivativeOn E covT univ)
    (Y Z : Π x : M, TangentSpace I x) (hZ : CMDiff (n + 1) (T% Z)) (x : M) :
    TangentSpace I x →ₗ[𝕜] TangentSpace I x :=
  ((ContinuousLinearMap.coeLM 𝕜).comp
    (curvatureVF Hcov hn hcov Z hZ x).toLinearMap).flip (Y x)

/-- The Ricci curvature of an unbundled affine connection `covT` on the tangent bundle `TM`, as a
bare function `Y Z x`. On paper `Ric(Y, Z) = tr (X ↦ R(X, Y) Z)`. Prefer `ricciAux_apply` and the
tensoriality lemmas to work with it. -/
noncomputable def ricciAux (Hcov : ContMDiffCovariantDerivativeOn E n covT univ) (hn : n ≠ 0)
    (hcov : IsCovariantDerivativeOn E covT univ)
    (Y Z : Π x : M, TangentSpace I x) (hZ : CMDiff (n + 1) (T% Z)) (x : M) : 𝕜 :=
  LinearMap.trace 𝕜 (TangentSpace I x) (ricciEndo Hcov hn hcov Y Z hZ x)

variable (Hcov : ContMDiffCovariantDerivativeOn E n covT univ) (hn : n ≠ 0)
  (hcov : IsCovariantDerivativeOn E covT univ)

/-- The Ricci endomorphism evaluated on a tangent vector `X₀`: `(X₀ ↦ R(X₀, Y) Z) X₀` equals the
bundled curvature `curvatureVF … x X₀ (Y x)`. -/
@[simp]
lemma ricciEndo_apply (Y Z : Π x : M, TangentSpace I x) (hZ : CMDiff (n + 1) (T% Z)) (x : M)
    (X₀ : TangentSpace I x) :
    ricciEndo Hcov hn hcov Y Z hZ x X₀ = curvatureVF Hcov hn hcov Z hZ x X₀ (Y x) := by
  simp [ricciEndo, LinearMap.flip_apply, ContinuousLinearMap.coeLM]

/-- The Ricci endomorphism, evaluated on a tangent vector `X₀`, expressed through the bare curvature
`curvatureAux` on `extend`ed fields: `(X₀ ↦ R(X₀, Y) Z) X₀ = R(extend X₀, Y) Z x`. -/
lemma ricciEndo_apply_eq_extend (Y Z : Π x : M, TangentSpace I x) (hZ : CMDiff (n + 1) (T% Z))
    (x : M) (X₀ : TangentSpace I x) :
    ricciEndo Hcov hn hcov Y Z hZ x X₀ =
      curvatureAux covT (extend E X₀) (extend E (Y x)) Z x := by
  rw [ricciEndo_apply, curvatureVF_apply_eq_extend]

/-- `ricciAux` as the trace of the genuine curvature endomorphism `X₀ ↦ R(extend X₀, Y) Z x`. This
reproduces the trace of the honest curvature, exhibiting `Ric` as `tr R(·, Y) Z` — the non-vacuity
of the definition (it is not identically the zero functional by fiat: it is the trace of the
curvature, which `curvatureVF_apply` shows reproduces `R`). -/
lemma ricciAux_apply (Y Z : Π x : M, TangentSpace I x) (hZ : CMDiff (n + 1) (T% Z)) (x : M) :
    ricciAux Hcov hn hcov Y Z hZ x =
      LinearMap.trace 𝕜 (TangentSpace I x)
        (((ContinuousLinearMap.coeLM 𝕜).comp
          (curvatureVF Hcov hn hcov Z hZ x).toLinearMap).flip (Y x)) :=
  rfl

/-! #### Tensoriality of `Ric` in the `Y` slot (clean)

`C^∞`-function-linearity and additivity in the first argument follow directly from the linearity of
`flip _` in its (first) tangent-vector argument and the linearity of `LinearMap.trace`, with no
differentiability hypotheses beyond those already carried by `curvatureVF`. -/

/-- `C^∞`-function-linearity (tensoriality) of the Ricci curvature in its first argument:
`Ric(f • Y, Z) = f • Ric(Y, Z)`, pointwise at `x`. Clean: no extra differentiability hypotheses. -/
lemma ricciAux_smul_left (f : M → 𝕜) (Y Z : Π x : M, TangentSpace I x)
    (hZ : CMDiff (n + 1) (T% Z)) (x : M) :
    ricciAux Hcov hn hcov (f • Y) Z hZ x = f x • ricciAux Hcov hn hcov Y Z hZ x := by
  rw [ricciAux, ricciAux, ricciEndo, ricciEndo]
  rw [show (f • Y) x = f x • Y x from rfl, map_smul, map_smul]

/-- Additivity of the Ricci curvature in its first argument:
`Ric(Y + Y', Z) = Ric(Y, Z) + Ric(Y', Z)`, pointwise at `x`. Clean. -/
lemma ricciAux_add_left (Y Y' Z : Π x : M, TangentSpace I x)
    (hZ : CMDiff (n + 1) (T% Z)) (x : M) :
    ricciAux Hcov hn hcov (Y + Y') Z hZ x
      = ricciAux Hcov hn hcov Y Z hZ x + ricciAux Hcov hn hcov Y' Z hZ x := by
  rw [ricciAux, ricciAux, ricciAux, ricciEndo, ricciEndo, ricciEndo]
  rw [show (Y + Y') x = Y x + Y' x from rfl, map_add, map_add]

/-! #### Tensoriality of `Ric` in the `Z` slot (inherits the section-slot hypotheses)

Tensoriality in the second (section) argument reduces, entrywise over the trace, to the section-slot
tensoriality of the curvature (`curvatureAux_smul_section''`, `curvatureAux_add_section`) applied on
`extend`ed tangent vectors. It therefore *inherits* the residual section-slot
hypotheses: the smoothness of `f` and `Z`, and — crucially — the *directional-derivative smoothness*
facts for every `extend`ed basis direction. We state these honestly and make no claim of an
unconditional `Z`-slot tensor. -/

/-- `C^∞`-function-linearity (tensoriality) of the Ricci curvature in its second (section) argument:
`Ric(Y, f • Z) = f • Ric(Y, Z)`, pointwise at `x`.

Unlike the `Y`-slot version, this is **not** unconditional: the section enters an iterated covariant
derivative, so the proof inherits the section-slot hypotheses of `curvatureAux_smul_section''` —
here specialised to the `extend`ed tangent vectors summed over by the trace. The surviving residual
data are the *directional-derivative smoothness* facts `hYf`, `hXf` for the `extend`ed directions
(the section-slot obstruction), for which Mathlib currently has no lemma in the `mvfderiv` (`d%`) form. -/
lemma ricciAux_smul_right [IsManifold I n M]
    (f : M → 𝕜) (Y Z : Π x : M, TangentSpace I x)
    (hZ : CMDiff (n + 1) (T% Z)) (hfZ : CMDiff (n + 1) (T% (f • Z))) (x : M)
    (hf : ∀ z, ContMDiffAt I 𝓘(𝕜, 𝕜) n f z) (hmn : minSmoothness 𝕜 2 ≤ n)
    (hσ : ∀ z, MDiffAt (T% Z) z)
    (hYf : MDiffAt (fun z ↦ (d% f z) (extend E (Y x) z)) x)
    (hXf : ∀ X₀ : TangentSpace I x, MDiffAt (fun z ↦ (d% f z) (extend E X₀ z)) x) :
    ricciAux Hcov hn hcov Y (f • Z) hfZ x = f x • ricciAux Hcov hn hcov Y Z hZ x := by
  rw [ricciAux, ricciAux, ← map_smul (LinearMap.trace 𝕜 (TangentSpace I x))]
  congr 1
  ext X₀
  rw [ricciEndo_apply_eq_extend, LinearMap.smul_apply, ricciEndo_apply_eq_extend]
  exact hcov.curvatureAux_smul_section'' Hcov hn f (extend E X₀) (extend E (Y x)) Z
    hf hmn hσ hZ (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
    hYf (hXf X₀)

/-- Additivity of the Ricci curvature in its second (section) argument:
`Ric(Y, Z + Z') = Ric(Y, Z) + Ric(Y, Z')`, pointwise at `x`.

Inherits the section-slot hypotheses of `curvatureAux_add_section` (specialised to the `extend`ed
directions summed over by the trace): the *global* differentiability of `Z`, `Z'` (the section
enters an outer covariant derivative) together with the once-covariantly-differentiated section
smoothness, discharged from the connection smoothness. -/
lemma ricciAux_add_right (Y Z Z' : Π x : M, TangentSpace I x)
    (hZ : CMDiff (n + 1) (T% Z)) (hZ' : CMDiff (n + 1) (T% Z'))
    (hZZ' : CMDiff (n + 1) (T% (Z + Z'))) (x : M)
    (hσ : ∀ z, MDiffAt (T% Z) z) (hσ' : ∀ z, MDiffAt (T% Z') z) :
    ricciAux Hcov hn hcov Y (Z + Z') hZZ' x
      = ricciAux Hcov hn hcov Y Z hZ x + ricciAux Hcov hn hcov Y Z' hZ' x := by
  rw [ricciAux, ricciAux, ricciAux, ← map_add (LinearMap.trace 𝕜 (TangentSpace I x))]
  congr 1
  ext X₀
  rw [ricciEndo_apply_eq_extend, LinearMap.add_apply,
    ricciEndo_apply_eq_extend, ricciEndo_apply_eq_extend]
  exact hcov.curvatureAux_add_section (extend E X₀) (extend E (Y x)) Z Z' hσ hσ'
    (covDir_mdifferentiableAt Hcov hn hZ (mdifferentiableAt_extend ..))
    (covDir_mdifferentiableAt Hcov hn hZ' (mdifferentiableAt_extend ..))
    (covDir_mdifferentiableAt Hcov hn hZ (mdifferentiableAt_extend ..))
    (covDir_mdifferentiableAt Hcov hn hZ' (mdifferentiableAt_extend ..))

end ricci

/-! ### Scalar curvature and the Einstein tensor

Given a Riemannian metric on the tangent bundle — i.e. a `RiemannianBundle` structure, which endows
each tangent space `TangentSpace I x` with an `InnerProductSpace ℝ` structure `g x` — the *scalar
curvature* `R(x)` is the metric trace `tr_g(Ric)` of the Ricci bilinear form. Concretely, over any
`g`-orthonormal basis `e` of `TangentSpace I x`,
`R(x) = ∑ i, Ric(e i, e i)`,
a metric-independent-of-basis quantity (the metric trace parallels `LinearMap.trace_eq_sum_inner`).
We realise it with the canonical `stdOrthonormalBasis ℝ (TangentSpace I x)`.

Because `ricciAux` (the Ricci curvature) contracts the *first* curvature index and takes vector-field
arguments, evaluating `Ric` on the tangent basis vectors `e i` requires lifting each `e i` to a
vector field. We use the canonical `extend E (e i)`, and — as the Ricci `Z`-slot carries a global
`C^{n+1}` section-smoothness hypothesis (a residual smoothness hypothesis) — the definition carries a frame
smoothness hypothesis `hframe : ∀ i, CMDiff (n + 1) (T% (extend E (e i)))`. The *value* is
independent of the smoothness proof term (`ContMDiff` is a `Prop`).

We work with `𝕜 = ℝ` here, since the Riemannian metric API (`RiemannianMetric`, `RiemannianBundle`)
is real-valued (`InnerProductSpace ℝ`). The scalar-curvature/Einstein constructions are the metric
trace of *any* Ricci tensor of *any* affine connection `covT` on `TM`; we do **not** specialise to
the Levi-Civita connection (that is the physically-distinguished choice whose curvature is the
Riemann tensor, but the metric-trace definition needs only a metric and a Ricci tensor). -/

section scalarCurvature

open scoped Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [FiniteDimensional ℝ E]
  [VectorBundle ℝ E (TangentSpace I : M → Type _)]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {covT : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
  {n : ℕ∞ω}

/-- The scalar curvature `R(x) = tr_g(Ric)` of an affine connection `covT` on the tangent bundle
`TM`, traced with a Riemannian metric `g` (supplied by the `RiemannianBundle` instance): the metric
trace of the Ricci bilinear form, realised as the sum `∑ i, Ric(e i, e i)` over the canonical
`g`-orthonormal basis `e = stdOrthonormalBasis ℝ (TangentSpace I x)`.

Honest hypotheses: the metric enters through `RiemannianBundle`; and, since `ricciAux` carries a
`C^{n+1}` smoothness hypothesis in its section (`Z`) slot, the definition carries a frame smoothness
hypothesis `hframe`, one `CMDiff (n + 1)` fact per extended orthonormal basis field. The value does
not depend on the proof term (`ContMDiff` is a `Prop`). -/
noncomputable def scalarCurvature
    (Hcov : ContMDiffCovariantDerivativeOn E n covT univ) (hn : n ≠ 0)
    (hcov : IsCovariantDerivativeOn E covT univ) (x : M)
    (hframe : ∀ i, CMDiff (n + 1) (T% (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)))) :
    ℝ :=
  ∑ i, ricciAux Hcov hn hcov
    (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
    (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) (hframe i) x

/-- Unfolding lemma for `scalarCurvature`: it is the sum of the Ricci curvatures along the diagonal
of the canonical orthonormal frame, exhibiting `R = ∑ i Ric(e i, e i) = tr_g(Ric)`. This makes the
non-vacuity manifest: it is the honest metric trace of `ricciAux`, whose non-vacuity is recorded on
`ricciAux_apply` (the trace of the genuine curvature endomorphism). -/
lemma scalarCurvature_apply
    (Hcov : ContMDiffCovariantDerivativeOn E n covT univ) (hn : n ≠ 0)
    (hcov : IsCovariantDerivativeOn E covT univ) (x : M)
    (hframe : ∀ i, CMDiff (n + 1) (T% (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)))) :
    scalarCurvature Hcov hn hcov x hframe =
      ∑ i, ricciAux Hcov hn hcov
        (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
        (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) (hframe i) x :=
  rfl

/-- The Einstein tensor `G(Y, Z) = Ric(Y, Z) − ½ R g(Y, Z)`, as a bare function `Y Z x`, where
`Ric = ricciAux` is the Ricci curvature, `R = scalarCurvature` is the scalar curvature, and
`g(Y, Z) x = ⟪Y x, Z x⟫` is the Riemannian metric on `TangentSpace I x` (from `RiemannianBundle`).

Honest hypotheses: `hZ` is the Ricci `Z`-slot smoothness of the field `Z`; `hframe` is the frame
smoothness for the scalar-curvature trace (see `scalarCurvature`). -/
noncomputable def einsteinTensor
    (Hcov : ContMDiffCovariantDerivativeOn E n covT univ) (hn : n ≠ 0)
    (hcov : IsCovariantDerivativeOn E covT univ)
    (Y Z : Π x : M, TangentSpace I x) (hZ : CMDiff (n + 1) (T% Z)) (x : M)
    (hframe : ∀ i, CMDiff (n + 1) (T% (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)))) :
    ℝ :=
  ricciAux Hcov hn hcov Y Z hZ x
    - (1 / 2) * scalarCurvature Hcov hn hcov x hframe * inner ℝ (Y x) (Z x)

/-- Unfolding lemma for `einsteinTensor`: `G(Y, Z) = Ric(Y, Z) − ½ R g(Y, Z)`. -/
lemma einsteinTensor_apply
    (Hcov : ContMDiffCovariantDerivativeOn E n covT univ) (hn : n ≠ 0)
    (hcov : IsCovariantDerivativeOn E covT univ)
    (Y Z : Π x : M, TangentSpace I x) (hZ : CMDiff (n + 1) (T% Z)) (x : M)
    (hframe : ∀ i, CMDiff (n + 1) (T% (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)))) :
    einsteinTensor Hcov hn hcov Y Z hZ x hframe =
      ricciAux Hcov hn hcov Y Z hZ x
        - (1 / 2) * scalarCurvature Hcov hn hcov x hframe * inner ℝ (Y x) (Z x) :=
  rfl

/-- `C^∞`-function-linearity (tensoriality) of the Einstein tensor in its first argument:
`G(f • Y, Z) = f • G(Y, Z)`, pointwise at `x`. Clean: follows from the clean `Y`-slot tensoriality of
Ricci (`ricciAux_smul_left`) and the linearity of the metric in its first argument
(`real_inner_smul_left`); no extra differentiability hypotheses beyond those of `ricciAux`. -/
lemma einsteinTensor_smul_left
    (Hcov : ContMDiffCovariantDerivativeOn E n covT univ) (hn : n ≠ 0)
    (hcov : IsCovariantDerivativeOn E covT univ)
    (f : M → ℝ) (Y Z : Π x : M, TangentSpace I x) (hZ : CMDiff (n + 1) (T% Z)) (x : M)
    (hframe : ∀ i, CMDiff (n + 1) (T% (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)))) :
    einsteinTensor Hcov hn hcov (f • Y) Z hZ x hframe
      = f x • einsteinTensor Hcov hn hcov Y Z hZ x hframe := by
  rw [einsteinTensor, einsteinTensor, ricciAux_smul_left]
  rw [show (f • Y) x = f x • Y x from rfl, real_inner_smul_left]
  simp only [smul_eq_mul]
  ring

/-- Additivity of the Einstein tensor in its first argument:
`G(Y + Y', Z) = G(Y, Z) + G(Y', Z)`, pointwise at `x`. Clean: follows from the clean `Y`-slot
additivity of Ricci (`ricciAux_add_left`) and the additivity of the metric in its first argument
(`inner_add_left`). -/
lemma einsteinTensor_add_left
    (Hcov : ContMDiffCovariantDerivativeOn E n covT univ) (hn : n ≠ 0)
    (hcov : IsCovariantDerivativeOn E covT univ)
    (Y Y' Z : Π x : M, TangentSpace I x) (hZ : CMDiff (n + 1) (T% Z)) (x : M)
    (hframe : ∀ i, CMDiff (n + 1) (T% (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)))) :
    einsteinTensor Hcov hn hcov (Y + Y') Z hZ x hframe
      = einsteinTensor Hcov hn hcov Y Z hZ x hframe
        + einsteinTensor Hcov hn hcov Y' Z hZ x hframe := by
  rw [einsteinTensor, einsteinTensor, einsteinTensor, ricciAux_add_left]
  rw [show (Y + Y') x = Y x + Y' x from rfl, inner_add_left]
  ring

/-- **Non-vacuity / the trace identity for the Einstein tensor.** Contracting the Einstein tensor
with the metric along the canonical orthonormal frame yields
`tr_g(G) = R − ½ R d = R (1 − d/2)`, where `d = finrank ℝ E` is the manifold dimension — the classical
identity (in particular `tr_g(G) = 0` in dimension `2`). This exhibits `einsteinTensor` as a genuine
modification of `Ric` by the scalar-curvature/metric term (not identically `Ric`, nor identically
zero by fiat): its metric trace differs from that of `Ric` (`= R`) by exactly `½ R d`.

Here the diagonal contraction uses `extend E (e i)` for the frame fields; the metric term collapses
via `extend_apply_self` and `∑ i ⟪e i, e i⟫ = d` for the orthonormal frame. -/
lemma sum_einsteinTensor_frame_diag
    (Hcov : ContMDiffCovariantDerivativeOn E n covT univ) (hn : n ≠ 0)
    (hcov : IsCovariantDerivativeOn E covT univ) (x : M)
    (hframe : ∀ i, CMDiff (n + 1) (T% (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)))) :
    ∑ i, einsteinTensor Hcov hn hcov
        (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
        (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) (hframe i) x hframe
      = scalarCurvature Hcov hn hcov x hframe
        - (1 / 2) * scalarCurvature Hcov hn hcov x hframe
          * (Module.finrank ℝ (TangentSpace I x) : ℝ) := by
  have hmet : ∀ i, inner ℝ
      ((extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) x)
      ((extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) x) = (1 : ℝ) := by
    intro i
    rw [extend_apply_self, real_inner_self_eq_norm_sq,
      (stdOrthonormalBasis ℝ (TangentSpace I x)).orthonormal.1 i]
    norm_num
  simp only [einsteinTensor, hmet, mul_one]
  rw [Finset.sum_sub_distrib, ← scalarCurvature]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end scalarCurvature

end IsCovariantDerivativeOn
