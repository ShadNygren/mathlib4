/-
Copyright (c) 2025 The Mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature

/-! # First and second variation of the Riemann curvature under a connection perturbation

Given a covariant derivative (Koszul connection) `∇` on a vector bundle `V`, and a *connection
perturbation* `A`, i.e. a one-form valued in the endomorphisms of `V`
(`A : Π x, V x →L[𝕜] TangentSpace I x →L[𝕜] V x`, exactly the perturbation type used by
`IsCovariantDerivativeOn.add_one_form` / `CovariantDerivative.addOneForm`), the perturbed
connection is `∇' σ x = ∇ σ x + A x (σ x)`.

The bare curvature function
`curvatureAux cov X Y σ x = cov (covDir cov Y σ) x (X x) − cov (covDir cov X σ) x (Y x)
  − cov σ x [X, Y] x`
is **exactly quadratic** in the connection `cov`. Consequently the curvature of the perturbed
connection decomposes as a *finite polynomial identity* — no differentiation, no limits:
```
curvatureAux (∇ + A) X Y σ x
  = curvatureAux ∇ X Y σ x            -- base (0th order)
  + linCurvatureAux ∇ A X Y σ x       -- 1st variation δ¹R[A] (linear in A)
  + quadCurvatureAux ∇ A X Y σ x      -- 2nd variation δ²R[A] (quadratic in A)
```
This rigorously *defines* the first and second variation of the curvature with respect to a
connection perturbation, with no analytic machinery. This decomposition
(`curvatureAux_addOneForm_eq`) is the crown result of this file.

## Main definitions and results

* `IsCovariantDerivativeOn.linCurvatureAux`: the first variation `δ¹R[A]` of the curvature
  (linear in the perturbation `A`).
* `IsCovariantDerivativeOn.quadCurvatureAux`: the second variation `δ²R[A]` of the curvature
  (quadratic in `A`), a purely algebraic (differentiation-free) expression.
* `IsCovariantDerivativeOn.curvatureAux_addOneForm_eq`: **the crown decomposition identity**
  `R(∇ + A) = R(∇) + δ¹R[A] + δ²R[A]`.
* `IsCovariantDerivativeOn.linCurvatureAux_smul_left`,
  `IsCovariantDerivativeOn.linCurvatureAux_smul_right`,
  `IsCovariantDerivativeOn.linCurvatureAux_add_left`,
  `IsCovariantDerivativeOn.linCurvatureAux_add_right`: `C^∞`-function-linearity (tensoriality) of
  `δ¹R[A]` in the two vector-field arguments, confirming the first variation is a genuine tensor.
* `IsCovariantDerivativeOn.curvatureAux_addOneForm_of_flat`: the flat-base corollary — over a flat
  base connection the perturbed curvature is *exactly* `δ¹R[A] + δ²R[A]`.
* `IsCovariantDerivativeOn.CurvatureVariationWitness.quadCurvatureAux_ne_zero`: a concrete
  non-vacuity witness (base `ℝ²`, non-commuting `A`) showing `δ²R[A] ≠ 0`.

## Scope (honest)

This is the **connection-level** variation: `δR` is taken with respect to a *connection*
perturbation `A`. The composition with the metric→connection map — i.e. producing `A = A(h)` from a
*metric* perturbation `h` via the Levi-Civita/Koszul formula and the resulting second-order metric variation, are
*not* treated here.

The Ricci/Einstein *trace* of the first variation — the **linearized Einstein operator `δ¹G[A]`** —
is built here as the trace chain of `linCurvatureAux`, mirroring the base
`curvatureVF → ricciAux → scalarCurvature → einsteinTensor` pipeline of `Curvature.lean` one
variation-order up:

* `IsCovariantDerivativeOn.linCurvatureVF`: `linCurvatureAux` bundled as a `(1, 2)`-in-vector-fields
  tensor via `TensorialAt.mkHom₂`, its two vector-field-slot `TensorialAt` instances discharged from
  the *`A`-smoothness bridge* `ASmoothOn` (differentiability of `z ↦ A z (σ z) (W z)`, the exact
  analogue of the `curvatureVF` section-smoothness hypothesis `hσ`). Because the first variation is
  *linear* in `A`, no iterated covariant derivative of `A` is taken, so — unlike `curvatureVF` — the
  bundle depends on the base connection only through `IsCovariantDerivativeOn` (the Leibniz rule),
  not through any `ContMDiffCovariantDerivativeOn` smoothness.
* `IsCovariantDerivativeOn.linRicciAux`: the first variation of the Ricci curvature `δ¹Ric[A]`, the
  `LinearMap.trace` of the linearized curvature endomorphism on `TM` (`V = TM`).
* `IsCovariantDerivativeOn.linScalarCurvature`: the linearized scalar curvature `δ¹R[A]_scal`, the
  metric trace `∑ i δ¹Ric[A](e i, e i)`.
* `IsCovariantDerivativeOn.linEinsteinTensor`: the **linearized Einstein tensor**
  `δ¹G[A] = δ¹Ric[A] − ½ δ¹R[A]_scal · g`.
* `IsCovariantDerivativeOn.sum_linEinsteinTensor_frame_diag`: the non-vacuity trace identity
  `tr_g(δ¹G[A]) = δ¹R[A]_scal (1 − d/2)`.

## Scope of `δ¹G[A]` (honest)

This is the linearized Einstein tensor for a *connection* perturbation `A`. Specialising to
`A = A(h)` (a *metric* perturbation, via the Levi-Civita/Koszul formula) and the resulting second-order metric variation are *not* treated here.
-/

open Bundle Set NormedSpace FiberBundle
open scoped Manifold ContDiff Topology

@[expose] public noncomputable section

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

variable {cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x)}
  {A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x}
  {X Y : Π x : M, TangentSpace I x} {σ : Π x : M, V x}

/-- The perturbed connection `∇ + A` as a bare function, matching the definiens of
`IsCovariantDerivativeOn.add_one_form`: `(∇ + A) σ x = ∇ σ x + A x (σ x)`. -/
noncomputable def addOneFormAux
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x) :
    (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x) :=
  fun σ x ↦ cov σ x + A x (σ x)

@[simp]
lemma addOneFormAux_apply
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x) (σ : Π x : M, V x) (x : M) :
    addOneFormAux cov A σ x = cov σ x + A x (σ x) :=
  rfl

/-- The first variation `δ¹R[A]` of the Riemann curvature under a connection perturbation `A`:
the part of `curvatureAux (∇ + A)` that is *linear* in `A`. Explicitly, it is the sum of
* the "inner-`A`" terms `∇` applied to the section `z ↦ A z (σ z) (Y z)` (resp. `X`),
* the "outer-`A`" terms `A` applied to the once-differentiated sections `∇_Y σ` (resp. `X`), and
* the bracket term `−A x (σ x) [X, Y] x`.

This is a genuine tensor (see `linCurvatureAux_smul_left`/`_smul_right`). -/
noncomputable def linCurvatureAux
    (cov : (Π x : M, V x) → (Π x : M, TangentSpace I x →L[𝕜] V x))
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x)
    (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  fun x ↦
    (cov (fun z ↦ A z (σ z) (Y z)) x (X x) - cov (fun z ↦ A z (σ z) (X z)) x (Y x))
      + (A x (covDir cov Y σ x) (X x) - A x (covDir cov X σ x) (Y x))
      - A x (σ x) (VectorField.mlieBracket I X Y x)

lemma linCurvatureAux_apply
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x)
    (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) :
    linCurvatureAux cov A X Y σ x =
      (cov (fun z ↦ A z (σ z) (Y z)) x (X x) - cov (fun z ↦ A z (σ z) (X z)) x (Y x))
        + (A x (covDir cov Y σ x) (X x) - A x (covDir cov X σ x) (Y x))
        - A x (σ x) (VectorField.mlieBracket I X Y x) :=
  rfl

/-- The second variation `δ²R[A]` of the Riemann curvature under a connection perturbation `A`:
the part of `curvatureAux (∇ + A)` that is *quadratic* in `A`. This is a purely algebraic
(differentiation-free) expression, `A x (A x (σ x) (Y x)) (X x) − A x (A x (σ x) (X x)) (Y x)`. -/
noncomputable def quadCurvatureAux
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x)
    (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) : Π x : M, V x :=
  fun x ↦ A x (A x (σ x) (Y x)) (X x) - A x (A x (σ x) (X x)) (Y x)

lemma quadCurvatureAux_apply
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x)
    (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) :
    quadCurvatureAux A X Y σ x =
      A x (A x (σ x) (Y x)) (X x) - A x (A x (σ x) (X x)) (Y x) :=
  rfl

/-- **The crown decomposition identity.** The Riemann curvature of the perturbed connection
`∇ + A` splits *exactly* — a finite polynomial identity, no differentiation or limits — into the
base curvature, its first variation (linear in `A`) and its second variation (quadratic in `A`):
`R(∇ + A) = R(∇) + δ¹R[A] + δ²R[A]`.

The `IsCovariantDerivativeOn`-additivity of `∇` (`hcov.add`) is used only to split the covariant
derivative `∇` applied to the *sum* section `∇_Y σ + (z ↦ A z (σ z) (Y z))` that arises inside the
perturbed iterated derivative; hence the differentiability hypotheses on `∇_Y σ`, `∇_X σ` and on
the sections `z ↦ A z (σ z) (Y z)`, `z ↦ A z (σ z) (X z)`. Everything else is `ContinuousLinearMap`
add/sub algebra: the quadratic (`A`-of-`A`) and the two flavours of linear terms are collected by
`abel`. -/
lemma curvatureAux_addOneForm_eq (hcov : IsCovariantDerivativeOn F cov univ)
    (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hcovYσ : MDiffAt (T% (covDir cov Y σ)) x) (hcovXσ : MDiffAt (T% (covDir cov X σ)) x)
    (hAY : MDiffAt (T% fun z ↦ A z (σ z) (Y z)) x)
    (hAX : MDiffAt (T% fun z ↦ A z (σ z) (X z)) x) :
    curvatureAux (addOneFormAux cov A) X Y σ x =
      curvatureAux cov X Y σ x + linCurvatureAux cov A X Y σ x + quadCurvatureAux A X Y σ x := by
  rw [curvatureAux_apply, curvatureAux_apply, linCurvatureAux_apply, quadCurvatureAux_apply]
  -- Unfold the perturbed connection and the perturbed `covDir` into a sum of sections.
  have hcovDirY : covDir (addOneFormAux cov A) Y σ
      = covDir cov Y σ + fun z ↦ A z (σ z) (Y z) := by
    ext z; simp [covDir, addOneFormAux]
  have hcovDirX : covDir (addOneFormAux cov A) X σ
      = covDir cov X σ + fun z ↦ A z (σ z) (X z) := by
    ext z; simp [covDir, addOneFormAux]
  rw [hcovDirY, hcovDirX]
  -- Split `∇` over the sum sections (needs the additivity axiom), and unfold the remaining `+A`.
  rw [addOneFormAux_apply, addOneFormAux_apply, addOneFormAux_apply,
    hcov.add hcovYσ hAY, hcov.add hcovXσ hAX]
  simp only [add_apply, Pi.add_apply, map_add, covDir]
  abel

/-! ### Tensoriality of the first variation

Like the curvature itself, the first variation `δ¹R[A]` is `C^∞`-function-linear (tensorial) in its
two vector-field arguments. The proof mirrors `curvatureAux_smul_left`: the single Leibniz
correction term produced by the inner covariant derivative `∇` on the section
`z ↦ A z (σ z) (X z)` cancels exactly against the product-rule correction from the Lie bracket
`[f • X, Y]`. -/

section tensoriality

variable [IsManifold I 2 M] [CompleteSpace E]

/-- `C^∞`-function-linearity (tensoriality) of the first variation of the curvature in its first
(left) vector-field argument: `δ¹R[A](f • X, Y) σ = f • δ¹R[A](X, Y) σ`, pointwise at `x`.

The Leibniz correction from `∇` applied to `z ↦ A z (σ z) ((f • X) z) = f • (z ↦ A z (σ z) (X z))`
cancels the product-rule correction from the Lie bracket `[f • X, Y]`, exactly as in
`curvatureAux_smul_left`. -/
lemma linCurvatureAux_smul_left (hcov : IsCovariantDerivativeOn F cov univ)
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x)
    (hAX : MDiffAt (T% fun z ↦ A z (σ z) (X z)) x) :
    linCurvatureAux cov A (f • X) Y σ x = f x • linCurvatureAux cov A X Y σ x := by
  rw [linCurvatureAux_apply, linCurvatureAux_apply]
  -- The first inner-`A` term and the two outer-`A` terms are directly linear in the tangent slot.
  rw [show (f • X) x = f x • X x from rfl, map_smul]
  -- The `covDir cov (f • X) σ` outer term pulls out `f` from the direction.
  rw [covDir_smul_dir, show (f • covDir cov X σ) x = f x • covDir cov X σ x from rfl]
  -- The second inner-`A` term is `∇` of `f • (z ↦ A z (σ z) (X z))`; apply Leibniz.
  rw [show (fun z ↦ A z (σ z) ((f • X) z)) = f • (fun z ↦ A z (σ z) (X z)) from by
      funext z
      show A z (σ z) (f z • X z) = f z • A z (σ z) (X z)
      rw [map_smul],
    hcov.leibniz hAX hf]
  -- The bracket term uses the product rule for `[f • X, Y]`.
  rw [VectorField.mlieBracket_smul_left hf hX]
  -- Evaluate the applied continuous-linear maps and cancel the two Leibniz corrections.
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
    covDir]
  module

/-- `C^∞`-function-linearity (tensoriality) of the first variation of the curvature in its second
(right) vector-field argument: `δ¹R[A](X, f • Y) σ = f • δ¹R[A](X, Y) σ`, pointwise at `x`. -/
lemma linCurvatureAux_smul_right (hcov : IsCovariantDerivativeOn F cov univ)
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x)
    (hAY : MDiffAt (T% fun z ↦ A z (σ z) (Y z)) x) :
    linCurvatureAux cov A X (f • Y) σ x = f x • linCurvatureAux cov A X Y σ x := by
  rw [linCurvatureAux_apply, linCurvatureAux_apply]
  -- The `covDir cov X (f • Y) σ` outer term pulls out `f` from the direction.
  rw [covDir_smul_dir, show (f • covDir cov Y σ) x = f x • covDir cov Y σ x from rfl]
  -- The first inner-`A` term is `∇` of `f • (z ↦ A z (σ z) (Y z))`; apply Leibniz.
  rw [show (fun z ↦ A z (σ z) ((f • Y) z)) = f • (fun z ↦ A z (σ z) (Y z)) from by
      funext z
      show A z (σ z) (f z • Y z) = f z • A z (σ z) (Y z)
      rw [map_smul],
    hcov.leibniz hAY hf]
  -- The bracket term uses the product rule for `[X, f • Y]`.
  rw [VectorField.mlieBracket_smul_right hf hY]
  -- The remaining two `(f • Y) x` direction arguments pull out `f` from the tangent slot.
  simp only [show (f • Y) x = f x • Y x from rfl, map_smul]
  -- Evaluate the applied continuous-linear maps and cancel the two Leibniz corrections.
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
    covDir]
  module

/-- Additivity of the first variation of the curvature in its first (left) vector-field argument:
`δ¹R[A](X + X', Y) σ = δ¹R[A](X, Y) σ + δ¹R[A](X', Y) σ`, pointwise at `x`. Together with
`linCurvatureAux_smul_left` this exhibits `δ¹R[A]` as `C^∞`-function-*linear* (a genuine tensor) in
its left slot. -/
lemma linCurvatureAux_add_left (hcov : IsCovariantDerivativeOn F cov univ)
    (X X' Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x)
    (hAX : MDiffAt (T% fun z ↦ A z (σ z) (X z)) x)
    (hAX' : MDiffAt (T% fun z ↦ A z (σ z) (X' z)) x) :
    linCurvatureAux cov A (X + X') Y σ x
      = linCurvatureAux cov A X Y σ x + linCurvatureAux cov A X' Y σ x := by
  rw [linCurvatureAux_apply, linCurvatureAux_apply, linCurvatureAux_apply]
  rw [covDir_add_dir]
  rw [show (fun z ↦ A z (σ z) ((X + X') z)) = (fun z ↦ A z (σ z) (X z)) + fun z ↦ A z (σ z) (X' z)
      from by funext z; show A z (σ z) (X z + X' z) = _; rw [map_add]; rfl,
    hcov.add hAX hAX']
  rw [VectorField.mlieBracket_add_left hX hX']
  simp only [Pi.add_apply, add_apply, map_add, covDir]
  abel

/-- Additivity of the first variation of the curvature in its second (right) vector-field argument:
`δ¹R[A](X, Y + Y') σ = δ¹R[A](X, Y) σ + δ¹R[A](X, Y') σ`, pointwise at `x`. -/
lemma linCurvatureAux_add_right (hcov : IsCovariantDerivativeOn F cov univ)
    (X Y Y' : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x)
    (hAY : MDiffAt (T% fun z ↦ A z (σ z) (Y z)) x)
    (hAY' : MDiffAt (T% fun z ↦ A z (σ z) (Y' z)) x) :
    linCurvatureAux cov A X (Y + Y') σ x
      = linCurvatureAux cov A X Y σ x + linCurvatureAux cov A X Y' σ x := by
  rw [linCurvatureAux_apply, linCurvatureAux_apply, linCurvatureAux_apply]
  rw [covDir_add_dir]
  rw [show (fun z ↦ A z (σ z) ((Y + Y') z)) = (fun z ↦ A z (σ z) (Y z)) + fun z ↦ A z (σ z) (Y' z)
      from by funext z; show A z (σ z) (Y z + Y' z) = _; rw [map_add]; rfl,
    hcov.add hAY hAY']
  rw [VectorField.mlieBracket_add_right hY hY']
  simp only [Pi.add_apply, add_apply, map_add, covDir]
  abel

end tensoriality

/-! ### The linearized Einstein operator `δ¹G[A]`: the trace chain of `δ¹R[A]`

Mirroring the curvature trace chain `curvatureAux → curvatureVF → ricciAux → scalarCurvature →
einsteinTensor` of `Curvature.lean`, one variation-order up, we bundle the first variation of the
curvature `linCurvatureAux` (`δ¹R[A]`) into a `(1, 2)`-in-vector-fields tensor `linCurvatureVF`, take
its Ricci trace `linRicciAux` (`δ¹Ric[A]`), the metric trace `linScalarCurvature`, and assemble the
linearized Einstein tensor `linEinsteinTensor` (`δ¹G[A] = δ¹Ric[A] − ½ δ¹R[A]_scal · g`).

The one honest ingredient beyond the base pipeline is the *`A`-smoothness bridge*: to discharge the
`hAX : MDiffAt (T% fun z ↦ A z (σ z) (X z)) x` hypotheses of the tensoriality lemmas from the
`TensorialAt.smul`/`.add` fields (which only supply `MDiffAt (T% X) x`), we assume the perturbed
section-form `z ↦ A z (σ z) (·)` is differentiable on differentiable vector fields, i.e. the
hypothesis `hAσ` below. This exactly parallels the section-smoothness hypothesis `hσ` carried by
`curvatureVF`: it says the one-form `A(σ)` is a differentiable `Hom(TM, V)`-valued section. -/

section linCurvatureVF

variable [IsManifold I 2 M] [CompleteSpace E] [VectorBundle 𝕜 F V] {n : ℕ∞ω}

variable (F) in
/-- The `A`-smoothness bridge: the section-form `z ↦ A z (σ z) (W z)` obtained by applying the
connection perturbation `A` to the section `σ` and a vector field `W` is differentiable at `x`
whenever `W` is. This is the honest smoothness datum on the perturbation `A` (paired with `σ`)
needed to discharge the `hAX` hypotheses of the first-variation tensoriality lemmas — the exact
analogue of the section-smoothness hypothesis `hσ` carried by `curvatureVF`. The fibre model `F` is
explicit so it can be inferred at use sites (it is not pinned by `A`/`σ`, which mention only `V`). -/
def ASmoothOn (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x) (σ : Π x : M, V x) (x : M) : Prop :=
  ∀ W : Π x : M, TangentSpace I x, MDiffAt (T% W) x →
    MDiffAt (T% (fun z ↦ A z (σ z) (W z) : Π z : M, V z)) x

omit [VectorBundle 𝕜 F V] in
/-- `C^∞`-function-linearity of the first variation `δ¹R[A]` in its first (left) vector-field
argument, with the differentiability of `z ↦ A z (σ z) (X z)` discharged from the `A`-smoothness
bridge `hAσ`. -/
lemma linCurvatureAux_smul_left'
    (hcov : IsCovariantDerivativeOn F cov univ)
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hf : MDiffAt f x) (hX : MDiffAt (T% X) x) (hAσ : ASmoothOn F A σ x) :
    linCurvatureAux cov A (f • X) Y σ x = f x • linCurvatureAux cov A X Y σ x :=
  hcov.linCurvatureAux_smul_left f X Y σ hf hX (hAσ X hX)

omit [VectorBundle 𝕜 F V] in
/-- Additivity of the first variation `δ¹R[A]` in its first (left) vector-field argument, with the
differentiability of the perturbed section-forms discharged from the `A`-smoothness bridge. -/
lemma linCurvatureAux_add_left'
    (hcov : IsCovariantDerivativeOn F cov univ)
    (X X' Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hX : MDiffAt (T% X) x) (hX' : MDiffAt (T% X') x) (hAσ : ASmoothOn F A σ x) :
    linCurvatureAux cov A (X + X') Y σ x
      = linCurvatureAux cov A X Y σ x + linCurvatureAux cov A X' Y σ x :=
  hcov.linCurvatureAux_add_left X X' Y σ hX hX' (hAσ X hX) (hAσ X' hX')

omit [VectorBundle 𝕜 F V] in
/-- `C^∞`-function-linearity of the first variation `δ¹R[A]` in its second (right) vector-field
argument, with the differentiability of `z ↦ A z (σ z) (Y z)` discharged from the `A`-smoothness
bridge. -/
lemma linCurvatureAux_smul_right'
    (hcov : IsCovariantDerivativeOn F cov univ)
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hf : MDiffAt f x) (hY : MDiffAt (T% Y) x) (hAσ : ASmoothOn F A σ x) :
    linCurvatureAux cov A X (f • Y) σ x = f x • linCurvatureAux cov A X Y σ x :=
  hcov.linCurvatureAux_smul_right f X Y σ hf hY (hAσ Y hY)

omit [VectorBundle 𝕜 F V] in
/-- Additivity of the first variation `δ¹R[A]` in its second (right) vector-field argument, with the
differentiability of the perturbed section-forms discharged from the `A`-smoothness bridge. -/
lemma linCurvatureAux_add_right'
    (hcov : IsCovariantDerivativeOn F cov univ)
    (X Y Y' : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hY : MDiffAt (T% Y) x) (hY' : MDiffAt (T% Y') x) (hAσ : ASmoothOn F A σ x) :
    linCurvatureAux cov A X (Y + Y') σ x
      = linCurvatureAux cov A X Y σ x + linCurvatureAux cov A X Y' σ x :=
  hcov.linCurvatureAux_add_right X Y Y' σ hY hY' (hAσ Y hY) (hAσ Y' hY')

omit [VectorBundle 𝕜 F V] in
/-- Tensoriality of the first variation `δ¹R[A]` in its first (left) vector-field slot, packaged as a
`TensorialAt` instance (the section `σ` and perturbation `A` held fixed). The `hAX` hypotheses are
discharged from the `A`-smoothness bridge `hAσ`. Consumed by the first argument of
`TensorialAt.mkHom₂`. -/
lemma linCurvatureAux_tensorial_left (hcov : IsCovariantDerivativeOn F cov univ)
    (Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (hAσ : ASmoothOn F A σ x) :
    TensorialAt I E (linCurvatureAux cov A · Y σ x) x where
  smul hf hX := hcov.linCurvatureAux_smul_left' _ _ _ _ hf hX hAσ
  add hX hX' := hcov.linCurvatureAux_add_left' _ _ _ _ hX hX' hAσ

omit [VectorBundle 𝕜 F V] in
/-- Tensoriality of the first variation `δ¹R[A]` in its second (right) vector-field slot, packaged as
a `TensorialAt` instance. Consumed by the second argument of `TensorialAt.mkHom₂`. -/
lemma linCurvatureAux_tensorial_right (hcov : IsCovariantDerivativeOn F cov univ)
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (hAσ : ASmoothOn F A σ x) :
    TensorialAt I E (linCurvatureAux cov A X · σ x) x where
  smul hf hY := hcov.linCurvatureAux_smul_right' _ _ _ _ hf hY hAσ
  add hY hY' := hcov.linCurvatureAux_add_right' _ _ _ _ hY hY' hAσ

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- The first variation of the curvature `δ¹R[A]`, bundled — for a fixed section `σ` and perturbation
`A` — as a continuous bilinear map in its two vector-field arguments,
`TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] V x`. This is the linearized `(1, 2)`-in-vector-fields
tensor, built with `TensorialAt.mkHom₂` from the vector-field tensoriality of `linCurvatureAux`,
mirroring `curvatureVF` one variation-order up. The tensoriality discharge is via the `A`-smoothness
bridge `hAσx` (there is no separate connection-smoothness dependence: the first variation is linear
in `A`, so no iterated covariant derivative of `A` is taken). -/
noncomputable def linCurvatureVF (hcov : IsCovariantDerivativeOn F cov univ)
    (σ : Π x : M, V x) (x : M) (hAσx : ∀ x', ASmoothOn F A σ x') :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] V x :=
  TensorialAt.mkHom₂ (linCurvatureAux cov A · · σ x) _
    (fun Y _ ↦ hcov.linCurvatureAux_tensorial_left Y σ (hAσx x))
    (fun X _ ↦ hcov.linCurvatureAux_tensorial_right X σ (hAσx x))

omit [VectorBundle 𝕜 F V] in
/-- Evaluation of the bundled first variation of the curvature: `linCurvatureVF … x (X x) (Y x)`
recovers the bare `linCurvatureAux cov A X Y σ x = δ¹R[A](X, Y) σ`, for differentiable `X`, `Y`. -/
lemma linCurvatureVF_apply (hcov : IsCovariantDerivativeOn F cov univ)
    (σ : Π x : M, V x) (hAσx : ∀ x', ASmoothOn F A σ x') {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x) :
    linCurvatureVF hcov σ x hAσx (X x) (Y x) = linCurvatureAux cov A X Y σ x :=
  TensorialAt.mkHom₂_apply _ _ hX hY

omit [VectorBundle 𝕜 F V] in
/-- Evaluation of the bundled first variation of the curvature on `extend`ed tangent vectors. -/
lemma linCurvatureVF_apply_eq_extend (hcov : IsCovariantDerivativeOn F cov univ)
    (σ : Π x : M, V x) (hAσx : ∀ x', ASmoothOn F A σ x') {x : M}
    (X₀ Y₀ : TangentSpace I x) :
    linCurvatureVF hcov σ x hAσx X₀ Y₀ =
      linCurvatureAux cov A (extend E X₀) (extend E Y₀) σ x :=
  TensorialAt.mkHom₂_apply_eq_extend _ _ X₀ Y₀

end linCurvatureVF

/-! ### Non-vacuity: the variation is genuinely non-trivial

The decomposition `curvatureAux_addOneForm_eq` is not the trivial `R = R + 0 + 0`. We first record
the *flat-base corollary*: when the base connection is flat, the entire curvature of the perturbed
connection is `δ¹R[A] + δ²R[A]`, i.e. curvature is generated purely by the perturbation. Then we
exhibit a concrete perturbation whose second variation `δ²R[A]` is nonzero. -/

/-- Flat-base corollary of the decomposition: if the base connection `∇` is flat at `(X, Y, σ, x)`
(`curvatureAux cov X Y σ x = 0`), then the curvature of the perturbed connection `∇ + A` there is
*exactly* the sum of the first and second variations, `δ¹R[A] + δ²R[A]` — curvature generated
purely by the connection perturbation. -/
lemma curvatureAux_addOneForm_of_flat (hcov : IsCovariantDerivativeOn F cov univ)
    (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) {x : M}
    (hcovYσ : MDiffAt (T% (covDir cov Y σ)) x) (hcovXσ : MDiffAt (T% (covDir cov X σ)) x)
    (hAY : MDiffAt (T% fun z ↦ A z (σ z) (Y z)) x)
    (hAX : MDiffAt (T% fun z ↦ A z (σ z) (X z)) x)
    (hflat : curvatureAux cov X Y σ x = 0) :
    curvatureAux (addOneFormAux cov A) X Y σ x =
      linCurvatureAux cov A X Y σ x + quadCurvatureAux A X Y σ x := by
  rw [curvatureAux_addOneForm_eq hcov X Y σ hcovYσ hcovXσ hAY hAX, hflat, zero_add]

/-! ### The linearized Ricci and Einstein tensors `δ¹Ric[A]`, `δ¹G[A]` on `TM`

Specialising the linearized curvature `linCurvatureVF` to the tangent bundle `V = TM`, its Ricci
trace is the *first variation of the Ricci curvature* `δ¹Ric[A] = linRicciAux`, and the Einstein
combination gives the **linearized Einstein tensor** `δ¹G[A] = linEinsteinTensor`. Everything mirrors
the base `ricciEndo → ricciAux → scalarCurvature → einsteinTensor` chain of `Curvature.lean`, one
variation-order up. The `Z`-slot section here is the fixed section `Z` of `TM`, and the linearized
curvature carries the `A`-smoothness bridge `hAσx` (paired with `Z`) in place of the base
section-smoothness `hZ`. Since the first variation is *linear* in `A`, no iterated covariant
derivative of `A` is taken, so `linCurvatureVF` — and hence this whole trace chain — depends on the
base connection only through `IsCovariantDerivativeOn` (the Leibniz rule), not through any
`ContMDiffCovariantDerivativeOn` smoothness of the connection. -/

section linRicci

variable [IsManifold I 2 M] [CompleteSpace E] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
  [VectorBundle 𝕜 E (TangentSpace I : M → Type _)]
  {covT : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x)}
  {AT : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] TangentSpace I x}

/-- The linearized Ricci endomorphism `X₀ ↦ δ¹R[A](X₀, Y) Z` of the tangent space `TM_x`, as a plain
`LinearMap`, extracted from the bundled linearized curvature `linCurvatureVF`. The trace of this
endomorphism is `linRicciAux`. Formed via `ContinuousLinearMap.coeLM` and the algebraic
`LinearMap.flip`, mirroring `ricciEndo`, so no norm on `TM_x` is required. -/
noncomputable def linRicciEndo (hcov : IsCovariantDerivativeOn E covT univ)
    (Y Z : Π x : M, TangentSpace I x) (hAσx : ∀ x', ASmoothOn E AT Z x') (x : M) :
    TangentSpace I x →ₗ[𝕜] TangentSpace I x :=
  ((ContinuousLinearMap.coeLM 𝕜).comp
    (linCurvatureVF hcov Z x hAσx).toLinearMap).flip (Y x)

/-- The **first variation of the Ricci curvature** `δ¹Ric[A]` of an unbundled affine connection
`covT` on `TM` under a connection perturbation `AT`, as a bare function `Y Z x`. On paper
`δ¹Ric[A](Y, Z) = tr (X ↦ δ¹R[A](X, Y) Z)`. Mirrors `ricciAux` one variation-order up. -/
noncomputable def linRicciAux (hcov : IsCovariantDerivativeOn E covT univ)
    (Y Z : Π x : M, TangentSpace I x) (hAσx : ∀ x', ASmoothOn E AT Z x') (x : M) : 𝕜 :=
  LinearMap.trace 𝕜 (TangentSpace I x) (linRicciEndo hcov Y Z hAσx x)

variable (hcov : IsCovariantDerivativeOn E covT univ)

/-- The linearized Ricci endomorphism evaluated on a tangent vector `X₀`:
`(X₀ ↦ δ¹R[A](X₀, Y) Z) X₀ = δ¹R[A]` bundled at `X₀` and `Y x`. -/
@[simp]
lemma linRicciEndo_apply (Y Z : Π x : M, TangentSpace I x)
    (hAσx : ∀ x', ASmoothOn E AT Z x') (x : M) (X₀ : TangentSpace I x) :
    linRicciEndo hcov Y Z hAσx x X₀ = linCurvatureVF hcov Z x hAσx X₀ (Y x) := by
  simp [linRicciEndo, LinearMap.flip_apply, ContinuousLinearMap.coeLM]

/-- `linRicciAux` as the trace of the genuine linearized curvature endomorphism
`X₀ ↦ δ¹R[A](extend X₀, Y) Z x`. This exhibits `δ¹Ric[A]` as `tr δ¹R[A](·, Y) Z` — the non-vacuity
of the definition (it is the trace of the genuine linearized curvature, which `linCurvatureVF_apply`
shows reproduces `δ¹R[A]`, whose non-vacuity is `quadCurvatureAux_ne_zero`'s first-order sibling). -/
lemma linRicciAux_apply (Y Z : Π x : M, TangentSpace I x)
    (hAσx : ∀ x', ASmoothOn E AT Z x') (x : M) :
    linRicciAux hcov Y Z hAσx x =
      LinearMap.trace 𝕜 (TangentSpace I x)
        (((ContinuousLinearMap.coeLM 𝕜).comp
          (linCurvatureVF hcov Z x hAσx).toLinearMap).flip (Y x)) :=
  rfl

/-- `C^∞`-function-linearity (tensoriality) of the linearized Ricci curvature `δ¹Ric[A]` in its
first argument: `δ¹Ric[A](f • Y, Z) = f • δ¹Ric[A](Y, Z)`. Clean: no extra hypotheses, from the
linearity of `flip _` in its tangent-vector argument and of `LinearMap.trace`. -/
lemma linRicciAux_smul_left (f : M → 𝕜) (Y Z : Π x : M, TangentSpace I x)
    (hAσx : ∀ x', ASmoothOn E AT Z x') (x : M) :
    linRicciAux hcov (f • Y) Z hAσx x = f x • linRicciAux hcov Y Z hAσx x := by
  rw [linRicciAux, linRicciAux, linRicciEndo, linRicciEndo]
  rw [show (f • Y) x = f x • Y x from rfl, map_smul, map_smul]

/-- Additivity of the linearized Ricci curvature `δ¹Ric[A]` in its first argument:
`δ¹Ric[A](Y + Y', Z) = δ¹Ric[A](Y, Z) + δ¹Ric[A](Y', Z)`. Clean. -/
lemma linRicciAux_add_left (Y Y' Z : Π x : M, TangentSpace I x)
    (hAσx : ∀ x', ASmoothOn E AT Z x') (x : M) :
    linRicciAux hcov (Y + Y') Z hAσx x
      = linRicciAux hcov Y Z hAσx x + linRicciAux hcov Y' Z hAσx x := by
  rw [linRicciAux, linRicciAux, linRicciAux, linRicciEndo, linRicciEndo, linRicciEndo]
  rw [show (Y + Y') x = Y x + Y' x from rfl, map_add, map_add]

end linRicci

section linScalarEinstein

open scoped Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [VectorBundle ℝ E (TangentSpace I : M → Type _)]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  {covT : (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x)}
  {AT : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x}

/-- The **linearized scalar curvature** `δ¹R[A]_scal(x) = tr_g(δ¹Ric[A])`: the metric trace of the
linearized Ricci bilinear form, realised as `∑ i, δ¹Ric[A](e i, e i)` over the canonical
`g`-orthonormal basis `e = stdOrthonormalBasis ℝ (TangentSpace I x)`. Mirrors `scalarCurvature`.

Honest hypotheses: the metric enters through `RiemannianBundle`; `hAframe` is the `A`-smoothness
bridge (paired with the frame field summed by the trace) required by the linearized Ricci in its
`Z`-slot, one per extended orthonormal basis field. -/
noncomputable def linScalarCurvature
    (hcov : IsCovariantDerivativeOn E covT univ) (x : M)
    (hAframe : ∀ i,
      ∀ x', ASmoothOn E AT (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) x') :
    ℝ :=
  ∑ i, linRicciAux hcov
    (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
    (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) (hAframe i) x

/-- Unfolding lemma for `linScalarCurvature`: the sum of the linearized Ricci curvatures along the
diagonal of the canonical orthonormal frame, `δ¹R[A]_scal = ∑ i δ¹Ric[A](e i, e i) = tr_g(δ¹Ric[A])`.
Makes the non-vacuity manifest: it is the honest metric trace of `linRicciAux`, whose non-vacuity is
recorded on `linRicciAux_apply` (the trace of the genuine linearized curvature endomorphism). -/
lemma linScalarCurvature_apply
    (hcov : IsCovariantDerivativeOn E covT univ) (x : M)
    (hAframe : ∀ i,
      ∀ x', ASmoothOn E AT (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) x') :
    linScalarCurvature hcov x hAframe =
      ∑ i, linRicciAux hcov
        (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
        (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) (hAframe i) x :=
  rfl

/-- The **linearized Einstein tensor** `δ¹G[A](Y, Z) = δ¹Ric[A](Y, Z) − ½ δ¹R[A]_scal · g(Y, Z)` of
an affine connection `covT` on `TM` under a connection perturbation `AT`. This is the first variation
of the Einstein tensor `G = Ric − ½ R g` under the connection perturbation `A` — the linearized
Einstein operator `δ¹G[A]`. Mirrors `einsteinTensor` one variation-order up.

Honest hypotheses: `hAσx` is the `A`-smoothness bridge in the linearized Ricci `Z`-slot; `hAframe`
is the frame `A`-smoothness bridge for the linearized scalar-curvature trace. -/
noncomputable def linEinsteinTensor
    (hcov : IsCovariantDerivativeOn E covT univ)
    (Y Z : Π x : M, TangentSpace I x) (hAσx : ∀ x', ASmoothOn E AT Z x') (x : M)
    (hAframe : ∀ i,
      ∀ x', ASmoothOn E AT (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) x') : ℝ :=
  linRicciAux hcov Y Z hAσx x
    - (1 / 2) * linScalarCurvature hcov x hAframe * inner ℝ (Y x) (Z x)

/-- Unfolding lemma for `linEinsteinTensor`:
`δ¹G[A](Y, Z) = δ¹Ric[A](Y, Z) − ½ δ¹R[A]_scal · g(Y, Z)`. -/
lemma linEinsteinTensor_apply
    (hcov : IsCovariantDerivativeOn E covT univ)
    (Y Z : Π x : M, TangentSpace I x) (hAσx : ∀ x', ASmoothOn E AT Z x') (x : M)
    (hAframe : ∀ i,
      ∀ x', ASmoothOn E AT (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) x') :
    linEinsteinTensor hcov Y Z hAσx x hAframe =
      linRicciAux hcov Y Z hAσx x
        - (1 / 2) * linScalarCurvature hcov x hAframe * inner ℝ (Y x) (Z x) :=
  rfl

/-- `C^∞`-function-linearity (tensoriality) of the linearized Einstein tensor `δ¹G[A]` in its first
argument: `δ¹G[A](f • Y, Z) = f • δ¹G[A](Y, Z)`. Follows from the first-slot tensoriality of the
linearized Ricci (`linRicciAux_smul_left`) and the linearity of the metric in its first argument
(`real_inner_smul_left`); no extra differentiability hypotheses. -/
lemma linEinsteinTensor_smul_left
    (hcov : IsCovariantDerivativeOn E covT univ)
    (f : M → ℝ) (Y Z : Π x : M, TangentSpace I x)
    (hAσx : ∀ x', ASmoothOn E AT Z x') (x : M)
    (hAframe : ∀ i,
      ∀ x', ASmoothOn E AT (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) x') :
    linEinsteinTensor hcov (f • Y) Z hAσx x hAframe
      = f x • linEinsteinTensor hcov Y Z hAσx x hAframe := by
  rw [linEinsteinTensor, linEinsteinTensor, linRicciAux_smul_left]
  rw [show (f • Y) x = f x • Y x from rfl, real_inner_smul_left, smul_eq_mul, smul_eq_mul]
  ring

/-- **Non-vacuity / the trace identity for the linearized Einstein tensor `δ¹G[A]`.** Contracting
`δ¹G[A]` with the metric along the canonical orthonormal frame yields
`tr_g(δ¹G[A]) = δ¹R[A]_scal − ½ δ¹R[A]_scal · d = δ¹R[A]_scal (1 − d/2)`, where `d = finrank ℝ E` is
the manifold dimension — the first-variation of the classical Einstein trace identity (in particular
`tr_g(δ¹G[A]) = 0` in dimension `2`). This exhibits `linEinsteinTensor` as a genuine modification of
`linRicciAux` by the linearized-scalar-curvature/metric term (not identically `δ¹Ric[A]`, nor
identically zero by fiat): its metric trace differs from that of `δ¹Ric[A]` (`= δ¹R[A]_scal`) by
exactly `½ δ¹R[A]_scal · d`. Mirrors `sum_einsteinTensor_frame_diag` one variation-order up. -/
lemma sum_linEinsteinTensor_frame_diag
    (hcov : IsCovariantDerivativeOn E covT univ) (x : M)
    (hAframe : ∀ i,
      ∀ x', ASmoothOn E AT (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) x') :
    ∑ i, linEinsteinTensor hcov
        (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
        (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) (hAframe i) x hAframe
      = linScalarCurvature hcov x hAframe
        - (1 / 2) * linScalarCurvature hcov x hAframe
          * (Module.finrank ℝ (TangentSpace I x) : ℝ) := by
  have hmet : ∀ i, inner ℝ
      ((extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) x)
      ((extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) x) = (1 : ℝ) := by
    intro i
    rw [extend_apply_self, real_inner_self_eq_norm_sq,
      (stdOrthonormalBasis ℝ (TangentSpace I x)).orthonormal.1 i]
    norm_num
  simp only [linEinsteinTensor, hmet, mul_one]
  rw [Finset.sum_sub_distrib, ← linScalarCurvature]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end linScalarEinstein

/-! ### The quadratic Einstein operator `δ²G[A]`: the trace chain of `δ²R[A]`

Mirroring the linearized trace chain `linCurvatureAux → linCurvatureVF → linRicciAux →
linScalarCurvature → linEinsteinTensor` (`δ¹`) one further variation-order up, we bundle the *second*
variation of the curvature `quadCurvatureAux` (`δ²R[A]`, quadratic in `A`) into a
`(1, 2)`-in-vector-fields tensor `quadCurvatureVF`, take its Ricci trace `quadRicciAux` (`δ²Ric[A]`),
the metric trace `quadScalarCurvature`, and assemble the quadratic Einstein tensor `quadEinsteinTensor`
(`δ²G[A] = δ²Ric[A] − ½ δ²R[A]_scal · g`).

**The crucial simplification over `δ¹`.** `quadCurvatureAux A X Y σ x =
A x (A x (σ x) (Y x)) (X x) − A x (A x (σ x) (X x)) (Y x)` is a *purely algebraic*, nested
`ContinuousLinearMap`-application expression — no covariant derivative, no `mfderiv`, no Lie bracket.
Hence its tensoriality in `X`, `Y` is *trivial* `map_add`/`map_smul` of the CLMs, needing **no**
`A`-smoothness bridge (`ASmoothOn`) — unlike `linCurvatureVF`, whose Leibniz-correction cancellation
required `hAσ`. `quadCurvatureVF` therefore carries no smoothness hypothesis at all. This is the
quadratic-in-`A` half of the full second-order Einstein variation `δ²G[h, h]`; the other half is
`δ¹G[A₂]` with `A₂` the second-order connection variation, and is not built here. -/

section quadCurvatureTensoriality

/-- `C^∞`-function-linearity (tensoriality) of the second variation `δ²R[A]` in its first (left)
vector-field argument: `δ²R[A](f • X, Y) σ = f • δ²R[A](X, Y) σ`, pointwise at `x`. Purely algebraic:
`X` enters only through the outermost direction slots `A … (X x)` and the inner `A x (σ x) (X x)`, so
`ContinuousLinearMap.map_smul` on the direction argument delivers the scalar, with **no** smoothness
hypothesis. -/
lemma quadCurvatureAux_smul_left
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) :
    quadCurvatureAux A (f • X) Y σ x = f x • quadCurvatureAux A X Y σ x := by
  simp only [quadCurvatureAux_apply, Pi.smul_apply']
  show A x (A x (σ x) (Y x)) (f x • X x) - A x (A x (σ x) (f x • X x)) (Y x)
      = f x • (A x (A x (σ x) (Y x)) (X x) - A x (A x (σ x) (X x)) (Y x))
  simp only [map_smul, smul_apply, smul_sub]

/-- Additivity of the second variation `δ²R[A]` in its first (left) vector-field argument:
`δ²R[A](X + X', Y) σ = δ²R[A](X, Y) σ + δ²R[A](X', Y) σ`. Purely algebraic (`map_add`), no smoothness
hypothesis. -/
lemma quadCurvatureAux_add_left
    (X X' Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) :
    quadCurvatureAux A (X + X') Y σ x
      = quadCurvatureAux A X Y σ x + quadCurvatureAux A X' Y σ x := by
  simp only [quadCurvatureAux_apply, Pi.add_apply]
  show A x (A x (σ x) (Y x)) (X x + X' x) - A x (A x (σ x) (X x + X' x)) (Y x)
      = (A x (A x (σ x) (Y x)) (X x) - A x (A x (σ x) (X x)) (Y x))
        + (A x (A x (σ x) (Y x)) (X' x) - A x (A x (σ x) (X' x)) (Y x))
  simp only [map_add, add_apply]
  abel

/-- `C^∞`-function-linearity (tensoriality) of the second variation `δ²R[A]` in its second (right)
vector-field argument: `δ²R[A](X, f • Y) σ = f • δ²R[A](X, Y) σ`. Purely algebraic, no smoothness
hypothesis. -/
lemma quadCurvatureAux_smul_right
    (f : M → 𝕜) (X Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) :
    quadCurvatureAux A X (f • Y) σ x = f x • quadCurvatureAux A X Y σ x := by
  simp only [quadCurvatureAux_apply, Pi.smul_apply']
  show A x (A x (σ x) (f x • Y x)) (X x) - A x (A x (σ x) (X x)) (f x • Y x)
      = f x • (A x (A x (σ x) (Y x)) (X x) - A x (A x (σ x) (X x)) (Y x))
  simp only [map_smul, smul_apply, smul_sub]

/-- Additivity of the second variation `δ²R[A]` in its second (right) vector-field argument. Purely
algebraic (`map_add`), no smoothness hypothesis. -/
lemma quadCurvatureAux_add_right
    (X Y Y' : Π x : M, TangentSpace I x) (σ : Π x : M, V x) (x : M) :
    quadCurvatureAux A X (Y + Y') σ x
      = quadCurvatureAux A X Y σ x + quadCurvatureAux A X Y' σ x := by
  simp only [quadCurvatureAux_apply, Pi.add_apply]
  show A x (A x (σ x) (Y x + Y' x)) (X x) - A x (A x (σ x) (X x)) (Y x + Y' x)
      = (A x (A x (σ x) (Y x)) (X x) - A x (A x (σ x) (X x)) (Y x))
        + (A x (A x (σ x) (Y' x)) (X x) - A x (A x (σ x) (X x)) (Y' x))
  simp only [map_add, add_apply]
  abel

variable [IsManifold I 2 M] [CompleteSpace E]

/-- Tensoriality of the second variation `δ²R[A]` in its first (left) vector-field slot, packaged as a
`TensorialAt` instance (the section `σ` and perturbation `A` held fixed). **No smoothness hypothesis**
— the discharge is the purely algebraic `quadCurvatureAux_smul_left`/`_add_left`. Consumed by the
first argument of `TensorialAt.mkHom₂`. -/
lemma quadCurvatureAux_tensorial_left
    (Y : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    TensorialAt I E (quadCurvatureAux A · Y σ x) x where
  smul _ _ := quadCurvatureAux_smul_left _ _ Y σ x
  add _ _ := quadCurvatureAux_add_left _ _ Y σ x

/-- Tensoriality of the second variation `δ²R[A]` in its second (right) vector-field slot, packaged as
a `TensorialAt` instance. **No smoothness hypothesis.** Consumed by the second argument of
`TensorialAt.mkHom₂`. -/
lemma quadCurvatureAux_tensorial_right
    (X : Π x : M, TangentSpace I x) (σ : Π x : M, V x) :
    TensorialAt I E (quadCurvatureAux A X · σ x) x where
  smul _ _ := quadCurvatureAux_smul_right _ X _ σ x
  add _ _ := quadCurvatureAux_add_right X _ _ σ x

end quadCurvatureTensoriality

section quadCurvatureVF

variable [IsManifold I 2 M] [CompleteSpace E] [VectorBundle 𝕜 F V]
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- The second variation of the curvature `δ²R[A]`, bundled — for a fixed section `σ` and perturbation
`A` — as a continuous bilinear map in its two vector-field arguments,
`TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] V x`. This is the quadratic `(1, 2)`-in-vector-fields
tensor, built with `TensorialAt.mkHom₂` from the vector-field tensoriality of `quadCurvatureAux`,
mirroring `linCurvatureVF` one variation-order up.

**Simpler than `linCurvatureVF`: it carries no `A`-smoothness bridge `hAσx`.** Since
`quadCurvatureAux` is purely algebraic (nested CLM applications, no covariant derivative), its
tensoriality lemmas `quadCurvatureAux_tensorial_left`/`_right` need no differentiability of the
perturbed section-form, so this bundle is unconditional. -/
noncomputable def quadCurvatureVF
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x)
    (σ : Π x : M, V x) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] V x :=
  TensorialAt.mkHom₂ (quadCurvatureAux A · · σ x) _
    (fun Y _ ↦ quadCurvatureAux_tensorial_left Y σ)
    (fun X _ ↦ quadCurvatureAux_tensorial_right X σ)

/-- Evaluation of the bundled second variation of the curvature: `quadCurvatureVF … x (X x) (Y x)`
recovers the bare `quadCurvatureAux A X Y σ x = δ²R[A](X, Y) σ`, for differentiable `X`, `Y`. -/
lemma quadCurvatureVF_apply
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x)
    (σ : Π x : M, V x) {x : M}
    {X : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x)
    {Y : Π x : M, TangentSpace I x} (hY : MDiffAt (T% Y) x) :
    quadCurvatureVF A σ x (X x) (Y x) = quadCurvatureAux A X Y σ x :=
  TensorialAt.mkHom₂_apply _ _ hX hY

/-- Evaluation of the bundled second variation of the curvature on `extend`ed tangent vectors. -/
lemma quadCurvatureVF_apply_eq_extend
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x)
    (σ : Π x : M, V x) {x : M}
    (X₀ Y₀ : TangentSpace I x) :
    quadCurvatureVF A σ x X₀ Y₀ =
      quadCurvatureAux A (extend E X₀) (extend E Y₀) σ x :=
  TensorialAt.mkHom₂_apply_eq_extend _ _ X₀ Y₀

end quadCurvatureVF

/-! ### The quadratic Ricci and Einstein tensors `δ²Ric[A]`, `δ²G[A]` on `TM`

Specialising the quadratic curvature `quadCurvatureVF` to the tangent bundle `V = TM`, its Ricci
trace is the *second variation of the Ricci curvature* `δ²Ric[A] = quadRicciAux`, and the Einstein
combination gives the **quadratic Einstein tensor** `δ²G[A] = quadEinsteinTensor`. Everything mirrors
the linearized `linRicciEndo → linRicciAux → linScalarCurvature → linEinsteinTensor` chain, one
variation-order up — but with **no `A`-smoothness bridge** (`quadCurvatureVF` is unconditional). -/

section quadRicci

variable [IsManifold I 2 M] [CompleteSpace E] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
  [VectorBundle 𝕜 E (TangentSpace I : M → Type _)]
  (AT : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] TangentSpace I x)

/-- The quadratic Ricci endomorphism `X₀ ↦ δ²R[A](X₀, Y) Z` of the tangent space `TM_x`, as a plain
`LinearMap`, extracted from the bundled quadratic curvature `quadCurvatureVF`. The trace of this
endomorphism is `quadRicciAux`. Formed via `ContinuousLinearMap.coeLM` and the algebraic
`LinearMap.flip`, mirroring `linRicciEndo` — but with no smoothness bridge. -/
noncomputable def quadRicciEndo (Y Z : Π x : M, TangentSpace I x) (x : M) :
    TangentSpace I x →ₗ[𝕜] TangentSpace I x :=
  ((ContinuousLinearMap.coeLM 𝕜).comp
    (quadCurvatureVF AT Z x).toLinearMap).flip (Y x)

/-- The **second variation of the Ricci curvature** `δ²Ric[A]` of an unbundled affine connection on
`TM` under a connection perturbation `AT`, as a bare function `Y Z x`. On paper
`δ²Ric[A](Y, Z) = tr (X ↦ δ²R[A](X, Y) Z)`. Mirrors `linRicciAux` one variation-order up, with **no**
`A`-smoothness bridge. -/
noncomputable def quadRicciAux (Y Z : Π x : M, TangentSpace I x) (x : M) : 𝕜 :=
  LinearMap.trace 𝕜 (TangentSpace I x) (quadRicciEndo AT Y Z x)

/-- The quadratic Ricci endomorphism evaluated on a tangent vector `X₀`:
`(X₀ ↦ δ²R[A](X₀, Y) Z) X₀ = δ²R[A]` bundled at `X₀` and `Y x`. -/
@[simp]
lemma quadRicciEndo_apply (Y Z : Π x : M, TangentSpace I x) (x : M) (X₀ : TangentSpace I x) :
    quadRicciEndo AT Y Z x X₀ = quadCurvatureVF AT Z x X₀ (Y x) := by
  simp [quadRicciEndo, LinearMap.flip_apply, ContinuousLinearMap.coeLM]

/-- `quadRicciAux` as the trace of the genuine quadratic curvature endomorphism
`X₀ ↦ δ²R[A](extend X₀, Y) Z x`. This exhibits `δ²Ric[A]` as `tr δ²R[A](·, Y) Z` — the non-vacuity of
the definition (it is the trace of the genuine second variation, which `quadCurvatureVF_apply` shows
reproduces `δ²R[A]`, whose non-vacuity is `quadCurvatureAux_ne_zero`). -/
lemma quadRicciAux_apply (Y Z : Π x : M, TangentSpace I x) (x : M) :
    quadRicciAux AT Y Z x =
      LinearMap.trace 𝕜 (TangentSpace I x)
        (((ContinuousLinearMap.coeLM 𝕜).comp
          (quadCurvatureVF AT Z x).toLinearMap).flip (Y x)) :=
  rfl

/-- `C^∞`-function-linearity (tensoriality) of the quadratic Ricci curvature `δ²Ric[A]` in its first
argument: `δ²Ric[A](f • Y, Z) = f • δ²Ric[A](Y, Z)`. Clean: no extra hypotheses, from the linearity of
`flip _` in its tangent-vector argument and of `LinearMap.trace`. -/
lemma quadRicciAux_smul_left (f : M → 𝕜) (Y Z : Π x : M, TangentSpace I x) (x : M) :
    quadRicciAux AT (f • Y) Z x = f x • quadRicciAux AT Y Z x := by
  rw [quadRicciAux, quadRicciAux, quadRicciEndo, quadRicciEndo]
  rw [show (f • Y) x = f x • Y x from rfl, map_smul, map_smul]

/-- Additivity of the quadratic Ricci curvature `δ²Ric[A]` in its first argument:
`δ²Ric[A](Y + Y', Z) = δ²Ric[A](Y, Z) + δ²Ric[A](Y', Z)`. Clean. -/
lemma quadRicciAux_add_left (Y Y' Z : Π x : M, TangentSpace I x) (x : M) :
    quadRicciAux AT (Y + Y') Z x
      = quadRicciAux AT Y Z x + quadRicciAux AT Y' Z x := by
  rw [quadRicciAux, quadRicciAux, quadRicciAux, quadRicciEndo, quadRicciEndo, quadRicciEndo]
  rw [show (Y + Y') x = Y x + Y' x from rfl, map_add, map_add]

end quadRicci

section quadScalarEinstein

open scoped Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [VectorBundle ℝ E (TangentSpace I : M → Type _)]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  (AT : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)

/-- The **quadratic scalar curvature** `δ²R[A]_scal(x) = tr_g(δ²Ric[A])`: the metric trace of the
quadratic Ricci bilinear form, realised as `∑ i, δ²Ric[A](e i, e i)` over the canonical
`g`-orthonormal basis `e = stdOrthonormalBasis ℝ (TangentSpace I x)`. Mirrors `linScalarCurvature`,
but with **no `A`-smoothness bridge**. The metric enters through `RiemannianBundle`. -/
noncomputable def quadScalarCurvature (x : M) : ℝ :=
  ∑ i, quadRicciAux AT
    (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
    (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) x

/-- Unfolding lemma for `quadScalarCurvature`: the sum of the quadratic Ricci curvatures along the
diagonal of the canonical orthonormal frame, `δ²R[A]_scal = ∑ i δ²Ric[A](e i, e i) = tr_g(δ²Ric[A])`.
Makes the non-vacuity manifest: it is the honest metric trace of `quadRicciAux`, whose non-vacuity is
recorded on `quadRicciAux_apply`. -/
lemma quadScalarCurvature_apply (x : M) :
    quadScalarCurvature AT x =
      ∑ i, quadRicciAux AT
        (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
        (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) x :=
  rfl

/-- The **quadratic Einstein tensor** `δ²G[A](Y, Z) = δ²Ric[A](Y, Z) − ½ δ²R[A]_scal · g(Y, Z)` of an
affine connection on `TM` under a connection perturbation `AT`. This is the second variation of the
Einstein tensor `G = Ric − ½ R g` that is *quadratic* in the connection perturbation `A` — the
quadratic Einstein operator `δ²G[A]`. Mirrors `linEinsteinTensor` one variation-order up, but with
**no `A`-smoothness bridge** (the whole quadratic chain is unconditional).

This is the **quadratic-in-`A` half** of the full second-order Einstein variation `δ²G[h, h]`; the
other half is `δ¹G[A₂]` with `A₂` the second-order connection variation of the Levi-Civita connection
(not treated here). -/
noncomputable def quadEinsteinTensor (Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  quadRicciAux AT Y Z x
    - (1 / 2) * quadScalarCurvature AT x * inner ℝ (Y x) (Z x)

/-- Unfolding lemma for `quadEinsteinTensor`:
`δ²G[A](Y, Z) = δ²Ric[A](Y, Z) − ½ δ²R[A]_scal · g(Y, Z)`. -/
lemma quadEinsteinTensor_apply (Y Z : Π x : M, TangentSpace I x) (x : M) :
    quadEinsteinTensor AT Y Z x =
      quadRicciAux AT Y Z x
        - (1 / 2) * quadScalarCurvature AT x * inner ℝ (Y x) (Z x) :=
  rfl

/-- `C^∞`-function-linearity (tensoriality) of the quadratic Einstein tensor `δ²G[A]` in its first
argument: `δ²G[A](f • Y, Z) = f • δ²G[A](Y, Z)`. Follows from the first-slot tensoriality of the
quadratic Ricci (`quadRicciAux_smul_left`) and the linearity of the metric in its first argument
(`real_inner_smul_left`); no extra hypotheses. -/
lemma quadEinsteinTensor_smul_left
    (f : M → ℝ) (Y Z : Π x : M, TangentSpace I x) (x : M) :
    quadEinsteinTensor AT (f • Y) Z x = f x • quadEinsteinTensor AT Y Z x := by
  rw [quadEinsteinTensor, quadEinsteinTensor, quadRicciAux_smul_left]
  rw [show (f • Y) x = f x • Y x from rfl, real_inner_smul_left, smul_eq_mul, smul_eq_mul]
  ring

/-- **Non-vacuity / the trace identity for the quadratic Einstein tensor `δ²G[A]`.** Contracting
`δ²G[A]` with the metric along the canonical orthonormal frame yields
`tr_g(δ²G[A]) = δ²R[A]_scal − ½ δ²R[A]_scal · d = δ²R[A]_scal (1 − d/2)`, where `d = finrank ℝ E` is
the manifold dimension — the quadratic (second-variation) analogue of the classical Einstein trace
identity (in particular `tr_g(δ²G[A]) = 0` in dimension `2`). This exhibits `quadEinsteinTensor` as a
genuine modification of `quadRicciAux` by the quadratic-scalar-curvature/metric term (not identically
`δ²Ric[A]`, nor identically zero by fiat). Mirrors `sum_linEinsteinTensor_frame_diag` one
variation-order up. -/
lemma sum_quadEinsteinTensor_frame_diag (x : M) :
    ∑ i, quadEinsteinTensor AT
        (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i))
        (extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) x
      = quadScalarCurvature AT x
        - (1 / 2) * quadScalarCurvature AT x
          * (Module.finrank ℝ (TangentSpace I x) : ℝ) := by
  have hmet : ∀ i, inner ℝ
      ((extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) x)
      ((extend E ((stdOrthonormalBasis ℝ (TangentSpace I x)) i)) x) = (1 : ℝ) := by
    intro i
    rw [extend_apply_self, real_inner_self_eq_norm_sq,
      (stdOrthonormalBasis ℝ (TangentSpace I x)).orthonormal.1 i]
    norm_num
  simp only [quadEinsteinTensor, hmet, mul_one]
  rw [Finset.sum_sub_distrib, ← quadScalarCurvature]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end quadScalarEinstein

end IsCovariantDerivativeOn

/-! ### A concrete non-vacuity witness

We instantiate on the base `ℝ²` (model `𝓘(ℝ, ℝ²)`, so `TangentSpace = ℝ²`) with the trivial fibre
`ℝ²`, and take `A` to be the constant connection one-form whose two direction-components are the
*non-commuting* matrices `M0`, `M1`. The second variation `δ²R[A]` at the point `0`, in the two
coordinate directions, is their commutator `[M0, M1] ![1, 0] = ![0, -2] ≠ 0`. Hence
`quadCurvatureAux` is genuinely nonzero and the decomposition is non-trivial. -/

namespace IsCovariantDerivativeOn.CurvatureVariationWitness

open Bundle Matrix
open scoped Manifold

/-- Base (and fibre) model space `ℝ²`. -/
abbrev Ba : Type := Fin 2 → ℝ
/-- Fibre model space `ℝ²`. -/
abbrev Fi : Type := Fin 2 → ℝ

/-- First direction-component of the witness connection one-form: the diagonal `diag(1, -1)`. -/
noncomputable def M0 : Fi →L[ℝ] Fi := (Matrix.toLin' !![1, 0; 0, -1]).toContinuousLinearMap
/-- Second direction-component of the witness connection one-form: the swap `[[0,1],[1,0]]`.
`M0` and `M1` do not commute. -/
noncomputable def M1 : Fi →L[ℝ] Fi := (Matrix.toLin' !![0, 1; 1, 0]).toContinuousLinearMap

/-- The witness connection one-form as a bilinear map: `A σ t = t 0 • M0 σ + t 1 • M1 σ`. -/
noncomputable def Abil : Fi →ₗ[ℝ] Ba →ₗ[ℝ] Fi where
  toFun σ :=
    { toFun := fun t => t 0 • M0 σ + t 1 • M1 σ
      map_add' := fun a b => by
        show (a + b) 0 • M0 σ + (a + b) 1 • M1 σ
          = (a 0 • M0 σ + a 1 • M1 σ) + (b 0 • M0 σ + b 1 • M1 σ)
        simp only [Pi.add_apply, add_smul]; abel
      map_smul' := fun c a => by
        show (c • a) 0 • M0 σ + (c • a) 1 • M1 σ = c • (a 0 • M0 σ + a 1 • M1 σ)
        simp only [Pi.smul_apply, smul_eq_mul, smul_add, mul_smul] }
  map_add' σ σ' := by
    refine LinearMap.ext fun t => ?_
    show t 0 • M0 (σ + σ') + t 1 • M1 (σ + σ')
      = (t 0 • M0 σ + t 1 • M1 σ) + (t 0 • M0 σ' + t 1 • M1 σ')
    simp only [map_add, smul_add]; abel
  map_smul' c σ := by
    refine LinearMap.ext fun t => ?_
    show t 0 • M0 (c • σ) + t 1 • M1 (c • σ) = c • (t 0 • M0 σ + t 1 • M1 σ)
    simp only [map_smul, smul_add, smul_comm (t _) c]

/-- The witness connection one-form, packaged as a `Fi →ₗ (Ba →L Fi)` (continuous in the fibre slot
by finite-dimensionality). -/
noncomputable def AL : Fi →ₗ[ℝ] Ba →L[ℝ] Fi where
  toFun σ := (Abil σ).toContinuousLinearMap
  map_add' σ σ' := by
    refine ContinuousLinearMap.ext fun t => ?_
    simp only [_root_.add_apply, LinearMap.coe_toContinuousLinearMap', map_add]
  map_smul' c σ := by
    refine ContinuousLinearMap.ext fun t => ?_
    simp only [_root_.smul_apply, LinearMap.coe_toContinuousLinearMap', map_smul, RingHom.id_apply]

/-- The witness connection one-form as a nested continuous-linear map `Fi →L Ba →L Fi`. -/
noncomputable def Aform : Fi →L[ℝ] Ba →L[ℝ] Fi := AL.toContinuousLinearMap

@[simp] lemma Aform_apply (t : Ba) (σ : Fi) : Aform σ t = t 0 • M0 σ + t 1 • M1 σ := rfl

/-- The witness perturbation `A`, at the exact type expected by `quadCurvatureAux` on the trivial
bundle over `ℝ²` (constant in the base point). -/
noncomputable def Awit : Π x : Ba, (Bundle.Trivial Ba Fi) x →L[ℝ]
    TangentSpace (𝓘(ℝ, Ba)) x →L[ℝ] (Bundle.Trivial Ba Fi) x := fun _ => Aform

/-- **Non-vacuity of the second variation.** The quadratic term `δ²R[A]` is genuinely nonzero: for
the constant non-commuting witness one-form, the second variation at `0` in the two coordinate
directions is the commutator `[M0, M1] ![1, 0] = ![0, -2] ≠ 0`. Hence the decomposition
`curvatureAux_addOneForm_eq` is not the trivial `R = R + 0 + 0`. -/
theorem quadCurvatureAux_ne_zero :
    IsCovariantDerivativeOn.quadCurvatureAux (I := 𝓘(ℝ, Ba)) (V := Bundle.Trivial Ba Fi)
      Awit (fun _ => ![1, 0]) (fun _ => ![0, 1]) (fun _ => ![1, 0]) 0 ≠ 0 := by
  show Aform (Aform ![1, 0] ![0, 1]) ![1, 0] - Aform (Aform ![1, 0] ![1, 0]) ![0, 1] ≠ 0
  simp only [Aform_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_smul, one_smul, add_zero, zero_add]
  intro h
  have h1 := congrFun h 1
  simp only [M0, M1, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply,
    Matrix.mulVec_cons, Matrix.mulVec_empty, Pi.sub_apply, Pi.zero_apply] at h1
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h1

end IsCovariantDerivativeOn.CurvatureVariationWitness

end
