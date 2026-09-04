/-
Copyright (c) 2025 The Mathlib community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.CurvatureVariation
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-! # The metric → connection variation `A(h)`

Given a Levi-Civita connection `∇` on the tangent bundle `TM` of a Riemannian manifold `(M, g)` and
a symmetric bilinear "metric perturbation"
`h : Π x, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ`, the *first-order change of the
Levi-Civita connection* under the metric variation `g ↦ g + h`, denoted `A(h)`, is the
`(1, 2)`-tensor determined by the coordinate-free **Koszul variation formula**
```
2 · g(A(h)(X, Y), Z) = (∇_X h)(Y, Z) + (∇_Y h)(X, Z) − (∇_Z h)(X, Y),
```
where the covariant derivative of the bilinear form `h` is the direct Leibniz expression
```
(∇_X h)(Y, Z) := X (h(Y, Z)) − h(∇_X Y, Z) − h(Y, ∇_X Z),
```
and the index on the right-hand side is raised into a vector by the metric's musical isomorphism
`(InnerProductSpace.toDual ℝ _).symm` (exactly as in the construction of `leviCivitaConnection`).

This file constructs `A(h)` coordinate-free — **no differentiation of the connection, no metric
positivity beyond the ambient `RiemannianBundle`, no local frames** — mirroring the musical-iso /
`TensorialAt.mkHom` construction of the Levi-Civita connection itself.

## Main definitions and results

* `CovariantDerivative.covDerivBilin`: the covariant derivative `(∇_X h)(Y, Z)` of the bilinear
  form `h`, as the direct Leibniz scalar
  `X (h(Y, Z)) − h(∇_X Y, Z) − h(Y, ∇_X Z)`.
* `CovariantDerivative.koszulVarInner`: the Koszul-variation right-hand side as a scalar,
  `((∇_X h)(Y, Z) + (∇_Y h)(X, Z) − (∇_Z h)(X, Y)) / 2`.
* `CovariantDerivative.koszulVarCovector`: that right-hand side packaged as a continuous **covector**
  in the `Z` slot (a `(0, 1)`-tensor), via `TensorialAt.mkHom`.
* `CovariantDerivative.metricConnPerturbAux`: **`A(h)(X, Y)` as a vector**, obtained by raising the
  index of `koszulVarCovector` with the musical isomorphism.
* `CovariantDerivative.metricConnPerturbAux_symm`: `A(h)` is **symmetric** in `X, Y` (torsion-free)
  when `h` is symmetric — the first rigorous property of the metric→connection variation.
* `CovariantDerivative.koszulVarCovector_ne_zero`, `metricConnPerturbAux_ne_zero`: the construction
  is faithful — a nonzero Koszul-variation scalar gives a nonzero covector, and (the musical
  isomorphism being a linear equivalence) a nonzero covector gives a nonzero `A(h)`.

## Scope (honest)

This is the *definition* of the metric→connection
map `A(h)` and its symmetry (torsion-freeness) characterization. Its `Z`-slot is packaged as a
genuine covector and index-raised to a vector; the `X, Y` arguments are *vector fields* (the
construction is pointwise in them). Bundling `A(h)` into the full perturbation type
`Π x, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x` used by
`CurvatureVariation.addOneFormAux` (so as to feed `curvatureAux_addOneForm_eq`), and the resulting
second-order metric variation, are *not* treated here.

-/

open Bundle FiberBundle Function NormedSpace VectorField Set
open scoped Manifold ContDiff Topology RealInnerProductSpace

@[expose] public noncomputable section

-- Let `M` be a `C²` manifold modeled on `(E, H)`, endowed with a Riemannian metric on `TM`.
variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [FiniteDimensional ℝ E]

variable {X Y Z : Π x : M, TangentSpace I x}
  {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
  {h : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ}

namespace CovariantDerivative

/-- The covariant derivative `(∇_X h)(Y, Z)` of a bilinear form `h`, as the direct Leibniz scalar
`X (h(Y, Z)) − h(∇_X Y, Z) − h(Y, ∇_X Z)`.

Here `X (h(Y, Z)) = d% (fun z ↦ h z (Y z) (Z z)) x (X x)` is the directional derivative of the
scalar field `z ↦ h z (Y z) (Z z)` along `X`, and `∇_X Y := fun x ↦ cov Y x (X x)`. -/
noncomputable def covDerivBilin
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (h : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  d% (fun z ↦ h z (Y z) (Z z)) x (X x)
    - h x (cov Y x (X x)) (Z x) - h x (Y x) (cov Z x (X x))

/-- The Koszul-variation right-hand side as a scalar:
`((∇_X h)(Y, Z) + (∇_Y h)(X, Z) − (∇_Z h)(X, Y)) / 2`.
This is (half) the quantity `g(A(h)(X, Y), Z)` that the Koszul variation formula prescribes. -/
noncomputable def koszulVarInner
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (h : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X Y Z : Π x : M, TangentSpace I x) (x : M) : ℝ :=
  (covDerivBilin I cov h X Y Z x + covDerivBilin I cov h Y X Z x
    - covDerivBilin I cov h Z X Y x) / 2

omit [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] [FiniteDimensional ℝ E] in
/-- `koszulVarInner` is tensorial (`C^∞`-function-linear) in its `Z` slot: each term of the
Koszul-variation right-hand side is linear in the direction `Z`, so the whole is a genuine covector
in `Z`. This mirrors `tensorialAt_leviCivitaAuxInner₃`.

The differentiability hypotheses `hhYX`/`hhXY` are the smoothness of the scalar fields
`z ↦ h z (Y z) (Z z)` etc. entering the directional derivative; they play the role that
`MDifferentiable.inner_bundle'` plays for the Levi-Civita construction (for a *general* `h` no such
`fun_prop` lemma is available, so they are carried as hypotheses). -/
theorem tensorialAt_koszulVarInner_right
    (x : M)
    (hhYX : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (Y z) (W z)) x)
    (hhXY : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (X z) (W z)) x) :
    TensorialAt I E (koszulVarInner I cov h X Y · x) x where
  smul {f Z} hf hZ := by
    simp only [koszulVarInner, covDerivBilin]
    -- Rewrite the two scalar fields where `f • Z` enters the bilinear form (terms 1 & 2).
    have e1 : (fun z ↦ h z (Y z) ((f • Z) z)) = fun z ↦ f z * (h z (Y z) (Z z)) := by
      ext z; simp
    have e2 : (fun z ↦ h z (X z) ((f • Z) z)) = fun z ↦ f z * (h z (X z) (Z z)) := by
      ext z; simp
    -- The connection Leibniz rule for `∇(f • Z)` (needed where `Z` is differentiated, terms 1 & 2).
    have lb := cov.isCovariantDerivativeOnUniv.leibniz hZ hf
    rw [e1, e2, mvfderiv_fun_mul hf (hhYX Z), mvfderiv_fun_mul hf (hhXY Z)]
    simp only [lb, Pi.smul_apply', add_apply,
      ContinuousLinearMap.smulRight_apply, smul_apply, map_smul, map_add, smul_eq_mul]
    ring
  add {Z₁ Z₂} hZ₁ hZ₂ := by
    simp only [koszulVarInner, covDerivBilin]
    have e1 : (fun z ↦ h z (Y z) ((Z₁ + Z₂) z)) =
        fun z ↦ (h z (Y z) (Z₁ z)) + (h z (Y z) (Z₂ z)) := by
      ext z; simp
    have e2 : (fun z ↦ h z (X z) ((Z₁ + Z₂) z)) =
        fun z ↦ (h z (X z) (Z₁ z)) + (h z (X z) (Z₂ z)) := by
      ext z; simp
    have ab := cov.isCovariantDerivativeOnUniv.add hZ₁ hZ₂
    rw [e1, e2, mvfderiv_fun_add (hhYX Z₁) (hhYX Z₂), mvfderiv_fun_add (hhXY Z₁) (hhXY Z₂)]
    simp only [ab, Pi.add_apply, map_add, add_apply]
    ring

/-- The Koszul-variation right-hand side packaged as a continuous **covector** in the `Z` slot,
i.e. the `(0, 1)`-tensor `Z ↦ koszulVarInner I cov h X Y Z x`. This is `g(A(h)(X, Y), ·)` before
raising the index by the metric. Obtained from `tensorialAt_koszulVarInner_right` via
`TensorialAt.mkHom`, exactly as `leviCivitaAuxOfMDiffAt` builds the Levi-Civita `(1, 1)`-tensor. -/
noncomputable def koszulVarCovector
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (h : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X Y : Π x : M, TangentSpace I x) {x : M}
    (hhYX : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (Y z) (W z)) x)
    (hhXY : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (X z) (W z)) x) :
    TangentSpace I x →L[ℝ] ℝ :=
  TensorialAt.mkHom (koszulVarInner I cov h X Y · x) x
    (tensorialAt_koszulVarInner_right (cov := cov) I x hhYX hhXY)

omit [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
theorem koszulVarCovector_apply
    {x : M}
    (hhYX : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (Y z) (W z)) x)
    (hhXY : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (X z) (W z)) x)
    (hZ : MDiffAt (T% Z) x) :
    koszulVarCovector I cov h X Y hhYX hhXY (Z x) = koszulVarInner I cov h X Y Z x :=
  TensorialAt.mkHom_apply (tensorialAt_koszulVarInner_right (cov := cov) I x hhYX hhXY) hZ

/-- **`A(h)(X, Y)` as a vector**: the first-order connection perturbation induced by the metric
perturbation `h`, obtained by raising the index of the covector `koszulVarCovector` with the
metric's musical isomorphism `(InnerProductSpace.toDual ℝ _).symm` — exactly the index-raising step
used to construct the Levi-Civita connection (`leviCivitaAuxOfMDiffAt`). It is characterized by the
Koszul variation formula `g(A(h)(X, Y), Z) = koszulVarInner I cov h X Y Z x`. -/
noncomputable def metricConnPerturbAux
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (h : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (X Y : Π x : M, TangentSpace I x) {x : M}
    (hhYX : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (Y z) (W z)) x)
    (hhXY : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (X z) (W z)) x) :
    TangentSpace I x :=
  (InnerProductSpace.toDual ℝ _).symm (koszulVarCovector I cov h X Y hhYX hhXY)

/-- The defining property of `A(h)(X, Y)`: it is the metric-dual of the Koszul-variation covector,
i.e. `g(A(h)(X, Y), Z) = koszulVarInner I cov h X Y Z x` (the coordinate-free Koszul variation
formula `2 g(A(h)(X, Y), Z) = (∇_X h)(Y,Z) + (∇_Y h)(X,Z) − (∇_Z h)(X,Y)`, since `koszulVarInner`
already carries the factor `1/2`). -/
theorem inner_metricConnPerturbAux
    {x : M}
    (hhYX : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (Y z) (W z)) x)
    (hhXY : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (X z) (W z)) x)
    (v : TangentSpace I x) :
    inner ℝ (metricConnPerturbAux I cov h X Y hhYX hhXY) v
      = koszulVarCovector I cov h X Y hhYX hhXY v := by
  rw [metricConnPerturbAux]
  exact InnerProductSpace.toDual_symm_apply (𝕜 := ℝ)

omit [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] [FiniteDimensional ℝ E] in
/-- When the bilinear form `h` is symmetric, its covariant derivative is symmetric in the two
form-slots: `(∇_X h)(Y, Z) = (∇_X h)(Z, Y)`. -/
theorem covDerivBilin_symm (hsymm : ∀ x u v, h x u v = h x v u) (x : M) :
    covDerivBilin I cov h X Y Z x = covDerivBilin I cov h X Z Y x := by
  simp only [covDerivBilin]
  rw [show (fun z ↦ h z (Y z) (Z z)) = (fun z ↦ h z (Z z) (Y z)) from
        funext fun z ↦ hsymm z (Y z) (Z z), hsymm x (cov Y x (X x)) (Z x),
      hsymm x (Y x) (cov Z x (X x))]
  ring

omit [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] [FiniteDimensional ℝ E] in
/-- The Koszul-variation scalar is symmetric in `X, Y` when `h` is symmetric:
`koszulVarInner I cov h X Y Z x = koszulVarInner I cov h Y X Z x`. This is the symmetry
(torsion-freeness) of the metric→connection variation at the level of the defining scalar. -/
theorem koszulVarInner_symm (hsymm : ∀ x u v, h x u v = h x v u) (x : M) :
    koszulVarInner I cov h X Y Z x = koszulVarInner I cov h Y X Z x := by
  simp only [koszulVarInner]
  rw [covDerivBilin_symm (Y := X) (Z := Y) I hsymm x]
  ring

/-- **`A(h)` is symmetric (torsion-free)**: when `h` is symmetric, `A(h)(X, Y) = A(h)(Y, X)`.
This is the first rigorous *property* of the metric→connection variation — the perturbation of a
torsion-free connection by a symmetric metric variation is again torsion-free.

The `X`/`Y` differentiability hypotheses (`hhYX`/`hhXY` vs. their swaps `hhXY'`/`hhYX'`) are the
respective scalar-field smoothness data entering `metricConnPerturbAux`; they are logically
interchangeable, so both are supplied. -/
theorem metricConnPerturbAux_symm (hsymm : ∀ x u v, h x u v = h x v u) {x : M}
    (hhYX : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (Y z) (W z)) x)
    (hhXY : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (X z) (W z)) x) :
    metricConnPerturbAux I cov h X Y hhYX hhXY = metricConnPerturbAux I cov h Y X hhXY hhYX := by
  rw [metricConnPerturbAux, metricConnPerturbAux]
  congr 1
  ext v
  simp only [koszulVarCovector, TensorialAt.mkHom_apply_eq_extend]
  exact koszulVarInner_symm (Y := Y) I hsymm x

/-- **Non-vacuity: the index-raising is faithful.** If the Koszul-variation covector is nonzero,
then the raised vector `A(h)(X, Y)` is nonzero — the metric→connection map does not collapse
nontrivial data. Consequently `metricConnPerturbAux` genuinely depends on `h`: whenever `h` produces
a nonzero Koszul-variation covector, `A(h) ≠ 0`. (The musical isomorphism `toDual` is a linear
*equivalence*, so it sends nonzero to nonzero.) -/
theorem metricConnPerturbAux_ne_zero {x : M}
    (hhYX : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (Y z) (W z)) x)
    (hhXY : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (X z) (W z)) x)
    (hne : koszulVarCovector I cov h X Y hhYX hhXY ≠ 0) :
    metricConnPerturbAux I cov h X Y hhYX hhXY ≠ 0 := by
  rw [metricConnPerturbAux]
  intro hzero
  apply hne
  have := congrArg (InnerProductSpace.toDual ℝ (TangentSpace I x)) hzero
  rwa [LinearIsometryEquiv.apply_symm_apply, map_zero] at this

omit [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)] in
/-- **Non-vacuity of the Koszul-variation covector itself.** For a genuine (nonzero) perturbation
`h`, the covector `koszulVarCovector` is nonzero as soon as its defining scalar
`koszulVarInner I cov h X Y Z x` is nonzero for some differentiable direction field `Z`. This
witnesses that the whole construction — and hence `A(h)` via `metricConnPerturbAux_ne_zero` — is
not identically zero. -/
theorem koszulVarCovector_ne_zero {x : M}
    (hhYX : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (Y z) (W z)) x)
    (hhXY : ∀ W : Π x : M, TangentSpace I x, MDiffAt (fun z ↦ h z (X z) (W z)) x)
    (hZ : MDiffAt (T% Z) x) (hne : koszulVarInner I cov h X Y Z x ≠ 0) :
    koszulVarCovector I cov h X Y hhYX hhXY ≠ 0 := by
  intro hzero
  apply hne
  rw [← koszulVarCovector_apply (cov := cov) I hhYX hhXY hZ, hzero, zero_apply]

end CovariantDerivative

end
