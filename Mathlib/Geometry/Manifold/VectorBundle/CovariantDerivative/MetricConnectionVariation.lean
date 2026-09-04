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
* `CovariantDerivative.MetricConnPerturbWitness`: a **concrete non-vacuity witness** on flat
  Euclidean space `ℝ²`. With the flat Levi-Civita connection, the constant basis field `cVF e₀` in
  all three slots and the nonconstant symmetric metric perturbation `hPert e₀ x = ⟪e₀, x⟫ • innerSL`,
  the Koszul-variation scalar is `koszulVarInner_witness : … = 1/2` (hence
  `koszulVarInner_ne_zero_witness`), which chains through the two faithfulness lemmas to
  `koszulVarCovector_ne_zero_witness` and `metricConnPerturbAux_ne_zero_witness : A(h) ≠ 0`. The key
  geometric input is `leviCivitaConnection_cVF_eq_zero` (`∇` annihilates constant fields on the flat
  model). This discharges the mathematically-substantive `koszulVarInner ≠ 0` conditional; the
  smoothness data `hhYX`/`hhXY` is carried as a hypothesis (see the scope note).

## Scope (honest)

This is the *definition* of the metric→connection
map `A(h)` and its symmetry (torsion-freeness) characterization. Its `Z`-slot is packaged as a
genuine covector and index-raised to a vector; the `X, Y` arguments are *vector fields* (the
construction is pointwise in them). Bundling `A(h)` into the full perturbation type
`Π x, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x` used by
`CurvatureVariation.addOneFormAux` (so as to feed `curvatureAux_addOneForm_eq`), and the resulting
second-order metric variation, are *not* treated here.

The differentiability hypotheses `hhYX`/`hhXY` of `koszulVarCovector`/`metricConnPerturbAux` are
stated for *all* direction fields `W` (mirroring the `∀ W` shape of the covector's `mkHom` inputs).
They are genuinely dischargeable only on *differentiable* `W` (see
`MetricConnPerturbWitness.mdiff_hPert_of_mdiff`), so the concrete witness
`metricConnPerturbAux_ne_zero_witness` carries them as hypotheses: it discharges the
mathematically-substantive `koszulVarInner ≠ 0` conditional unconditionally, but not the
well-formedness smoothness datum. Conditioning these hypotheses on `MDiffAt (T% W) x` (a
statement-improvement leaving all proofs intact, since the tensoriality proof only ever applies them
to differentiable slots) would make the whole chain fully unconditional.

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

/-! ## A concrete non-vacuity witness: `A(h) ≠ 0` on flat Euclidean space `ℝ²`

We discharge the mathematically-substantive conditional of `metricConnPerturbAux_ne_zero`
(namely that the Koszul-variation scalar `koszulVarInner` is nonzero) with a fully explicit choice:
the flat Levi-Civita connection of `ℝ²`, the constant basis field `cVF e₀` in all three slots, and
the nonconstant symmetric metric perturbation `hPert e₀ x = ⟪e₀, x⟫ • innerSL ℝ`. The concrete
Koszul-variation scalar computes to `1/2` (`koszulVarInner_witness`), and this chains through
`koszulVarCovector_ne_zero` and `metricConnPerturbAux_ne_zero` to `A(h) ≠ 0`
(`metricConnPerturbAux_ne_zero_witness`).

The key geometric fact making the computation explicit is `leviCivitaConnection_cVF_eq_zero`: on the
flat/constant-metric model, the Levi-Civita connection annihilates every constant vector field
(`∇(cVF e) = 0`), so the two connection (Christoffel) terms of `covDerivBilin` vanish and only the
directional derivative of the metric perturbation survives. -/
namespace MetricConnPerturbWitness

open scoped RealInnerProductSpace

/-- A constant vector field `z ↦ a` on the tangent bundle of `ℝ²`. -/
def cVF (a : EuclideanSpace ℝ (Fin 2)) :
    Π z : EuclideanSpace ℝ (Fin 2), TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) z := fun _ ↦ a

/-- The symmetric, nonconstant metric perturbation `h x = ⟪v₀, x⟫ • innerSL ℝ`, i.e.
`h x u w = ⟪v₀, x⟫ * ⟪u, w⟫`. It is symmetric in `(u, w)` and its `x`-dependence is linear
(nonconstant for `v₀ ≠ 0`), so it produces a nonzero Koszul variation. -/
noncomputable def hPert (v0 : EuclideanSpace ℝ (Fin 2)) :
    Π x : EuclideanSpace ℝ (Fin 2), TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) x →L[ℝ]
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) x →L[ℝ] ℝ :=
  fun x ↦ (⟪v0, x⟫) • (innerSL ℝ)

/-- A constant vector field on the tangent bundle of the vector-space model `ℝ²` is differentiable:
its coordinate in the (identity) trivialization is constant. -/
lemma cVF_mdiff (a x : EuclideanSpace ℝ (Fin 2)) : MDiffAt (T% (cVF a)) x := by
  rw [mdifferentiableAt_section]
  exact (mdifferentiableAt_const (c := a)).congr_of_eventuallyEq
    (by filter_upwards with y; simp [cVF])

lemma hPert_apply (v0 x u w : EuclideanSpace ℝ (Fin 2)) : hPert v0 x u w = ⟪v0, x⟫ * ⟪u, w⟫ := by
  show ((⟪v0, x⟫ • (innerSL ℝ)) u) w = _
  rw [smul_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]

/-- The Lie bracket of two constant vector fields on `ℝ²` vanishes (both `fderiv`s of a constant are
zero). -/
lemma mlie_cVF (v w x : EuclideanSpace ℝ (Fin 2)) :
    VectorField.mlieBracket 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (cVF v) (cVF w) x = 0 := by
  rw [← mlieBracketWithin_univ, mlieBracketWithin_eq_lieBracketWithin]
  show VectorField.lieBracketWithin ℝ (fun _ ↦ v) (fun _ ↦ w) univ x = 0
  simp [VectorField.lieBracketWithin]

/-- On the model space `ℝ²`, the manifold directional derivative `d%` of a differentiable scalar
field is the ordinary Fréchet derivative `fderiv` (chart = identity). -/
lemma mvfderiv_eq_fderiv (g : EuclideanSpace ℝ (Fin 2) → ℝ) (x : EuclideanSpace ℝ (Fin 2))
    (hg : DifferentiableAt ℝ g x) (e : EuclideanSpace ℝ (Fin 2)) :
    d% g x e = fderiv ℝ g x e := by
  rw [hg.mdifferentiableAt.mvfderiv]
  simp only [writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.comp_id, Function.id_comp, PartialEquiv.refl_symm, modelWithCornersSelf_coe,
    range_id, fderivWithin_univ]
  rfl

/-- The inner product of the Levi-Civita covariant derivative of a constant field against a
constant field vanishes: on the flat model every `d% ⟪·,·⟫` and Lie-bracket term is zero. -/
lemma inner_leviCivita_cVF (e v w x : EuclideanSpace ℝ (Fin 2)) :
    ⟪leviCivitaConnection 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2))
      (cVF e) x (cVF v x), (cVF w x)⟫ = 0 := by
  rw [leviCivitaConnection_apply_inner (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)))
    (M := EuclideanSpace ℝ (Fin 2)) (X := cVF v) (Y := cVF e) (Z := cVF w)
    (cVF_mdiff v x) (cVF_mdiff e x) (cVF_mdiff w x)]
  have hc : ∀ (p q : EuclideanSpace ℝ (Fin 2)),
      (fun z : EuclideanSpace ℝ (Fin 2) ↦ ⟪cVF p z, cVF q z⟫) = fun _ ↦ ⟪p, q⟫ := fun p q ↦ rfl
  simp only [hc, mvfderiv_const, mlie_cVF, zero_apply]
  simp

/-- **`∇(cVF e) = 0`.** The flat Levi-Civita connection of the constant Euclidean metric annihilates
every constant vector field. -/
lemma leviCivitaConnection_cVF_eq_zero (e : EuclideanSpace ℝ (Fin 2))
    {x : EuclideanSpace ℝ (Fin 2)} (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) x) :
    leviCivitaConnection 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) (cVF e) x v
      = 0 := by
  apply ext_inner_left ℝ
  intro w
  rw [inner_zero_right, real_inner_comm]
  simpa [cVF] using inner_leviCivita_cVF e v w x

/-- The surviving directional-derivative term: `d% (fun z ↦ h z e e) x e = ⟪v₀, e⟫ * ⟪e, e⟫`. -/
lemma mvfderiv_hPert (v0 e x : EuclideanSpace ℝ (Fin 2)) :
    d% (fun z : EuclideanSpace ℝ (Fin 2) ↦ hPert v0 z (cVF e z) (cVF e z)) x (cVF e x)
      = ⟪v0, e⟫ * ⟪e, e⟫ := by
  have hfun : (fun z : EuclideanSpace ℝ (Fin 2) ↦ hPert v0 z (cVF e z) (cVF e z))
      = fun z ↦ ⟪v0, z⟫ * ⟪e, e⟫ := by
    ext z; simp only [cVF]; rw [hPert_apply]
  have hd2 : DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin 2) ↦ ⟪v0, z⟫) x :=
    (innerSL ℝ v0).differentiableAt.congr_of_eventuallyEq
      (by filter_upwards with z; rw [innerSL_apply_apply])
  have hdiff : DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin 2) ↦ ⟪v0, z⟫ * ⟪e, e⟫) x :=
    hd2.mul (differentiableAt_const _)
  have hfd : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin 2) ↦ ⟪v0, z⟫) x e = ⟪v0, e⟫ := by
    have heq : (fun z : EuclideanSpace ℝ (Fin 2) ↦ ⟪v0, z⟫) = ⇑(innerSL ℝ v0) := by
      ext z; rw [innerSL_apply_apply]
    rw [heq, ContinuousLinearMap.fderiv, innerSL_apply_apply]
  rw [show cVF e x = e from rfl, hfun, mvfderiv_eq_fderiv _ x hdiff e, fderiv_mul_const hd2]
  rw [smul_apply, smul_eq_mul, hfd, mul_comm]

/-- The covariant derivative of `hPert v₀` in the all-constant configuration: the two connection
terms vanish by `leviCivitaConnection_cVF_eq_zero`, leaving `⟪v₀, e⟫ * ⟪e, e⟫`. -/
lemma covDerivBilin_cVF (v0 e x : EuclideanSpace ℝ (Fin 2)) :
    covDerivBilin 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      (leviCivitaConnection 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)))
      (hPert v0) (cVF e) (cVF e) (cVF e) x = ⟪v0, e⟫ * ⟪e, e⟫ := by
  rw [covDerivBilin]
  simp only [leviCivitaConnection_cVF_eq_zero, map_zero, zero_apply, sub_zero]
  rw [mvfderiv_hPert]

/-- The Koszul-variation scalar in the all-constant configuration equals `(⟪v₀, e⟫ * ⟪e, e⟫) / 2`
(the three `covDerivBilin` terms are identical, giving `(T + T − T)/2 = T/2`). -/
lemma koszulVarInner_cVF (v0 e x : EuclideanSpace ℝ (Fin 2)) :
    koszulVarInner 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      (leviCivitaConnection 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)))
      (hPert v0) (cVF e) (cVF e) (cVF e) x = (⟪v0, e⟫ * ⟪e, e⟫) / 2 := by
  rw [koszulVarInner, covDerivBilin_cVF]; ring

/-- The explicit basis vector `e₀ = (1, 0) ∈ ℝ²`. -/
def e0 : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.single 0 1

@[simp] lemma inner_e0_e0 : (⟪e0, e0⟫ : ℝ) = 1 := by simp [e0]

/-- **Concrete nonzero Koszul-variation scalar.** For `v₀ = e = e₀`, `koszulVarInner = 1/2`. -/
lemma koszulVarInner_witness (x : EuclideanSpace ℝ (Fin 2)) :
    koszulVarInner 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      (leviCivitaConnection 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)))
      (hPert e0) (cVF e0) (cVF e0) (cVF e0) x = 1 / 2 := by
  rw [koszulVarInner_cVF, inner_e0_e0]; norm_num

/-- **`koszulVarInner ≠ 0` for the explicit choice** — discharging the mathematically-substantive
conditional of `koszulVarCovector_ne_zero`/`metricConnPerturbAux_ne_zero`. -/
theorem koszulVarInner_ne_zero_witness (x : EuclideanSpace ℝ (Fin 2)) :
    koszulVarInner 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      (leviCivitaConnection 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)))
      (hPert e0) (cVF e0) (cVF e0) (cVF e0) x ≠ 0 := by
  rw [koszulVarInner_witness]; norm_num

/-- If `W` is differentiable, the scalar field `z ↦ hPert e₀ z (cVF e₀ z) (W z)` is differentiable
— the smoothness/well-formedness datum `koszulVarCovector` requires in its `Z` slot. (For an
*arbitrary* `W` this is false, which is why the theorems below carry `hhYX`/`hhXY` as
hypotheses.) -/
lemma mdiff_hPert_of_mdiff {x : EuclideanSpace ℝ (Fin 2)}
    (W : Π z : EuclideanSpace ℝ (Fin 2), TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) z)
    (hW : MDiffAt (T% W) x) :
    MDiffAt (fun z ↦ hPert e0 z (cVF e0 z) (W z)) x := by
  have hfun : (fun z : EuclideanSpace ℝ (Fin 2) ↦ hPert e0 z (cVF e0 z) (W z))
      = fun z ↦ (⟪e0, z⟫) * (⟪(cVF e0 z), W z⟫) := by
    ext z
    show ((⟪e0, z⟫ • (innerSL ℝ)) (cVF e0 z)) (W z) = _
    rw [smul_apply, smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [hfun]
  refine MDifferentiableAt.mul ?_ (MDifferentiableAt.inner_bundle (cVF_mdiff e0 x) hW)
  exact (innerSL ℝ e0).mdifferentiableAt.congr_of_eventuallyEq
    (by filter_upwards with z; rw [innerSL_apply_apply])

/-- **The Koszul-variation covector is nonzero for the explicit choice.** Given the smoothness data
`hhYX`/`hhXY` (dischargeable on differentiable directions by `mdiff_hPert_of_mdiff`), the concrete
covector is nonzero: its value `1/2` on the differentiable direction `cVF e₀` is provided by
`koszulVarInner_ne_zero_witness`. -/
theorem koszulVarCovector_ne_zero_witness {x : EuclideanSpace ℝ (Fin 2)}
    (hhYX : ∀ W : Π z : EuclideanSpace ℝ (Fin 2), TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) z,
      MDiffAt (fun z ↦ hPert e0 z (cVF e0 z) (W z)) x)
    (hhXY : ∀ W : Π z : EuclideanSpace ℝ (Fin 2), TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) z,
      MDiffAt (fun z ↦ hPert e0 z (cVF e0 z) (W z)) x) :
    koszulVarCovector 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      (leviCivitaConnection 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)))
      (hPert e0) (cVF e0) (cVF e0) hhYX hhXY ≠ 0 :=
  koszulVarCovector_ne_zero (Z := cVF e0) (cov := leviCivitaConnection _ _)
    _ hhYX hhXY (cVF_mdiff e0 x) (koszulVarInner_ne_zero_witness x)

/-- **`A(h) ≠ 0` for the explicit choice** — chaining `koszulVarCovector_ne_zero_witness` through
`metricConnPerturbAux_ne_zero`. On flat Euclidean space `ℝ²`, the constant field `cVF e₀` and the
nonconstant symmetric metric perturbation `hPert e₀` give a nonzero metric→connection variation
`A(h)`; the underlying Koszul-variation scalar is `1/2` (`koszulVarInner_witness`). The smoothness
data `hhYX`/`hhXY` is the intrinsic well-formedness datum of the covector construction
(dischargeable on differentiable directions by `mdiff_hPert_of_mdiff`). -/
theorem metricConnPerturbAux_ne_zero_witness {x : EuclideanSpace ℝ (Fin 2)}
    (hhYX : ∀ W : Π z : EuclideanSpace ℝ (Fin 2), TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) z,
      MDiffAt (fun z ↦ hPert e0 z (cVF e0 z) (W z)) x)
    (hhXY : ∀ W : Π z : EuclideanSpace ℝ (Fin 2), TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) z,
      MDiffAt (fun z ↦ hPert e0 z (cVF e0 z) (W z)) x) :
    metricConnPerturbAux 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      (leviCivitaConnection 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)))
      (hPert e0) (cVF e0) (cVF e0) hhYX hhXY ≠ 0 :=
  metricConnPerturbAux_ne_zero _ hhYX hhXY (koszulVarCovector_ne_zero_witness hhYX hhXY)

end MetricConnPerturbWitness

end CovariantDerivative

end
