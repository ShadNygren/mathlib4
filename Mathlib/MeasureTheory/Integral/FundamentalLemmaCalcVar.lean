/-
Copyright (c) 2026 Shad Nygren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shad Nygren
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # The fundamental lemma of the calculus of variations over metric balls

This file proves a ball-weighted form of the fundamental lemma of the calculus of variations:
a continuous function whose *ball-weighted integral* against the quadratic weight
`w(x) = ℓ² − dist(x, p)²` vanishes over every ball of every radius must vanish pointwise. The
weight `w` is strictly positive on the open ball `Metric.ball p ℓ` and vanishes on the boundary
sphere, so it plays the role of the smooth compactly-supported bump functions in the classical
statement while remaining fully explicit.

## Main results

Three progressively more general settings are treated.

* **Real interval.** `fundamental_lemma_ball_weight`: for continuous `H : ℝ → ℝ`, if the weighted
  integral `∫_{p-ℓ}^{p+ℓ} (ℓ² − (x − p)²) · H x` vanishes for every `ℓ > 0`, then `H p = 0`.
  Proved by a shrinking-window mass estimate (`weight_mass`: the window mass is `4ℓ³/3`).
* **Finite-dimensional inner-product space.** `fundamental_lemma_ball_dDim`: for continuous
  `H : EuclideanSpace ℝ (Fin d) → ℝ`, if the weighted integral over `Metric.ball p ℓ` against
  `ℓ² − ‖v − p‖²` vanishes for every `ℓ > 0`, then `H p = 0`. Proved by a positivity argument
  against the Haar `volume`.
* **Proper metric measure space.** `fundamental_lemma_ball_metric`: for a proper metric space `X`
  with a measure positive on nonempty opens and finite on compacts, and continuous `H : X → ℝ`, if
  the weighted integral over `Metric.ball p ℓ` against `ℓ² − dist(x, p)²` vanishes for every
  `ℓ > 0`, then `H p = 0`. The Euclidean case is the special case with Lebesgue `volume`.

## Implementation notes

The finite-dimensional and general metric proofs share the same positivity argument: continuity of
`H` at `p` with `H p > 0` yields a `δ`-ball on which `H > H p / 2 > 0`, so the weighted integrand is
strictly positive there; positivity of the ball's measure then makes the set-integral strictly
positive, contradicting the vanishing hypothesis at radius `δ`. The sign-`< 0` case follows by
applying the positive core to `−H`.
-/

@[expose] public noncomputable section

open intervalIntegral MeasureTheory Set

namespace FundamentalLemmaCalcVar

/-! ### The real interval -/

/-- The quadratic ball weight on the interval of half-width `ℓ` centered at `p`: the parabola
`ℓ² − (x − p)²`, strictly positive inside `(p − ℓ, p + ℓ)` and vanishing at the two endpoints
`p ± ℓ`. -/
def ballWeight (p ℓ x : ℝ) : ℝ := ℓ ^ 2 - (x - p) ^ 2

/-- The ball-weighted integral of a density `f` over the interval of half-width `ℓ` centered at `p`:
`∫_{p-ℓ}^{p+ℓ} (ℓ² − (x − p)²) · f x`. -/
noncomputable def ballWeightedIntegral (f : ℝ → ℝ) (p ℓ : ℝ) : ℝ :=
  ∫ x in (p - ℓ)..(p + ℓ), ballWeight p ℓ x * f x

/-- **Window mass.** `∫_{p-ℓ}^{p+ℓ} (ℓ² − (x−p)²) dx = 4ℓ³/3`. For `ℓ > 0` this is strictly
positive, which makes the normalized shrinking-window average a genuine average. Proved by the
fundamental theorem of calculus with the antiderivative `ℓ²x − (x−p)³/3`. -/
theorem weight_mass (p ℓ : ℝ) :
    ∫ x in (p - ℓ)..(p + ℓ), ballWeight p ℓ x = 4 * ℓ ^ 3 / 3 := by
  unfold ballWeight
  have key : ∫ x in (p - ℓ)..(p + ℓ), (ℓ ^ 2 - (x - p) ^ 2)
      = (ℓ ^ 2 * (p + ℓ) - ((p + ℓ) - p) ^ 3 / 3)
        - (ℓ ^ 2 * (p - ℓ) - ((p - ℓ) - p) ^ 3 / 3) := by
    apply integral_eq_sub_of_hasDerivAt (f := fun x => ℓ ^ 2 * x - (x - p) ^ 3 / 3)
    · intro x _
      have h1 : HasDerivAt (fun x : ℝ => ℓ ^ 2 * x) (ℓ ^ 2) x := by
        simpa using (hasDerivAt_id x).const_mul (ℓ ^ 2)
      have h2 : HasDerivAt (fun x : ℝ => (x - p) ^ 3 / 3) ((x - p) ^ 2) x := by
        have h := ((hasDerivAt_id x).sub_const p).pow 3
        simp only [id_eq, Nat.cast_ofNat] at h
        have h' := h.div_const 3
        have e : (3 : ℝ) * (x - p) ^ (3 - 1) * 1 / 3 = (x - p) ^ 2 := by norm_num
        rw [e] at h'
        exact h'
      exact h1.sub h2
    · exact (by fun_prop : Continuous fun x : ℝ => (ℓ ^ 2 - (x - p) ^ 2)).intervalIntegrable _ _
  rw [key]; ring

/-- **Fundamental lemma of the calculus of variations over intervals.** If `H` is continuous and its
ball-weighted integral over *every* centered window vanishes, then `H p = 0` for every `p`.

Proof: fix `p`, suppose `H p ≠ 0`, so `c := |H p| > 0`. By continuity choose `δ` with
`|H x − H p| < c/2` for `|x − p| < δ`, take `ℓ = δ/2`. Split the (zero) window integral as
`∫ w·(H − H p) + H p · ∫ w`; the second term is `H p · 4ℓ³/3` by `weight_mass`. On the window
`|w| ≤ ℓ²` and `|H − H p| ≤ c/2`, so the first term is bounded by `(ℓ²·c/2)·(2ℓ) = c·ℓ³`. Hence
`c · 4ℓ³/3 ≤ c·ℓ³`, i.e. `4/3 ≤ 1` — a contradiction. So `H p = 0`. -/
theorem fundamental_lemma_ball_weight (H : ℝ → ℝ) (hH : Continuous H) (p : ℝ)
    (hzero : ∀ ℓ, 0 < ℓ → ballWeightedIntegral H p ℓ = 0) :
    H p = 0 := by
  unfold ballWeightedIntegral ballWeight at hzero
  by_contra hne
  set c := |H p| with hc
  have hcpos : 0 < c := abs_pos.mpr hne
  have hCA : ContinuousAt H p := hH.continuousAt
  rw [Metric.continuousAt_iff] at hCA
  obtain ⟨δ, hδ, hδp⟩ := hCA (c / 2) (by linarith)
  set ℓ := δ / 2 with hℓdef
  have hℓ : 0 < ℓ := by positivity
  have hle : p - ℓ ≤ p + ℓ := by linarith
  have hwbound : ∀ x ∈ Set.uIoc (p - ℓ) (p + ℓ),
      |ℓ ^ 2 - (x - p) ^ 2| * |H x - H p| ≤ ℓ ^ 2 * (c / 2) := by
    intro x hx
    rw [Set.uIoc_of_le hle] at hx
    have hsq : (x - p) ^ 2 ≤ ℓ ^ 2 := by nlinarith [hx.1, hx.2]
    have hw : |ℓ ^ 2 - (x - p) ^ 2| ≤ ℓ ^ 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x - p)]
    have hdist : dist x p < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> [linarith [hx.1]; linarith [hx.2]]
    have hM' : |H x - H p| ≤ c / 2 := by
      have := hδp hdist; rw [Real.dist_eq] at this; exact le_of_lt this
    exact mul_le_mul hw hM' (abs_nonneg _) (by positivity)
  have hint_split : (∫ x in (p - ℓ)..(p + ℓ), (ℓ ^ 2 - (x - p) ^ 2) * H x)
      = (∫ x in (p - ℓ)..(p + ℓ), (ℓ ^ 2 - (x - p) ^ 2) * (H x - H p))
        + H p * (∫ x in (p - ℓ)..(p + ℓ), (ℓ ^ 2 - (x - p) ^ 2)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add]
    · congr 1; funext x; ring
    · exact ((by fun_prop :
        Continuous fun x : ℝ => (ℓ ^ 2 - (x - p) ^ 2) * (H x - H p))).intervalIntegrable _ _
    · exact ((by fun_prop :
        Continuous fun x : ℝ => H p * (ℓ ^ 2 - (x - p) ^ 2))).intervalIntegrable _ _
  have hzero_ℓ := hzero ℓ hℓ
  have hwm : (∫ x in (p - ℓ)..(p + ℓ), (ℓ ^ 2 - (x - p) ^ 2)) = 4 * ℓ ^ 3 / 3 := by
    have := weight_mass p ℓ; unfold ballWeight at this; exact this
  rw [hint_split, hwm] at hzero_ℓ
  have heq : (∫ x in (p - ℓ)..(p + ℓ), (ℓ ^ 2 - (x - p) ^ 2) * (H x - H p))
      = -(H p * (4 * ℓ ^ 3 / 3)) := by linarith
  have hbnd : |∫ x in (p - ℓ)..(p + ℓ), (ℓ ^ 2 - (x - p) ^ 2) * (H x - H p)|
      ≤ (ℓ ^ 2 * (c / 2)) * (2 * ℓ) := by
    have hbb := intervalIntegral.norm_integral_le_of_norm_le_const (a := p - ℓ) (b := p + ℓ)
      (C := ℓ ^ 2 * (c / 2)) (f := fun x => (ℓ ^ 2 - (x - p) ^ 2) * (H x - H p)) ?_
    · simp only [Real.norm_eq_abs] at hbb
      have habs : |p + ℓ - (p - ℓ)| = 2 * ℓ := by rw [abs_of_nonneg (by linarith)]; ring
      rw [habs] at hbb; exact hbb
    · intro x hx
      simp only [Real.norm_eq_abs, abs_mul]
      exact hwbound x hx
  rw [heq] at hbnd
  have hlhs : |(-(H p * (4 * ℓ ^ 3 / 3)))| = c * (4 * ℓ ^ 3 / 3) := by
    rw [abs_neg, abs_mul, ← hc]; congr 1; rw [abs_of_pos (by positivity)]
  rw [hlhs] at hbnd
  nlinarith [hbnd, hcpos, pow_pos hℓ 3]

/-- **Linearity split.** For continuous `A B`,
`ballWeightedIntegral (A − k·B) p ℓ = ballWeightedIntegral A p ℓ − k · ballWeightedIntegral B p ℓ`.
-/
theorem ballWeightedIntegral_sub_smul (A B : ℝ → ℝ) (hA : Continuous A) (hB : Continuous B)
    (k : ℝ) (p ℓ : ℝ) :
    ballWeightedIntegral (fun y => A y - k * B y) p ℓ
      = ballWeightedIntegral A p ℓ - k * ballWeightedIntegral B p ℓ := by
  unfold ballWeightedIntegral ballWeight
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub]
  · congr 1; funext y; ring
  · exact ((by fun_prop :
      Continuous fun y : ℝ => (ℓ ^ 2 - (y - p) ^ 2) * A y)).intervalIntegrable _ _
  · exact ((by fun_prop :
      Continuous fun y : ℝ => k * ((ℓ ^ 2 - (y - p) ^ 2) * B y))).intervalIntegrable _ _

/-- **The window mass is genuinely nonzero.** The ball-weighted integral of the constant density
`1` over the unit interval `[−1, 1]` is `4/3 > 0`: the window has strictly positive mass, so the
vanishing hypothesis of `fundamental_lemma_ball_weight` is a genuine constraint (not the vacuous
`0 = 0`). -/
theorem ballWeightedIntegral_one_zero_one : ballWeightedIntegral (fun _ => 1) 0 1 = 4 / 3 := by
  unfold ballWeightedIntegral ballWeight
  have : (fun x : ℝ => ((1 : ℝ) ^ 2 - (x - 0) ^ 2) * (1 : ℝ))
      = fun x : ℝ => ((1 : ℝ) ^ 2 - (x - 0) ^ 2) := by funext x; ring
  rw [this]
  have := weight_mass 0 1
  unfold ballWeight at this
  rw [this]; norm_num

/-! ### The finite-dimensional Euclidean ball -/

/-- The quadratic ball weight `w(v) = ℓ² − ‖v − p‖²` on a finite-dimensional inner-product space.
Strictly positive on the open ball `Metric.ball p ℓ` (where `dist v p < ℓ`) and vanishing on the
boundary sphere `‖v − p‖ = ℓ`; the multi-dimensional analogue of `ballWeight`. -/
noncomputable def ballWeightD {d : ℕ} (p : EuclideanSpace ℝ (Fin d)) (ℓ : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ℓ ^ 2 - ‖v - p‖ ^ 2

/-- **The weight is strictly positive on the open ball.** For `v ∈ Metric.ball p ℓ` (so
`dist v p = ‖v − p‖ < ℓ`), `0 < ℓ² − ‖v − p‖²`. This positivity — together with the open ball's
positive Haar volume — is the engine of the finite-dimensional fundamental lemma. -/
theorem ballWeightD_pos {d : ℕ} (p : EuclideanSpace ℝ (Fin d)) (ℓ : ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ Metric.ball p ℓ) : 0 < ballWeightD p ℓ v := by
  rw [Metric.mem_ball] at hv
  have hd : dist v p = ‖v - p‖ := dist_eq_norm v p
  rw [hd] at hv
  have : 0 ≤ ‖v - p‖ := norm_nonneg _
  unfold ballWeightD
  nlinarith [hv]

/-- **The ball-weighted integral** of a density `f` over `Metric.ball p ℓ`:
`∫_{B(p,ℓ)} (ℓ² − ‖v − p‖²) · f v dv`, the multi-dimensional analogue of `ballWeightedIntegral`. -/
noncomputable def ballWeightedIntegralD {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (p : EuclideanSpace ℝ (Fin d)) (ℓ : ℝ) : ℝ :=
  ∫ v in Metric.ball p ℓ, ballWeightD p ℓ v * f v

/-- **Integrability of a continuous weighted density on the ball.** For continuous `f`, the
integrand `w · f` is continuous, hence locally integrable, hence integrable on the compact
`closedBall`, hence (by monotonicity) on the open `ball`. -/
theorem integrableOn_ballWeightD_mul {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (hf : Continuous f) (p : EuclideanSpace ℝ (Fin d)) (ℓ : ℝ) :
    IntegrableOn (fun v => ballWeightD p ℓ v * f v) (Metric.ball p ℓ) volume := by
  have hcont : Continuous fun v : EuclideanSpace ℝ (Fin d) => ballWeightD p ℓ v * f v := by
    unfold ballWeightD; fun_prop
  exact (hcont.locallyIntegrable.integrableOn_isCompact
    (isCompact_closedBall p ℓ)).mono_set Metric.ball_subset_closedBall

/-- **Positive-case core.** If `H` is continuous with `H p > 0` and its ball-weighted integral
vanishes for every radius, we derive a contradiction: continuity yields a `δ`-ball on which
`H > H p / 2 > 0`; there the integrand `w · H` is strictly positive on a positive-Haar-volume open
ball, so its set-integral is `> 0` — contradicting the vanishing at `ℓ = δ`. -/
theorem fundamental_lemma_ball_dDim_core {d : ℕ} (p : EuclideanSpace ℝ (Fin d))
    (H : EuclideanSpace ℝ (Fin d) → ℝ) (hH : Continuous H) (hpos : 0 < H p)
    (hker : ∀ ℓ : ℝ, 0 < ℓ → ballWeightedIntegralD H p ℓ = 0) : False := by
  -- local sign: ∃ δ > 0, ∀ v ∈ ball p δ, H p / 2 < H v
  have hsign : ∃ δ > 0, ∀ v ∈ Metric.ball p δ, H p / 2 < H v := by
    have hev : ∀ᶠ v in nhds p, H p / 2 < H v :=
      (hH.continuousAt (x := p)).eventually
        (IsOpen.mem_nhds (isOpen_lt continuous_const continuous_id) (by simp; linarith))
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, h⟩ := hev
    exact ⟨δ, hδ, fun v hv => h (by rwa [Metric.mem_ball] at hv)⟩
  obtain ⟨δ, hδ, hδlt⟩ := hsign
  set ℓ := δ with hℓdef
  have hℓ : 0 < ℓ := hδ
  set g : EuclideanSpace ℝ (Fin d) → ℝ := fun v => ballWeightD p ℓ v * H v with hgdef
  have hint : IntegrableOn g (Metric.ball p ℓ) volume :=
    integrableOn_ballWeightD_mul H hH p ℓ
  have hgpos : ∀ v ∈ Metric.ball p ℓ, 0 < g v := by
    intro v hv
    have hHv : 0 < H v := by have := hδlt v hv; linarith
    exact mul_pos (ballWeightD_pos p ℓ v hv) hHv
  have hnonneg : 0 ≤ᵐ[volume.restrict (Metric.ball p ℓ)] g :=
    (ae_restrict_iff' measurableSet_ball).mpr (ae_of_all _ fun v hv => le_of_lt (hgpos v hv))
  have hballpos : 0 < volume (Metric.ball p ℓ) := Metric.measure_ball_pos _ p hℓ
  have hpos_int : 0 < ∫ v in Metric.ball p ℓ, g v := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint]
    have hsub : Metric.ball p ℓ ⊆ Function.support g ∩ Metric.ball p ℓ :=
      fun v hv => ⟨ne_of_gt (hgpos v hv), hv⟩
    exact lt_of_lt_of_le hballpos (measure_mono hsub)
  have hz : ballWeightedIntegralD H p ℓ = 0 := hker ℓ hℓ
  rw [ballWeightedIntegralD, ← hgdef] at hz
  rw [hz] at hpos_int
  exact lt_irrefl 0 hpos_int

/-- **Fundamental lemma of the calculus of variations over Euclidean balls.**

If `H : EuclideanSpace ℝ (Fin d) → ℝ` is continuous and its ball-weighted integral
`∫_{B(p,ℓ)} (ℓ² − ‖v − p‖²) · H v dv` vanishes for **every** radius `ℓ > 0` at the center `p`,
then `H p = 0`.

Proof by the positivity argument (`fundamental_lemma_ball_dDim_core`), applied to `H` if
`H p > 0` and to `−H` if `H p < 0` (the ball-weighted integral is odd in `H`). This is the
multi-dimensional, all-radii analogue of `fundamental_lemma_ball_weight`. -/
theorem fundamental_lemma_ball_dDim {d : ℕ} (p : EuclideanSpace ℝ (Fin d))
    (H : EuclideanSpace ℝ (Fin d) → ℝ) (hH : Continuous H)
    (hker : ∀ ℓ : ℝ, 0 < ℓ → ballWeightedIntegralD H p ℓ = 0) :
    H p = 0 := by
  rcases lt_trichotomy (H p) 0 with hlt | h0 | hgt
  · exfalso
    have hker' : ∀ ℓ : ℝ, 0 < ℓ → ballWeightedIntegralD (fun v => -H v) p ℓ = 0 := by
      intro ℓ hℓ
      have hcongr : (fun v => ballWeightD p ℓ v * (-H v))
          = (fun v => -(ballWeightD p ℓ v * H v)) := by funext v; ring
      rw [ballWeightedIntegralD, hcongr, MeasureTheory.integral_neg]
      rw [show (∫ v in Metric.ball p ℓ, ballWeightD p ℓ v * H v) = ballWeightedIntegralD H p ℓ from
        rfl, hker ℓ hℓ, neg_zero]
    exact fundamental_lemma_ball_dDim_core p (fun v => -H v) hH.neg (by simpa using hlt) hker'
  · exact h0
  · exact absurd (fundamental_lemma_ball_dDim_core p H hH hgt hker) (fun h => h.elim)

/-- **Linearity split.** For continuous `A B`,
`ballWeightedIntegralD (A − k·B) p ℓ = ballWeightedIntegralD A p ℓ − k · ballWeightedIntegralD B p ℓ`.
-/
theorem ballWeightedIntegralD_sub_smul {d : ℕ} (A B : EuclideanSpace ℝ (Fin d) → ℝ)
    (hA : Continuous A) (hB : Continuous B) (k : ℝ) (p : EuclideanSpace ℝ (Fin d)) (ℓ : ℝ) :
    ballWeightedIntegralD (fun v => A v - k * B v) p ℓ
      = ballWeightedIntegralD A p ℓ - k * ballWeightedIntegralD B p ℓ := by
  unfold ballWeightedIntegralD
  have hwA := integrableOn_ballWeightD_mul A hA p ℓ
  have hwB := integrableOn_ballWeightD_mul B hB p ℓ
  rw [show (fun v => ballWeightD p ℓ v * (A v - k * B v))
      = (fun v => ballWeightD p ℓ v * A v - k * (ballWeightD p ℓ v * B v)) from by funext v; ring]
  rw [MeasureTheory.integral_sub hwA (hwB.const_mul k), MeasureTheory.integral_const_mul]

/-- **The weighted volume is genuinely nonzero.** The ball-weighted integral of the constant
density `1` over a ball of positive radius is **strictly positive**:
`0 < ∫_{B(p,ℓ)} (ℓ² − ‖v − p‖²) dv`. This certifies the fundamental lemma is not vacuously about
the zero integrand — the vanishing hypothesis is a genuine constraint. -/
theorem ballWeightedIntegralD_one_pos {d : ℕ} (p : EuclideanSpace ℝ (Fin d)) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    0 < ballWeightedIntegralD (fun _ => 1) p ℓ := by
  unfold ballWeightedIntegralD
  have hint : IntegrableOn (fun v => ballWeightD p ℓ v * (1 : ℝ)) (Metric.ball p ℓ) volume :=
    integrableOn_ballWeightD_mul (fun _ => 1) continuous_const p ℓ
  have hgpos : ∀ v ∈ Metric.ball p ℓ, 0 < ballWeightD p ℓ v * (1 : ℝ) := by
    intro v hv; simpa using ballWeightD_pos p ℓ v hv
  have hnonneg : 0 ≤ᵐ[volume.restrict (Metric.ball p ℓ)] fun v => ballWeightD p ℓ v * (1 : ℝ) :=
    (ae_restrict_iff' measurableSet_ball).mpr (ae_of_all _ fun v hv => le_of_lt (hgpos v hv))
  have hballpos : 0 < volume (Metric.ball p ℓ) := Metric.measure_ball_pos _ p hℓ
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint]
  have hsub : Metric.ball p ℓ ⊆ Function.support (fun v => ballWeightD p ℓ v * (1 : ℝ))
      ∩ Metric.ball p ℓ := fun v hv => ⟨ne_of_gt (hgpos v hv), hv⟩
  exact lt_of_lt_of_le hballpos (measure_mono hsub)

/-! ### The general proper metric measure space

The positivity argument uses only three properties of the space-and-measure `(X, μ)`: the ball
`Metric.ball p ℓ` has positive measure (`IsOpenPosMeasure μ`); a continuous integrand is integrable
on the ball (`IsFiniteMeasureOnCompacts μ` with `ProperSpace X`); and closed balls are compact
(`ProperSpace X`). So the entire argument generalizes to any proper metric measure space whose
measure is positive on nonempty opens and finite on compacts. The Euclidean case above is the
special case with Lebesgue `volume`.
-/

section MetricMeasure

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) [Measure.IsOpenPosMeasure μ] [IsFiniteMeasureOnCompacts μ]

/-- The quadratic **metric ball weight** `w(x) = ℓ² − dist x p ²`. Strictly positive on the open
ball `Metric.ball p ℓ` (where `dist x p < ℓ`) and vanishing on the boundary sphere `dist x p = ℓ`;
the general-metric analogue of `ballWeightD`. -/
noncomputable def ballWeightM (p : X) (ℓ : ℝ) (x : X) : ℝ := ℓ ^ 2 - dist x p ^ 2

omit [MeasurableSpace X] [BorelSpace X] [ProperSpace X] in
/-- **The weight is strictly positive on the open ball.** For `x ∈ Metric.ball p ℓ` (so
`dist x p < ℓ`), `0 < ℓ² − dist x p ²`. This positivity — together with the ball's positive
measure — is the engine of the general fundamental lemma. -/
theorem ballWeightM_pos (p : X) (ℓ : ℝ) (x : X) (hx : x ∈ Metric.ball p ℓ) :
    0 < ballWeightM p ℓ x := by
  rw [Metric.mem_ball] at hx
  have hnn : 0 ≤ dist x p := dist_nonneg
  unfold ballWeightM
  nlinarith [hx]

/-- **The metric ball-weighted integral** of a density `f`:
`∫_{B(p,ℓ)} (ℓ² − dist x p ²) · f x dμ`, the general metric-measure analogue of
`ballWeightedIntegralD`. -/
noncomputable def ballWeightedIntegralM (f : X → ℝ) (p : X) (ℓ : ℝ) : ℝ :=
  ∫ x in Metric.ball p ℓ, ballWeightM p ℓ x * f x ∂μ

omit [Measure.IsOpenPosMeasure μ] in
/-- **Integrability of a continuous weighted density on the ball.** For continuous `f`, the
integrand `w · f` is continuous, hence locally integrable (locally finite measure, from
`IsFiniteMeasureOnCompacts` + `ProperSpace`), hence integrable on the compact `closedBall`
(`ProperSpace`), hence (by monotonicity) on the open `ball`. -/
theorem integrableOn_ballWeightM_mul (f : X → ℝ) (hf : Continuous f) (p : X) (ℓ : ℝ) :
    IntegrableOn (fun x => ballWeightM p ℓ x * f x) (Metric.ball p ℓ) μ := by
  have hcont : Continuous fun x : X => ballWeightM p ℓ x * f x := by
    unfold ballWeightM; fun_prop
  exact (hcont.locallyIntegrable.integrableOn_isCompact
    (isCompact_closedBall p ℓ)).mono_set Metric.ball_subset_closedBall

/-- **Positive-case core.** If `H` is continuous with `H p > 0` and its metric ball-weighted
integral vanishes for every radius, we derive a contradiction: continuity yields a `δ`-ball on
which `H > H p / 2 > 0`; there the integrand `w · H` is strictly positive on a positive-measure
open ball, so its set-integral is `> 0` — contradicting the vanishing at `ℓ = δ`. This is
`fundamental_lemma_ball_dDim_core` generalized from Euclidean Lebesgue volume to any
positive-on-opens, finite-on-compacts measure on a proper metric space. -/
theorem fundamental_lemma_ball_metric_core (p : X)
    (H : X → ℝ) (hH : Continuous H) (hpos : 0 < H p)
    (hker : ∀ ℓ : ℝ, 0 < ℓ → ballWeightedIntegralM μ H p ℓ = 0) : False := by
  -- local sign: ∃ δ > 0, ∀ x ∈ ball p δ, H p / 2 < H x
  have hsign : ∃ δ > 0, ∀ x ∈ Metric.ball p δ, H p / 2 < H x := by
    have hev : ∀ᶠ x in nhds p, H p / 2 < H x :=
      (hH.continuousAt (x := p)).eventually
        (IsOpen.mem_nhds (isOpen_lt continuous_const continuous_id) (by simp; linarith))
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, h⟩ := hev
    exact ⟨δ, hδ, fun x hx => h (by rwa [Metric.mem_ball] at hx)⟩
  obtain ⟨δ, hδ, hδlt⟩ := hsign
  set ℓ := δ with hℓdef
  have hℓ : 0 < ℓ := hδ
  set g : X → ℝ := fun x => ballWeightM p ℓ x * H x with hgdef
  have hint : IntegrableOn g (Metric.ball p ℓ) μ :=
    integrableOn_ballWeightM_mul μ H hH p ℓ
  have hgpos : ∀ x ∈ Metric.ball p ℓ, 0 < g x := by
    intro x hx
    have hHx : 0 < H x := by have := hδlt x hx; linarith
    exact mul_pos (ballWeightM_pos p ℓ x hx) hHx
  have hnonneg : 0 ≤ᵐ[μ.restrict (Metric.ball p ℓ)] g :=
    (ae_restrict_iff' measurableSet_ball).mpr (ae_of_all _ fun x hx => le_of_lt (hgpos x hx))
  have hballpos : 0 < μ (Metric.ball p ℓ) := Metric.measure_ball_pos _ p hℓ
  have hpos_int : 0 < ∫ x in Metric.ball p ℓ, g x ∂μ := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint]
    have hsub : Metric.ball p ℓ ⊆ Function.support g ∩ Metric.ball p ℓ :=
      fun x hx => ⟨ne_of_gt (hgpos x hx), hx⟩
    exact lt_of_lt_of_le hballpos (measure_mono hsub)
  have hz : ballWeightedIntegralM μ H p ℓ = 0 := hker ℓ hℓ
  rw [ballWeightedIntegralM, ← hgdef] at hz
  rw [hz] at hpos_int
  exact lt_irrefl 0 hpos_int

/-- **Fundamental lemma of the calculus of variations over metric balls.**

Let `(X, μ)` be a proper metric measure space whose measure is positive on nonempty opens and
finite on compacts. If `H : X → ℝ` is continuous and its metric ball-weighted integral
`∫_{B(p,ℓ)} (ℓ² − dist x p ²) · H x dμ` vanishes for **every** radius `ℓ > 0` at the center `p`,
then `H p = 0`.

Proof by the positivity argument (`fundamental_lemma_ball_metric_core`), applied to `H` if
`H p > 0` and to `−H` if `H p < 0` (the metric ball-weighted integral is odd in `H`). This is
`fundamental_lemma_ball_dDim` lifted from the Euclidean ball (Lebesgue volume) to any proper metric
measure space. -/
theorem fundamental_lemma_ball_metric (p : X)
    (H : X → ℝ) (hH : Continuous H)
    (hker : ∀ ℓ : ℝ, 0 < ℓ → ballWeightedIntegralM μ H p ℓ = 0) :
    H p = 0 := by
  rcases lt_trichotomy (H p) 0 with hlt | h0 | hgt
  · exfalso
    have hker' : ∀ ℓ : ℝ, 0 < ℓ → ballWeightedIntegralM μ (fun x => -H x) p ℓ = 0 := by
      intro ℓ hℓ
      have hcongr : (fun x => ballWeightM p ℓ x * (-H x))
          = (fun x => -(ballWeightM p ℓ x * H x)) := by funext x; ring
      rw [ballWeightedIntegralM, hcongr, MeasureTheory.integral_neg]
      rw [show (∫ x in Metric.ball p ℓ, ballWeightM p ℓ x * H x ∂μ)
          = ballWeightedIntegralM μ H p ℓ from rfl, hker ℓ hℓ, neg_zero]
    exact fundamental_lemma_ball_metric_core μ p (fun x => -H x) hH.neg
      (by simpa using hlt) hker'
  · exact h0
  · exact absurd (fundamental_lemma_ball_metric_core μ p H hH hgt hker) (fun h => h.elim)

omit [Measure.IsOpenPosMeasure μ] in
/-- **Linearity split.** For continuous `A B`,
`ballWeightedIntegralM (A − k·B) p ℓ = ballWeightedIntegralM A p ℓ − k · ballWeightedIntegralM B p ℓ`.
-/
theorem ballWeightedIntegralM_sub_smul (A B : X → ℝ)
    (hA : Continuous A) (hB : Continuous B) (k : ℝ) (p : X) (ℓ : ℝ) :
    ballWeightedIntegralM μ (fun x => A x - k * B x) p ℓ
      = ballWeightedIntegralM μ A p ℓ - k * ballWeightedIntegralM μ B p ℓ := by
  unfold ballWeightedIntegralM
  have hwA := integrableOn_ballWeightM_mul μ A hA p ℓ
  have hwB := integrableOn_ballWeightM_mul μ B hB p ℓ
  rw [show (fun x => ballWeightM p ℓ x * (A x - k * B x))
      = (fun x => ballWeightM p ℓ x * A x - k * (ballWeightM p ℓ x * B x)) from by
        funext x; ring]
  rw [MeasureTheory.integral_sub hwA (hwB.const_mul k), MeasureTheory.integral_const_mul]

/-- **The weighted measure is genuinely nonzero.** The metric ball-weighted integral of the
constant density `1` over a ball of positive radius is **strictly positive**:
`0 < ∫_{B(p,ℓ)} (ℓ² − dist x p ²) dμ`. This certifies the fundamental lemma is not vacuously about
the zero integrand — the vanishing hypothesis is a genuine constraint. -/
theorem ballWeightedIntegralM_one_pos (p : X) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    0 < ballWeightedIntegralM μ (fun _ => 1) p ℓ := by
  unfold ballWeightedIntegralM
  have hint : IntegrableOn (fun x => ballWeightM p ℓ x * (1 : ℝ)) (Metric.ball p ℓ) μ :=
    integrableOn_ballWeightM_mul μ (fun _ => 1) continuous_const p ℓ
  have hgpos : ∀ x ∈ Metric.ball p ℓ, 0 < ballWeightM p ℓ x * (1 : ℝ) := by
    intro x hx; simpa using ballWeightM_pos p ℓ x hx
  have hnonneg : 0 ≤ᵐ[μ.restrict (Metric.ball p ℓ)] fun x => ballWeightM p ℓ x * (1 : ℝ) :=
    (ae_restrict_iff' measurableSet_ball).mpr (ae_of_all _ fun x hx => le_of_lt (hgpos x hx))
  have hballpos : 0 < μ (Metric.ball p ℓ) := Metric.measure_ball_pos _ p hℓ
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint]
  have hsub : Metric.ball p ℓ ⊆ Function.support (fun x => ballWeightM p ℓ x * (1 : ℝ))
      ∩ Metric.ball p ℓ := fun x hx => ⟨ne_of_gt (hgpos x hx), hx⟩
  exact lt_of_lt_of_le hballpos (measure_mono hsub)

end MetricMeasure

end FundamentalLemmaCalcVar
