/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib

/-!
# Fourier analysis on the 3-torus: basic setup

`T3 = UnitAddTorus (Fin 3)`, Mathlib's product of three unit circles. Mathlib's `mFourierBasis`
identifies `L²(T3)` isometrically with `ℓ²(ℤ³, ℂ)`, the `n`-th coordinate being `mFourierCoeff f n`.
-/

noncomputable section

open scoped ENNReal
open UnitAddTorus

namespace TorusFourierNS

/-- Normalised (probability) Haar measure on each circle, as in Mathlib's multi-dimensional
Fourier file. -/
local instance : MeasureTheory.MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

/-- Lattice of Fourier modes on the 3-torus. -/
abbrev Mode := Fin 3 → ℤ

/-- `L²` of the 3-torus. -/
abbrev L2T3 := MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin 3)))

/-- `|n|² = n₀² + n₁² + n₂²`. -/
def nsq (n : Mode) : ℝ := ∑ i, ((n i : ℝ)) ^ 2

lemma nsq_nonneg (n : Mode) : 0 ≤ nsq n := by unfold nsq; positivity

/-- Fourier coefficient of an `L²` function, read through Mathlib's Hilbert basis. -/
def coeff (f : L2T3) (n : Mode) : ℂ := mFourierBasis.repr f n

lemma coeff_eq_mFourierCoeff (f : L2T3) (n : Mode) : coeff f n = mFourierCoeff f n :=
  mFourierBasis_repr f n

lemma two_toReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num

/-- **Parseval** (norm form): `‖f‖² = ∑ₙ |f̂(n)|²`. -/
theorem parseval_norm_sq (f : L2T3) : ‖f‖ ^ 2 = ∑' n, ‖coeff f n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (mFourierBasis.repr f)
  rw [LinearIsometryEquiv.norm_map] at h
  simpa [two_toReal, coeff] using h

lemma summable_coeff_sq (f : L2T3) : Summable fun n => ‖coeff f n‖ ^ 2 := by
  have := (memℓp_gen_iff (p := 2) (by norm_num)).1 (mFourierBasis.repr f).2
  simpa [two_toReal, coeff] using this

/-- A bounded Fourier multiplier `|m n| ≤ 1` maps `ℓ²` to `ℓ²`. -/
lemma memℓp_mul (m : Mode → ℂ) (hm : ∀ n, ‖m n‖ ≤ 1) (a : lp (fun _ : Mode => ℂ) 2) :
    Memℓp (fun n => m n * a n) 2 := by
  have ha := (memℓp_gen_iff (p := 2) (by norm_num)).1 a.2
  refine (memℓp_gen_iff (p := 2) (by norm_num)).2 ?_
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) ha
  rw [norm_mul]
  apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
  exact mul_le_of_le_one_left (norm_nonneg _) (hm n)

set_option maxHeartbeats 1000000 in
/-- The `L²` operator with Fourier symbol `m`, `|m| ≤ 1`. -/
def multiplier (m : Mode → ℂ) (hm : ∀ n, ‖m n‖ ≤ 1) (f : L2T3) : L2T3 :=
  mFourierBasis.repr.symm ⟨fun n => m n * mFourierBasis.repr f n, memℓp_mul m hm _⟩

@[simp] lemma coeff_multiplier (m : Mode → ℂ) (hm) (f : L2T3) (n : Mode) :
    coeff (multiplier m hm f) n = m n * coeff f n := by
  simp [coeff, multiplier]

set_option maxHeartbeats 1000000 in
lemma ext_coeff {f g : L2T3} (h : ∀ n, coeff f n = coeff g n) : f = g := by
  apply mFourierBasis.repr.injective
  ext n; exact h n

/-- Bounded multipliers are `L²` contractions. -/
theorem norm_multiplier_le (m : Mode → ℂ) (hm) (f : L2T3) : ‖multiplier m hm f‖ ≤ ‖f‖ := by
  have h1 := parseval_norm_sq (multiplier m hm f)
  have h2 := parseval_norm_sq f
  have hle : ‖multiplier m hm f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [h1, h2]
    have hs : Summable fun n => ‖coeff (multiplier m hm f) n‖ ^ 2 := summable_coeff_sq _
    refine hs.tsum_le_tsum (fun n => ?_) (summable_coeff_sq f)
    rw [coeff_multiplier, norm_mul]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_of_le_one_left (norm_nonneg _) (hm n)
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num) |>.1 hle

end TorusFourierNS
