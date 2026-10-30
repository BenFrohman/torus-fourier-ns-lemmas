/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import TorusFourierNS.GalerkinNS
import TorusFourierNS.FconvSummable

/-!
# Uniform-in-`N` time for the Galerkin system from an `H^s` energy inequality

Coined names: `restrictG`, `HermitianField`, `GalerkinHsEnergyInequality`, `ode_barrier`,
`barrierTime`, `galerkin_uniform_bound_of_energy`.

**Proved:**
* `ode_barrier`: if `y' ≤ C y^{3/2}` on `[0,T]` and `y 0 ≤ Y`, then `y ≤ Y + 1` on `[0,T]` as soon as
  `T ≤ barrierTime C Y` (a time depending only on `C, Y`).
* `hsNormField_extendG_restrictG_le`: truncation does not increase the `H^s` norm.
* `galerkin_uniform_bound_of_energy`: **conditional on** `GalerkinHsEnergyInequality ν s C`, every
  Galerkin solution started from the truncation of `a ∈ H^s` that stays Hermitian and
  divergence-free satisfies `‖u_N(t)‖²_{H^s} ≤ ‖a‖²_{H^s} + 1` on `[0, barrierTime C ‖a‖²]`,
  uniformly in `N`.

**NOT proved:** `GalerkinHsEnergyInequality` itself. It needs the cancellation of the leading
transport term `Re⟨Λ^s u, Λ^s P(u·∇u)⟩ = Re⟨Λ^s u, [Λ^s, u·∇]u⟩` (uses Hermitian symmetry and
`DivergenceFree`) and a Kato–Ponce commutator bound, plus the `ℓ¹`-summability of `|k| |û_k|`
for `s > 5/2`. The Hermitian hypothesis is necessary: for complex non-Hermitian fields the
real part of the transport pairing need not cancel.
-/

noncomputable section
open Set
namespace TorusFourierNS

/-- Truncation of a Fourier field to the mode box. -/
def restrictG (N : ℕ) (a : FField) : GState N := fun k => a k.1

/-- Fourier coefficients of a real field: `û(-k) = conj û(k)`. -/
def HermitianField (u : FField) : Prop := ∀ k i, u (-k) i = (starRingEnd ℂ) (u k i)

/-- Explicit uniform time of the barrier argument. -/
def barrierTime (C Y : ℝ) : ℝ := 1 / (2 * (C * (Y + 1) ^ (3/2 : ℝ) + 1))

/-- **Proved.** ODE comparison with a linear barrier. -/
theorem ode_barrier {y : ℝ → ℝ} {T C Y : ℝ} (hC : 0 ≤ C) (hY : 0 ≤ Y) (hy0 : y 0 ≤ Y)
    (hT : T ≤ barrierTime C Y)
    (hd : ∀ t ∈ Icc 0 T, ∃ d, HasDerivAt y d t ∧ d ≤ C * (y t) ^ (3/2 : ℝ)) :
    ∀ t ∈ Icc 0 T, y t ≤ Y + 1 := by
  classical
  set L := C * (Y + 1) ^ (3/2 : ℝ) + 1 with hL
  have hL0 : 0 < L := by have : 0 ≤ C * (Y + 1) ^ (3/2 : ℝ) := by positivity
                         linarith
  let f' : ℝ → ℝ := fun t => if h : ∃ d, HasDerivAt y d t ∧ d ≤ C * (y t) ^ (3/2 : ℝ)
    then h.choose else 0
  have hf'spec : ∀ t ∈ Icc 0 T, HasDerivAt y (f' t) t ∧ f' t ≤ C * (y t) ^ (3/2 : ℝ) := by
    intro t ht; have h := hd t ht; simp only [f', dif_pos h]; exact h.choose_spec
  have hB : ∀ t ∈ Icc 0 T, y t ≤ Y + 1/2 + L * t := by
    refine image_le_of_deriv_right_lt_deriv_boundary' (f := y) (f' := f')
      (B := fun t => Y + 1/2 + L * t) (B' := fun _ => L) ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun t ht => (hf'spec t ht).1.continuousAt.continuousWithinAt
    · exact fun t ht => (hf'spec t (Ico_subset_Icc_self ht)).1.hasDerivWithinAt
    · simp; linarith
    · exact (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
    · intro t _
      have := ((hasDerivAt_id t).const_mul L).const_add (Y + 1/2)
      simpa using this.hasDerivWithinAt
    · intro t ht heq
      have ht' := Ico_subset_Icc_self ht
      have hLT : L * t ≤ 1/2 := by
        have h1 : t ≤ 1 / (2 * L) := le_trans ht.2.le hT
        rw [le_div_iff₀ (by positivity)] at h1; nlinarith
      have hyt0 : 0 ≤ y t := by rw [heq]; nlinarith [ht.1]
      have hyK : y t ≤ Y + 1 := by rw [heq]; linarith
      have := (hf'spec t ht').2
      have hp : (y t) ^ (3/2 : ℝ) ≤ (Y + 1) ^ (3/2 : ℝ) :=
        Real.rpow_le_rpow hyt0 hyK (by norm_num)
      have : f' t ≤ C * (Y + 1) ^ (3/2 : ℝ) := this.trans (mul_le_mul_of_nonneg_left hp hC)
      linarith
  intro t ht
  have h1 : t ≤ 1 / (2 * L) := le_trans ht.2 hT
  rw [le_div_iff₀ (by positivity)] at h1
  have := hB t ht; nlinarith [ht.1]

/-- **Proved.** Truncation does not increase the `H^s` norm. -/
theorem hsNormField_extendG_restrictG_le {s : ℝ} {a : FField} (ha : MemHsField s a) (N : ℕ) :
    hsNormField s (extendG (restrictG N a)) ≤ hsNormField s a := by
  unfold hsNormField
  apply Real.sqrt_le_sqrt
  have hle : ∀ p : Mode × Fin 3, sobW s p.1 * ‖extendG (restrictG N a) p.1 p.2‖ ^ 2 ≤
      sobW s p.1 * ‖a p.1 p.2‖ ^ 2 := by
    intro p
    by_cases h : p.1 ∈ modeBox N
    · simp [extendG, restrictG, h]
    · simp only [extendG, h, dif_neg, not_false_eq_true]
      simp; exact mul_nonneg (sobW_pos s p.1).le (sq_nonneg _)
  have hnn : ∀ p : Mode × Fin 3, 0 ≤ sobW s p.1 * ‖extendG (restrictG N a) p.1 p.2‖ ^ 2 :=
    fun p => mul_nonneg (sobW_pos s p.1).le (sq_nonneg _)
  exact (Summable.of_nonneg_of_le hnn hle ha).tsum_le_tsum hle ha

/-- **Named Prop (NOT proved).** The Galerkin `H^s` energy inequality
`d/dt ‖u_N‖²_{H^s} ≤ C (‖u_N‖²_{H^s})^{3/2}` along Hermitian divergence-free states, with `C`
independent of `N`. -/
def GalerkinHsEnergyInequality (ν s C : ℝ) : Prop :=
  ∀ (N : ℕ) (α : ℝ → GState N) (t : ℝ), HasDerivAt α (galerkinNSField N ν (α t)) t →
    HermitianField (extendG (α t)) → DivergenceFree (extendG (α t)) →
    ∃ d, HasDerivAt (fun τ => hsNormField s (extendG (α τ)) ^ 2) d t ∧
      d ≤ C * (hsNormField s (extendG (α t)) ^ 2) ^ (3/2 : ℝ)

/-- **Conditional (on `GalerkinHsEnergyInequality`).** Uniform-in-`N` a priori bound on the
explicit time `barrierTime C ‖a‖²_{H^s}`. -/
theorem galerkin_uniform_bound_of_energy {ν s C : ℝ} (hC : 0 ≤ C)
    (hE : GalerkinHsEnergyInequality ν s C) {a : FField} (ha : MemHsField s a)
    {N : ℕ} {α : ℝ → GState N} {T : ℝ}
    (hT : T ≤ barrierTime C (hsNormField s a ^ 2))
    (h0 : α 0 = restrictG N a)
    (hα : ∀ t ∈ Icc 0 T, HasDerivAt α (galerkinNSField N ν (α t)) t)
    (hstruct : ∀ t ∈ Icc 0 T, HermitianField (extendG (α t)) ∧ DivergenceFree (extendG (α t))) :
    ∀ t ∈ Icc 0 T, hsNormField s (extendG (α t)) ^ 2 ≤ hsNormField s a ^ 2 + 1 := by
  refine ode_barrier (y := fun τ => hsNormField s (extendG (α τ)) ^ 2) hC (sq_nonneg _) ?_ hT ?_
  · simp only [h0]
    exact pow_le_pow_left₀ (hsNormField_nonneg _ _) (hsNormField_extendG_restrictG_le ha N) 2
  · intro t ht
    exact hE N α t (hα t ht) (hstruct t ht).1 (hstruct t ht).2

/-! ### Energy identity for the Galerkin system (proved) and reduction to a static bound -/

/-- **Proved.** `‖extendG v‖²_{H^s}` is the finite sum over the mode box. -/
theorem hsNormSq_extendG (s : ℝ) {N : ℕ} (v : GState N) :
    hsNormField s (extendG v) ^ 2 = ∑ k : modeBox N, ∑ i, sobW s k.1 * ‖v k i‖ ^ 2 := by
  classical
  have hsupp : ∀ p ∉ (modeBox N ×ˢ (Finset.univ : Finset (Fin 3))),
      sobW s p.1 * ‖extendG v p.1 p.2‖ ^ 2 = 0 := by
    intro p hp
    have : p.1 ∉ modeBox N := by simpa [Finset.mem_product] using hp
    simp [extendG, this]
  have htsum := tsum_eq_sum (L := SummationFilter.unconditional (Mode × Fin 3)) hsupp
  unfold hsNormField
  rw [Real.sq_sqrt (tsum_nonneg fun p : Mode × Fin 3 => mul_nonneg (sobW_pos s p.1).le (sq_nonneg ‖extendG v p.1 p.2‖)), htsum,
    Finset.sum_product, ← Finset.sum_coe_sort (modeBox N)]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [extendG_apply]

/-- **Proved.** Derivative of `‖u_N(t)‖²_{H^s}` along any `C¹` curve in `GState N`. -/
theorem hsNormSq_extendG_hasDerivAt (s : ℝ) {N : ℕ} {α : ℝ → GState N} {F : GState N} {t : ℝ}
    (hα : HasDerivAt α F t) :
    HasDerivAt (fun τ => hsNormField s (extendG (α τ)) ^ 2)
      (∑ k : modeBox N, ∑ i, sobW s k.1 * (2 * inner ℝ (α t k i) (F k i))) t := by
  simp only [hsNormSq_extendG]
  apply HasDerivAt.fun_sum; intro k _
  apply HasDerivAt.fun_sum; intro i _
  have hk := (hasDerivAt_pi.1 hα) k
  have hki := (hasDerivAt_pi.1 hk) i
  exact hki.norm_sq.const_mul _

lemma galerkinNSField_apply {N : ℕ} (ν : ℝ) (u : GState N) (k : modeBox N) (i : Fin 3) :
    galerkinNSField N ν u k i = (-viscCoeff ν k.1) • u k i + -(nsBilin u u k i) := rfl

/-- **Named Prop (NOT proved).** Static transport bound: the `H^s` pairing of `u` with the
projected nonlinearity is `≤ C ‖u‖³_{H^s}` (Hermitian, divergence-free `u`, `C` independent of
`N`). This is where the transport cancellation and the commutator estimate enter. -/
def GalerkinTransportBound (s C : ℝ) : Prop :=
  ∀ (N : ℕ) (v : GState N), HermitianField (extendG v) → DivergenceFree (extendG v) →
    ∑ k : modeBox N, ∑ i, sobW s k.1 * (2 * inner ℝ (v k i) (-(nsBilin v v k i))) ≤
      C * (hsNormField s (extendG v) ^ 2) ^ (3/2 : ℝ)

lemma viscCoeff_nonneg {ν : ℝ} (hν : 0 ≤ ν) (k : Mode) : 0 ≤ viscCoeff ν k := by
  unfold viscCoeff ksq; positivity

/-- **Proved.** For `ν ≥ 0` the viscous term only dissipates, so the static transport bound
implies the Galerkin `H^s` energy inequality. -/
theorem galerkinHsEnergyInequality_of_transport {ν s C : ℝ} (hν : 0 ≤ ν)
    (hB : GalerkinTransportBound s C) : GalerkinHsEnergyInequality ν s C := by
  intro N α t hα hH hD
  refine ⟨_, hsNormSq_extendG_hasDerivAt s hα, ?_⟩
  refine le_trans ?_ (hB N (α t) hH hD)
  apply Finset.sum_le_sum; intro k _
  apply Finset.sum_le_sum; intro i _
  rw [galerkinNSField_apply, inner_add_right]
  have hv : inner ℝ (α t k i) ((-viscCoeff ν k.1) • α t k i) = -viscCoeff ν k.1 * ‖α t k i‖ ^ 2 := by
    simp [Complex.inner, Complex.real_smul, Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hv]
  have h1 := viscCoeff_nonneg hν k.1
  have h2 := (sobW_pos s k.1).le
  have : sobW s k.1 * (2 * (-viscCoeff ν k.1 * ‖α t k i‖ ^ 2)) ≤ 0 := by
    have : 0 ≤ viscCoeff ν k.1 * ‖α t k i‖ ^ 2 := by positivity
    nlinarith
  nlinarith

end TorusFourierNS
