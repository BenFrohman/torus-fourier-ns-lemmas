/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import TorusFourierNS.TransportBound

/-!
# Tame transport bound and propagation of higher Galerkin regularity

**Proved.**
* `galerkinTameTransportBound_of_gt` (`5/2 < s₀`, `2 ≤ s`): for Hermitian, divergence-free
  Galerkin fields the `H^s` transport pairing is at most `tameConst s₀ s · ‖v‖_{H^{s₀}} · ‖v‖²_{H^s}`.
  This is linear in the top norm (tame). It reuses the commutator bound `norm_triTerm_sub_le`,
  the cancellation `triTerm_sym_cancel` and the Young bounds from `TransportBound.lean`. The only
  change is that the `ℓ¹` factor is measured in `H^{s₀}` rather than `H^s`.
* `galerkinTameEnergyInequality_of_gt` (`ν ≥ 0`): the matching energy inequality.
* `galerkin_hs_propagation` (Grönwall): if a Galerkin solution stays Hermitian, divergence-free
  and `‖·‖_{H^{s₀}} ≤ A` on `[0,T]`, then
  `‖α t‖²_{H^s} ≤ ‖α 0‖²_{H^s} · exp(tameConst s₀ s · A · t)` on `[0,T]`, for every `s ≥ 2`.

All names are coined.
-/

noncomputable section
open Complex

namespace TorusFourierNS

/-- Coined: constant of the tame transport bound. -/
def tameConst (s₀ s : ℝ) : ℝ :=
  24 * Real.sqrt 3 * Real.pi * kpConst s * Real.sqrt (∑' k : Mode, sobW (-(s₀ - 1)) k)

/-- Coined: the tame static transport bound. -/
def GalerkinTameTransportBound (s₀ s C : ℝ) : Prop :=
  ∀ (N : ℕ) (v : GState N), HermitianField (extendG v) → DivergenceFree (extendG v) →
    ∑ k : modeBox N, ∑ i, sobW s k.1 * (2 * inner ℝ (v k i) (-(nsBilin v v k i))) ≤
      C * hsNormField s₀ (extendG v) * hsNormField s (extendG v) ^ 2

/-- **Proved (tame Kato–Ponce bound with transport cancellation).** -/
theorem galerkinTameTransportBound_of_gt {s₀ s : ℝ} (hs₀ : 5 / 2 < s₀) (hs2 : 2 ≤ s) :
    GalerkinTameTransportBound s₀ s (tameConst s₀ s) := by
  classical
  intro N v hH hD
  set B := modeBox N
  set u := extendG v
  have hu : ∀ k ∉ B, u k = 0 := fun k hk => by
    have hk' : k ∉ modeBox N := hk
    funext i; simp [u, extendG, hk']
  have haC : ∀ k ∉ B, aC u k = 0 := fun k hk => by simp [aC, hu k hk]
  have hsq : ∀ r : ℝ, hsNormField r u ^ 2 = ∑ k ∈ B, ∑ i, sobW r k * ‖u k i‖ ^ 2 := fun r => by
    rw [hsNormSq_extendG, ← Finset.sum_coe_sort B]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    simp [u, extendG_apply]
  set h := hsNormField s u ^ 2 with hh
  set h₀ := hsNormField s₀ u ^ 2 with hh₀
  have h0 : 0 ≤ h := sq_nonneg _
  have h00 : 0 ≤ h₀ := sq_nonneg _
  have hY2gen : ∀ r : ℝ, ∑ k ∈ B, (sig r k * aC u k) ^ 2 ≤ 3 * hsNormField r u ^ 2 := fun r => by
    rw [hsq r, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    simp only [mul_pow, sig_sq, aC]
    have := sq_sum_fin3_le (fun i => ‖u k i‖)
    have hw := (sobW_pos r k).le
    rw [← Finset.mul_sum]
    nlinarith
  set Y : Mode → ℝ := fun k => sig s k * aC u k
  set Y₀ : Mode → ℝ := fun k => sig s₀ k * aC u k
  set X : Mode → ℝ := fun k => br k * aC u k
  have hY0 : ∀ k ∉ B, Y k = 0 := fun k hk => by simp [Y, haC k hk]
  have hX0 : ∀ k, 0 ≤ X k := fun k => mul_nonneg (br_nonneg k) (aC_nonneg u k)
  have hY0' : ∀ k, 0 ≤ Y k := fun k => mul_nonneg (sig_nonneg s k) (aC_nonneg u k)
  have hY2 : ∑ k ∈ B, Y k ^ 2 ≤ 3 * h := hY2gen s
  have hY02 : ∑ k ∈ B, Y₀ k ^ 2 ≤ 3 * h₀ := hY2gen s₀
  set S := ∑' k : Mode, sobW (-(s₀ - 1)) k
  have hSsum : Summable fun k : Mode => sobW (-(s₀ - 1)) k := summable_sobW_neg (by linarith)
  have hS0 : 0 ≤ S := tsum_nonneg fun k => (sobW_pos _ k).le
  have hX1 : ∑ k ∈ B, X k ≤ Real.sqrt S * Real.sqrt (3 * h₀) := by
    have e : ∀ k, X k = Real.sqrt (sobW (-(s₀ - 1)) k) * Y₀ k := fun k => by
      simp only [X, Y₀, br_eq s₀ k]; ring
    simp only [e]
    refine (Real.sum_mul_le_sqrt_mul_sqrt B _ _).trans ?_
    gcongr
    · simp only [Real.sq_sqrt (sobW_pos _ _).le]
      exact hSsum.sum_le_tsum B (fun k _ => (sobW_pos _ k).le)
  set Ysq := Real.sqrt (∑ k ∈ B, Y k ^ 2)
  have hYsq : Ysq ≤ Real.sqrt (3 * h) := Real.sqrt_le_sqrt hY2
  have hYsq0 : 0 ≤ Ysq := Real.sqrt_nonneg _
  set T := ∑ p ∈ triDom B, triTerm u (fun k _ => sobW s k) p
  have hT : T = ∑ p ∈ triDom B,
      (triTerm u (fun k _ => sobW s k) p - triTerm u (fun k j => sig s k * sig s j) p) := by
    rw [Finset.sum_sub_distrib, triTerm_sym_cancel s hH hD, sub_zero]
  have hK := kpConst_nonneg hs2
  have hTb : ‖T‖ ≤ kpConst s * (2 * (Real.sqrt S * Real.sqrt (3 * h₀) * Real.sqrt (3 * h) *
      Real.sqrt (3 * h))) := by
    rw [hT]
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => norm_triTerm_sub_le hs2 u p).trans ?_
    have hsub : triDom B ⊆ B ×ˢ B := Finset.filter_subset _ _
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by
      have := hX0 p.1; have := hX0 p.2; have := hY0' p.1; have := hY0' p.2
      have := hY0' (p.1 + p.2)
      exact mul_nonneg hK (by positivity))).trans ?_
    rw [Finset.sum_product]
    simp only [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hK
    show ∑ m ∈ B, ∑ j ∈ B, (X m * Y (m + j) * Y j + Y m * Y (m + j) * X j) ≤ _
    simp only [Finset.sum_add_distrib]
    have y1 := young_box B X Y Y hX0 hY0
    have y2 := young_box' B Y Y X hX0 hY0
    have hb1 : (∑ m ∈ B, X m) * Ysq * Ysq ≤
        Real.sqrt S * Real.sqrt (3 * h₀) * Real.sqrt (3 * h) * Real.sqrt (3 * h) := by
      have := Real.sqrt_nonneg S; have := Real.sqrt_nonneg (3 * h₀)
      have := Real.sqrt_nonneg (3 * h)
      have hX1' : 0 ≤ ∑ m ∈ B, X m := Finset.sum_nonneg fun k _ => hX0 k
      calc (∑ m ∈ B, X m) * Ysq * Ysq ≤ (Real.sqrt S * Real.sqrt (3 * h₀)) * Real.sqrt (3 * h) *
            Real.sqrt (3 * h) := by gcongr
        _ = _ := by ring
    linarith
  have hLHS := transport_pairing_eq s v hD
  rw [preTerm_sum_eq u hu] at hLHS
  change _ = -2 * (2 * Real.pi * I * T).re at hLHS
  rw [hLHS]
  have hre : -2 * (2 * Real.pi * I * T).re ≤ 4 * Real.pi * ‖T‖ := by
    have := Complex.abs_re_le_norm (2 * Real.pi * I * T)
    have hn : ‖(2 * Real.pi * I * T : ℂ)‖ = 2 * Real.pi * ‖T‖ := by
      simp [Real.pi_pos.le]
    rw [hn] at this
    linarith [abs_le.1 this]
  refine hre.trans ?_
  have e3 : Real.sqrt (3 * h₀) * Real.sqrt (3 * h) * Real.sqrt (3 * h) =
      3 * Real.sqrt 3 * (hsNormField s₀ u * h) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_mul (by norm_num), hh₀,
      Real.sqrt_sq (hsNormField_nonneg _ _)]
    have a := Real.mul_self_sqrt h0
    have b := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)
    calc Real.sqrt 3 * hsNormField s₀ u * (Real.sqrt 3 * Real.sqrt h) * (Real.sqrt 3 * Real.sqrt h)
        = (Real.sqrt 3 * Real.sqrt 3) * Real.sqrt 3 * (hsNormField s₀ u * (Real.sqrt h * Real.sqrt h)) := by
          ring
      _ = _ := by rw [a, b]
  have : ‖T‖ ≤ kpConst s * (6 * Real.sqrt 3 * Real.sqrt S * (hsNormField s₀ u * h)) := by
    refine hTb.trans (le_of_eq ?_)
    have e4 : Real.sqrt S * Real.sqrt (3 * h₀) * Real.sqrt (3 * h) * Real.sqrt (3 * h) =
        Real.sqrt S * (3 * Real.sqrt 3 * (hsNormField s₀ u * h)) := by rw [← e3]; ring
    rw [e4]; ring
  unfold tameConst
  show 4 * Real.pi * ‖T‖ ≤ 24 * Real.sqrt 3 * Real.pi * kpConst s * Real.sqrt S *
    hsNormField s₀ u * h
  have := Real.pi_pos
  calc 4 * Real.pi * ‖T‖ ≤ 4 * Real.pi * (kpConst s * (6 * Real.sqrt 3 * Real.sqrt S *
      (hsNormField s₀ u * h))) := by gcongr
    _ = _ := by ring

/-- Coined: the tame Galerkin energy inequality. -/
def GalerkinTameEnergyInequality (ν s₀ s C : ℝ) : Prop :=
  ∀ (N : ℕ) (α : ℝ → GState N) (t : ℝ), HasDerivAt α (galerkinNSField N ν (α t)) t →
    HermitianField (extendG (α t)) → DivergenceFree (extendG (α t)) →
    ∃ d, HasDerivAt (fun τ => hsNormField s (extendG (α τ)) ^ 2) d t ∧
      d ≤ C * hsNormField s₀ (extendG (α t)) * hsNormField s (extendG (α t)) ^ 2

/-- **Proved (`ν ≥ 0`, `5/2 < s₀`, `2 ≤ s`).** -/
theorem galerkinTameEnergyInequality_of_gt {ν s₀ s : ℝ} (hν : 0 ≤ ν) (hs₀ : 5 / 2 < s₀)
    (hs2 : 2 ≤ s) : GalerkinTameEnergyInequality ν s₀ s (tameConst s₀ s) := by
  intro N α t hα hH hD
  refine ⟨_, hsNormSq_extendG_hasDerivAt s hα, ?_⟩
  refine le_trans ?_ (galerkinTameTransportBound_of_gt hs₀ hs2 N (α t) hH hD)
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

lemma tameConst_nonneg {s₀ s : ℝ} (hs : 2 ≤ s) : 0 ≤ tameConst s₀ s := by
  unfold tameConst
  have := kpConst_nonneg hs
  have := Real.pi_pos.le
  positivity

/-- **Proved (Grönwall).** Propagation of `H^s` regularity for Galerkin solutions under an
`H^{s₀}` bound, `ν ≥ 0`, `5/2 < s₀`, `2 ≤ s`. -/
theorem galerkin_hs_propagation {ν s₀ s : ℝ} (hν : 0 ≤ ν) (hs₀ : 5 / 2 < s₀) (hs2 : 2 ≤ s)
    {N : ℕ} {α : ℝ → GState N} {T A : ℝ}
    (hα : ∀ t ∈ Set.Icc 0 T, HasDerivAt α (galerkinNSField N ν (α t)) t)
    (hstruct : ∀ t ∈ Set.Icc 0 T, HermitianField (extendG (α t)) ∧ DivergenceFree (extendG (α t)))
    (hA : ∀ t ∈ Set.Icc 0 T, hsNormField s₀ (extendG (α t)) ≤ A) :
    ∀ t ∈ Set.Icc 0 T, hsNormField s (extendG (α t)) ^ 2 ≤
      hsNormField s (extendG (α 0)) ^ 2 * Real.exp (tameConst s₀ s * A * t) := by
  set K := tameConst s₀ s * A
  set y : ℝ → ℝ := fun τ => hsNormField s (extendG (α τ)) ^ 2
  have hC := tameConst_nonneg (s₀ := s₀) hs2
  have hE := galerkinTameEnergyInequality_of_gt hν hs₀ hs2
  -- g τ = y τ * exp (-K τ) is antitone on [0,T]
  have hder : ∀ τ ∈ Set.Icc 0 T, ∃ d, HasDerivAt y d τ ∧ d ≤ K * y τ := fun τ hτ => by
    obtain ⟨d, hd, hdle⟩ := hE N α τ (hα τ hτ) (hstruct τ hτ).1 (hstruct τ hτ).2
    refine ⟨d, hd, hdle.trans ?_⟩
    have := sq_nonneg (hsNormField s (extendG (α τ)))
    have := hA τ hτ
    calc tameConst s₀ s * hsNormField s₀ (extendG (α τ)) * hsNormField s (extendG (α τ)) ^ 2
        ≤ tameConst s₀ s * A * hsNormField s (extendG (α τ)) ^ 2 := by gcongr
      _ = K * y τ := rfl
  choose! d hd hdle using hder
  set g : ℝ → ℝ := fun τ => y τ * Real.exp (-(K * τ))
  have hg' : ∀ τ ∈ Set.Icc 0 T, HasDerivAt g (d τ * Real.exp (-(K * τ)) +
      y τ * (Real.exp (-(K * τ)) * (-K))) τ := fun τ hτ => by
    have h1 : HasDerivAt (fun τ => -(K * τ)) (-K) τ := by
      simpa using ((hasDerivAt_id τ).const_mul K).neg
    exact (hd τ hτ).mul (h1.exp)
  have hanti : AntitoneOn g (Set.Icc 0 T) := by
    have hneg : MonotoneOn (fun τ => -g τ) (Set.Icc 0 T) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T)
        (f' := fun τ => -(d τ * Real.exp (-(K * τ)) + y τ * (Real.exp (-(K * τ)) * (-K))))
        (fun τ hτ => (hg' τ hτ).continuousAt.continuousWithinAt.neg)
        (fun τ hτ => (hg' τ (interior_subset hτ)).neg.hasDerivWithinAt) (fun τ hτ => ?_)
      have := hdle τ (interior_subset hτ)
      have he := Real.exp_pos (-(K * τ))
      nlinarith
    intro a ha b hb hab
    have := hneg ha hb hab
    simp only at this; linarith
  intro t ht
  have h0T : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have := hanti h0T ht ht.1
  simp only [g, mul_zero, neg_zero, Real.exp_zero, mul_one] at this
  have he := Real.exp_pos (K * t)
  calc y t = y t * Real.exp (-(K * t)) * Real.exp (K * t) := by
        rw [mul_assoc, ← Real.exp_add]; simp
    _ ≤ y 0 * Real.exp (K * t) := by gcongr

end TorusFourierNS
