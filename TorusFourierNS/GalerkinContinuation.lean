/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import TorusFourierNS.GalerkinStructure

/-!
# Continuation of the Galerkin NS ODE under an a priori bound

**Proved:**
* `galerkinNS_continuation_of_normBound`: if every solution of `v' = galerkinNSField N ν v`,
  `v 0 = x₀`, on any `[0,T'] ⊆ [0,T]` satisfies `‖v t‖ ≤ R`, then a solution exists on all of
  `[0,T]` (two-sided derivative at every point of `[0,T]`).
  Proof: clamp the field outside a ball (globally Lipschitz, bounded), apply Picard–Lindelöf
  on `[-1,T+1]`, then real induction shows the clamped solution never leaves the ball.
* `norm_le_hsNormField_mul`: on `GState N`, `‖v‖ ≤ ‖extendG v‖_{H^s} · D(N,s)`.
* `galerkinNS_continuation_of_hsBound`: the same continuation with an `H^s` a priori bound.

Coined names: `clampC`, `clampG`, `clamp_real_abs`, `clampC_dist_le`, `clampC_norm_le`,
`clampC_of_norm_le`, `clampG_dist_le`, `clampG_norm_le`,
`clampG_of_norm_le`, `galerkinNS_continuation_of_normBound`, `hsBoxConst`, `hsBoxConst_nonneg`,
`norm_le_hsNormField_mul`, `galerkinNS_continuation_of_hsBound`.
-/

noncomputable section
open Set Filter Topology Metric

namespace TorusFourierNS

/-- Componentwise clamp of real and imaginary parts to `[-ρ, ρ]` (coined). -/
def clampC (ρ : ℝ) (z : ℂ) : ℂ := ⟨max (-ρ) (min ρ z.re), max (-ρ) (min ρ z.im)⟩

lemma clamp_real_abs (ρ a b : ℝ) :
    |max (-ρ) (min ρ a) - max (-ρ) (min ρ b)| ≤ |a - b| := by
  rw [max_comm (-ρ), max_comm (-ρ)]
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  simp

lemma clampC_dist_le (ρ : ℝ) (z w : ℂ) : dist (clampC ρ z) (clampC ρ w) ≤ dist z w := by
  rw [Complex.dist_eq_re_im, Complex.dist_eq_re_im]
  apply Real.sqrt_le_sqrt
  simp only [clampC]
  have h1 := clamp_real_abs ρ z.re w.re
  have h2 := clamp_real_abs ρ z.im w.im
  have := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
  have := sq_le_sq' (abs_le.1 h2).1 (abs_le.1 h2).2
  rw [sq_abs] at *
  linarith

lemma clampC_norm_le {ρ : ℝ} (hρ : 0 ≤ ρ) (z : ℂ) : ‖clampC ρ z‖ ≤ 2 * ρ := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [clampC]
  have h : ∀ a : ℝ, |max (-ρ) (min ρ a)| ≤ ρ := fun a => by
    rw [abs_le]; constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  linarith [h z.re, h z.im]

lemma clampC_of_norm_le {ρ : ℝ} {z : ℂ} (hz : ‖z‖ ≤ ρ) : clampC ρ z = z := by
  have hr := (abs_le.1 ((Complex.abs_re_le_norm z).trans hz))
  have hi := (abs_le.1 ((Complex.abs_im_le_norm z).trans hz))
  apply Complex.ext <;> simp only [clampC]
  · rw [min_eq_right hr.2, max_eq_right hr.1]
  · rw [min_eq_right hi.2, max_eq_right hi.1]

variable {N : ℕ}

/-- Componentwise clamp on `GState N` (coined). -/
def clampG (ρ : ℝ) (x : GState N) : GState N := fun k i => clampC ρ (x k i)

lemma clampG_dist_le (ρ : ℝ) (x y : GState N) : dist (clampG ρ x) (clampG ρ y) ≤ dist x y := by
  refine (dist_pi_le_iff dist_nonneg).2 fun k => (dist_pi_le_iff dist_nonneg).2 fun i => ?_
  exact (clampC_dist_le ρ _ _).trans ((dist_le_pi_dist (x k) (y k) i).trans (dist_le_pi_dist x y k))

lemma clampG_norm_le {ρ : ℝ} (hρ : 0 ≤ ρ) (x : GState N) : ‖clampG ρ x‖ ≤ 2 * ρ :=
  (pi_norm_le_iff_of_nonneg (by linarith)).2 fun k =>
    (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => clampC_norm_le hρ _

lemma clampG_of_norm_le {ρ : ℝ} {x : GState N} (hx : ‖x‖ ≤ ρ) : clampG ρ x = x := by
  funext k i
  exact clampC_of_norm_le (((norm_le_pi_norm (x k) i).trans (norm_le_pi_norm x k)).trans hx)

/-- **Proved.** Continuation of the Galerkin NS ODE under an a priori sup-norm bound. -/
theorem galerkinNS_continuation_of_normBound (ν : ℝ) (x₀ : GState N) {T : ℝ} (hT : 0 < T)
    (R : ℝ)
    (hB : ∀ T' ∈ Icc 0 T, ∀ α : ℝ → GState N, α 0 = x₀ →
      (∀ t ∈ Icc 0 T', HasDerivAt α (galerkinNSField N ν (α t)) t) →
      ∀ t ∈ Icc 0 T', ‖α t‖ ≤ R) :
    ∃ α : ℝ → GState N, α 0 = x₀ ∧
      ∀ t ∈ Icc 0 T, HasDerivAt α (galerkinNSField N ν (α t)) t := by
  set F := galerkinNSField N ν with hFdef
  set ρ : ℝ := max R ‖x₀‖ + 1 with hρ
  have hρ0 : 0 ≤ ρ := by have := le_max_right R ‖x₀‖; positivity
  have hRρ : R < ρ := by have := le_max_left R ‖x₀‖; linarith
  have hx₀ρ : ‖x₀‖ < ρ := by have := le_max_right R ‖x₀‖; linarith
  have hcpt : IsCompact (closedBall (0 : GState N) (2 * ρ)) := isCompact_closedBall _ _
  obtain ⟨K, hK⟩ := ((galerkinNSField_contDiff (N := N) ν).locallyLipschitz.locallyLipschitzOn
    (s := closedBall (0 : GState N) (2 * ρ))).exists_lipschitzOnWith_of_compact hcpt
  obtain ⟨L0, hL0⟩ := hcpt.exists_bound_of_continuousOn
    (galerkinNSField_contDiff (N := N) ν).continuous.continuousOn
  have hmem : ∀ x : GState N, clampG ρ x ∈ closedBall (0 : GState N) (2 * ρ) := fun x => by
    rw [mem_closedBall, dist_zero_right]; exact clampG_norm_le hρ0 x
  set G : GState N → GState N := fun x => F (clampG ρ x) with hG
  set L : NNReal := Real.toNNReal L0 with hL
  set a : NNReal := L * Real.toNNReal (T + 1) with ha
  have hGlip : LipschitzOnWith K G (closedBall x₀ a) :=
    LipschitzOnWith.of_dist_le_mul fun x _ y _ =>
      (hK.dist_le_mul _ (hmem x) _ (hmem y)).trans
        (mul_le_mul_of_nonneg_left (clampG_dist_le ρ x y) K.2)
  have hGb : ∀ x ∈ closedBall x₀ a, ‖G x‖ ≤ L := fun x _ =>
    (hL0 _ (hmem x)).trans (Real.le_coe_toNNReal L0)
  have hT0 : (0 : ℝ) ∈ Icc (-1) (T + 1) := ⟨by norm_num, by linarith⟩
  have hPL : IsPicardLindelof (fun _ => G) (tmin := -1) (tmax := T + 1) ⟨0, hT0⟩ x₀ a 0 L K := by
    apply IsPicardLindelof.of_time_independent hGb hGlip
    simp only [ha, NNReal.coe_mul, Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ T + 1),
      NNReal.coe_zero, sub_zero, zero_sub, neg_neg]
    rw [max_eq_left (by linarith)]
  obtain ⟨β, hβ0, hβ⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hβ0' : β 0 = x₀ := hβ0
  have hβd : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt β (G (β t)) t := fun t ht =>
    (hβ t ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivAt
      (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
  have hβc : ∀ t ∈ Icc (0:ℝ) T, ContinuousAt β t := fun t ht => (hβd t ht).continuousAt
  have hGF : ∀ x : GState N, ‖x‖ ≤ ρ → G x = F x := fun x hx => by
    simp only [hG, clampG_of_norm_le hx]
  have key : ∀ t ∈ Icc (0:ℝ) T, (∀ u ∈ Icc 0 t, ‖β u‖ ≤ ρ) → ∀ u ∈ Icc 0 t, ‖β u‖ ≤ R := by
    intro t ht hρt
    refine hB t ht β hβ0' fun u hu => ?_
    rw [← hGF _ (hρt u hu)]
    exact hβd u ⟨hu.1, hu.2.trans ht.2⟩
  set S : Set ℝ := {t | ∀ u ∈ Icc 0 t, ‖β u‖ ≤ R} with hS
  have hC : IsClosed (Icc (0:ℝ) T ∩ β ⁻¹' {x | ‖x‖ ≤ R}) :=
    ContinuousOn.preimage_isClosed_of_isClosed
      (fun t ht => (hβc t ht).continuousWithinAt) isClosed_Icc
      (isClosed_le continuous_norm continuous_const)
  have hsub : S ∩ Icc 0 T ⊆ Icc (0:ℝ) T ∩ β ⁻¹' {x | ‖x‖ ≤ R} := fun t ht =>
    ⟨ht.2, ht.1 t ⟨ht.2.1, le_rfl⟩⟩
  have hclosed : IsClosed (S ∩ Icc 0 T) := by
    refine isClosed_of_closure_subset fun t ht => ?_
    have htI : t ∈ Icc (0:ℝ) T := closure_minimal inter_subset_right isClosed_Icc ht
    refine ⟨fun u hu => ?_, htI⟩
    rcases eq_or_lt_of_le hu.2 with h | h
    · subst h
      exact (closure_minimal hsub hC ht).2
    · obtain ⟨b, hb, hdb⟩ := Metric.mem_closure_iff.1 ht (t - u) (by linarith)
      rw [Real.dist_eq] at hdb
      have := (abs_lt.1 hdb).2
      exact hb.1 u ⟨hu.1, by linarith⟩
  have hIcc : Icc (0:ℝ) T ⊆ S := by
    refine hclosed.Icc_subset_of_forall_mem_nhdsWithin ?_ ?_
    · have h0 : (0:ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
      refine key 0 h0 fun u hu => ?_
      rw [le_antisymm hu.2 hu.1, hβ0']; exact hx₀ρ.le
    · intro x hx
      have hxI : x ∈ Icc (0:ℝ) T := ⟨hx.2.1, hx.2.2.le⟩
      have hxR : ‖β x‖ ≤ R := hx.1 x ⟨hx.2.1, le_rfl⟩
      have hev : ∀ᶠ y in 𝓝 x, ‖β y‖ < ρ :=
        (hβc x hxI).norm.eventually (gt_mem_nhds (hxR.trans_lt hRρ))
      obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hev
      have hIoo : Ioo x (min (x + ε) T) ⊆ S := by
        intro y hy
        have hyI : y ∈ Icc (0:ℝ) T := ⟨by linarith [hy.1, hx.2.1], hy.2.le.trans (min_le_right _ _)⟩
        refine key y hyI fun v hv => ?_
        rcases le_or_gt v x with hvx | hvx
        · exact (hx.1 v ⟨hv.1, hvx⟩).trans hRρ.le
        · refine (hεb ?_).le
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [hy.2.trans_le (min_le_left _ _), hv.2]
      exact mem_of_superset (Ioo_mem_nhdsGT (lt_min (by linarith) hx.2.2)) hIoo
  refine ⟨β, hβ0', fun t ht => ?_⟩
  rw [← hGF _ ((hIcc ht t ⟨ht.1, le_rfl⟩).trans hRρ.le)]
  exact hβd t ht

/-- `Σ_{k ∈ box} (1+|k|²)^{-s/2}` (coined). -/
def hsBoxConst (N : ℕ) (s : ℝ) : ℝ := ∑ k : modeBox N, (Real.sqrt (sobW s k.1))⁻¹

lemma hsBoxConst_nonneg (N : ℕ) (s : ℝ) : 0 ≤ hsBoxConst N s :=
  Finset.sum_nonneg fun _ _ => inv_nonneg.2 (Real.sqrt_nonneg _)

/-- **Proved.** Sup norm on `GState N` is controlled by the `H^s` norm of the extension. -/
theorem norm_le_hsNormField_mul (s : ℝ) (v : GState N) :
    ‖v‖ ≤ hsNormField s (extendG v) * hsBoxConst N s := by
  have hh : 0 ≤ hsNormField s (extendG v) := Real.sqrt_nonneg _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hh (hsBoxConst_nonneg N s))).2 fun k =>
    (pi_norm_le_iff_of_nonneg (mul_nonneg hh (hsBoxConst_nonneg N s))).2 fun i => ?_
  have hw := sobW_pos s k.1
  have h1 : sobW s k.1 * ‖v k i‖ ^ 2 ≤ hsNormField s (extendG v) ^ 2 := by
    rw [hsNormSq_extendG]
    refine le_trans ?_ (Finset.single_le_sum (f := fun k : modeBox N =>
      ∑ i, sobW s k.1 * ‖v k i‖ ^ 2) (fun k _ => Finset.sum_nonneg fun i _ =>
        mul_nonneg (sobW_pos s k.1).le (sq_nonneg _)) (Finset.mem_univ k))
    exact Finset.single_le_sum (f := fun i => sobW s k.1 * ‖v k i‖ ^ 2)
      (fun i _ => mul_nonneg hw.le (sq_nonneg _)) (Finset.mem_univ i)
  have hsq : Real.sqrt (sobW s k.1) * ‖v k i‖ ≤ hsNormField s (extendG v) := by
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_mul hw.le, Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hh] at this
  have hsw : 0 < Real.sqrt (sobW s k.1) := Real.sqrt_pos.2 hw
  have h2 : ‖v k i‖ ≤ hsNormField s (extendG v) * (Real.sqrt (sobW s k.1))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hsw]; linarith
  refine h2.trans (mul_le_mul_of_nonneg_left ?_ hh)
  exact Finset.single_le_sum (f := fun k : modeBox N => (Real.sqrt (sobW s k.1))⁻¹)
    (fun _ _ => inv_nonneg.2 (Real.sqrt_nonneg _)) (Finset.mem_univ k)

/-- **Proved.** Continuation of the Galerkin NS ODE under an a priori `H^s` bound. -/
theorem galerkinNS_continuation_of_hsBound (ν s : ℝ) (x₀ : GState N) {T : ℝ} (hT : 0 < T)
    (M : ℝ)
    (hB : ∀ T' ∈ Icc 0 T, ∀ α : ℝ → GState N, α 0 = x₀ →
      (∀ t ∈ Icc 0 T', HasDerivAt α (galerkinNSField N ν (α t)) t) →
      ∀ t ∈ Icc 0 T', hsNormField s (extendG (α t)) ≤ M) :
    ∃ α : ℝ → GState N, α 0 = x₀ ∧
      ∀ t ∈ Icc 0 T, HasDerivAt α (galerkinNSField N ν (α t)) t :=
  galerkinNS_continuation_of_normBound ν x₀ hT (M * hsBoxConst N s)
    fun T' hT' α h0 hd t ht => (norm_le_hsNormField_mul s (α t)).trans
      (mul_le_mul_of_nonneg_right (hB T' hT' α h0 hd t ht) (hsBoxConst_nonneg N s))

end TorusFourierNS
