/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import TorusFourierNS.TransportBound

/-!
# The Galerkin NS flow preserves Hermitian symmetry and `DivergenceFree` on `[0,T]`

**Proved:**
* `galerkinNSField_reflG`: the Galerkin field commutes with `reflG` (`v_k ↦ conj v_{-k}`).
* `galerkinNS_hermitian_Icc`: a solution on `[0,T]` from Hermitian data stays Hermitian
  (ODE uniqueness, the field is `C¹` hence Lipschitz on a ball containing both curves).
* `galerkinNS_divergenceFree_Icc`: a solution on `[0,T]` from divergence-free data stays
  divergence-free.
* `galerkinNS_structure_Icc`: both together.
* `hermitian_extendG_restrictG`, `divergenceFree_extendG_restrictG`: truncation keeps both.

Coined names: `negG`, `reflG`, `galerkinNSField_reflG`, `galerkinNS_hermitian_Icc`,
`galerkinNS_divergenceFree_Icc`, `galerkinNS_structure_Icc`, `ode_unique_Icc`,
`hermitian_extendG_restrictG`, `divergenceFree_extendG_restrictG`.
-/

noncomputable section
open Complex Set

namespace TorusFourierNS

variable {N : ℕ}

/-- Negation on the mode box (coined). -/
def negG (N : ℕ) : modeBox N ≃ modeBox N where
  toFun k := ⟨-k.1, modeBox_neg k.2⟩
  invFun k := ⟨-k.1, modeBox_neg k.2⟩
  left_inv k := by ext1; simp
  right_inv k := by ext1; simp

/-- Conjugate reflection `v_k ↦ conj v_{-k}` (coined). -/
def reflG (v : GState N) : GState N := fun k i => (starRingEnd ℂ) (v (negG N k) i)

lemma extendG_reflG (v : GState N) (k : Mode) (i : Fin 3) :
    extendG (reflG v) k i = (starRingEnd ℂ) (extendG v (-k) i) := by
  by_cases hk : k ∈ modeBox N
  · have hk' : -k ∈ modeBox N := modeBox_neg hk
    simp [extendG, hk, hk', reflG, negG]
  · have hk' : -k ∉ modeBox N := fun h => hk (by simpa using modeBox_neg h)
    simp [extendG, hk, hk']

lemma reflG_reflG (v : GState N) : reflG (reflG v) = v := by
  funext k i; simp [reflG, negG]

lemma hermitian_of_reflG {v : GState N} (h : reflG v = v) : HermitianField (extendG v) := by
  intro k i
  have := extendG_reflG v (-k) i
  rw [h, neg_neg] at this
  rw [this]

lemma reflG_of_hermitian {v : GState N} (h : HermitianField (extendG v)) : reflG v = v := by
  funext k i
  have := extendG_reflG v k.1 i
  rw [h, extendG_apply, extendG_apply] at this
  simpa using this

lemma kvec_neg (k : Mode) : kvec (-k) = -kvec k := by funext i; simp [kvec]

lemma ksq_kvec_neg (k : Mode) : ksq (kvec (-k)) = ksq (kvec k) := by
  simp [ksq, kvec_neg]

lemma ksq_neg' (x : Fin 3 → ℝ) : ksq (-x) = ksq x := by simp [ksq]

lemma lerayP_conj (k : Mode) (w : Fin 3 → ℂ) (i : Fin 3) :
    lerayP k (fun l => (starRingEnd ℂ) (w l)) i = (starRingEnd ℂ) (lerayP (-k) w i) := by
  simp only [lerayP, dot, kvec_neg, ksq_neg', Pi.neg_apply, map_sub, map_mul, map_div₀,
    map_sum, Complex.conj_ofReal]
  push_cast
  simp only [neg_mul, Finset.sum_neg_distrib]
  ring

lemma gconv_reflG (v : GState N) (k : Mode) (i : Fin 3) :
    gconv (reflG v) (reflG v) k i = (starRingEnd ℂ) (gconv v v (-k) i) := by
  simp only [gconv, extendG_reflG]
  rw [← (negG N).sum_comp]
  simp only [map_mul, map_sum, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [reflG, negG, Equiv.coe_fn_mk, neg_neg, Subtype.coe_eta]
  have e2 : -(k - -m.1) = -k - m.1 := by abel
  rw [e2]
  have e3 : ∀ l, (((k - -m.1) l : ℤ) : ℂ) = -(((-k - m.1) l : ℤ) : ℂ) := by
    intro l; simp; ring
  simp only [e3]
  simp only [mul_neg, Finset.sum_neg_distrib]
  ring

/-- **Proved.** The Galerkin NS field commutes with conjugate reflection. -/
theorem galerkinNSField_reflG (ν : ℝ) (v : GState N) :
    galerkinNSField N ν (reflG v) = reflG (galerkinNSField N ν v) := by
  funext k i
  rw [galerkinNSField_apply]
  simp only [reflG, galerkinNSField_apply]
  have hv : viscCoeff ν (negG N k).1 = viscCoeff ν k.1 := by
    simp [negG, viscCoeff, ksq_kvec_neg]
  have hb : nsBilin (reflG v) (reflG v) k i = (starRingEnd ℂ) (nsBilin v v (negG N k) i) := by
    simp only [nsBilin]
    rw [show gconv (reflG v) (reflG v) k.1 = fun l => (starRingEnd ℂ) (gconv v v (-k.1) l) from
      funext fun l => gconv_reflG v k.1 l, lerayP_conj]
    rfl
  rw [hb, hv]
  simp

lemma reflG_hasDerivAt {α : ℝ → GState N} {F : GState N} {t : ℝ} (h : HasDerivAt α F t) :
    HasDerivAt (fun s => reflG (α s)) (reflG F) t := by
  refine hasDerivAt_pi.2 fun k => hasDerivAt_pi.2 fun i => ?_
  have := hasDerivAt_pi.1 (hasDerivAt_pi.1 h (negG N k)) i
  exact this.star

lemma galerkinField_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) : ContDiff ℝ 1 (galerkinField A B) := by
  have hB : ContDiff ℝ 1 (fun u : E => B u u) :=
    B.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)
  exact A.contDiff.add hB

lemma galerkinNSField_contDiff (ν : ℝ) : ContDiff ℝ 1 (galerkinNSField N ν) :=
  galerkinField_contDiff _ _

/-- **Proved.** Uniqueness for the Galerkin NS system on `[0,T]` (coined). -/
theorem ode_unique_Icc (ν : ℝ) {f g : ℝ → GState N} {T : ℝ}
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f (galerkinNSField N ν (f t)) t)
    (hg : ∀ t ∈ Icc 0 T, HasDerivAt g (galerkinNSField N ν (g t)) t) (h0 : f 0 = g 0) :
    EqOn f g (Icc 0 T) := by
  have cf : ContinuousOn f (Icc 0 T) := fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have cg : ContinuousOn g (Icc 0 T) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  obtain ⟨Rf, hRf⟩ := isCompact_Icc.exists_bound_of_continuousOn cf
  obtain ⟨Rg, hRg⟩ := isCompact_Icc.exists_bound_of_continuousOn cg
  set R := max Rf Rg
  obtain ⟨K, hK⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : GState N) R)
    ((galerkinNSField_contDiff (N := N) ν).locallyLipschitz.locallyLipschitzOn)
  refine ODE_solution_unique_of_mem_Icc_right (v := fun _ => galerkinNSField N ν)
    (s := fun _ => Metric.closedBall 0 R) (fun _ _ => hK) cf
    (fun t ht => (hf t (Ico_subset_Icc_self ht)).hasDerivWithinAt) ?_ cg
    (fun t ht => (hg t (Ico_subset_Icc_self ht)).hasDerivWithinAt) ?_ h0
  · intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hRf t (Ico_subset_Icc_self ht)).trans (le_max_left _ _)
  · intro t ht
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hRg t (Ico_subset_Icc_self ht)).trans (le_max_right _ _)

/-- **Proved.** A Galerkin solution on `[0,T]` from Hermitian data stays Hermitian. -/
theorem galerkinNS_hermitian_Icc (ν : ℝ) {α : ℝ → GState N} {T : ℝ}
    (hα : ∀ t ∈ Icc 0 T, HasDerivAt α (galerkinNSField N ν (α t)) t)
    (h0 : HermitianField (extendG (α 0))) :
    ∀ t ∈ Icc 0 T, HermitianField (extendG (α t)) := by
  have hg : ∀ t ∈ Icc 0 T, HasDerivAt (fun s => reflG (α s))
      (galerkinNSField N ν (reflG (α t))) t := by
    intro t ht
    rw [galerkinNSField_reflG]
    exact reflG_hasDerivAt (hα t ht)
  have heq := ode_unique_Icc ν hα hg (reflG_of_hermitian h0).symm
  intro t ht
  exact hermitian_of_reflG (heq ht).symm

/-- **Proved.** A Galerkin solution on `[0,T]` from divergence-free data stays
divergence-free. -/
theorem galerkinNS_divergenceFree_Icc (ν : ℝ) {α : ℝ → GState N} {T : ℝ}
    (hα : ∀ t ∈ Icc 0 T, HasDerivAt α (galerkinNSField N ν (α t)) t)
    (h0 : DivergenceFree (extendG (α 0))) :
    ∀ t ∈ Icc 0 T, DivergenceFree (extendG (α t)) := by
  intro t ht k
  by_cases hk : k ∈ modeBox N
  swap
  · simp [extendG, hk, dot]
  set kk : modeBox N := ⟨k, hk⟩
  rw [show extendG (α t) k = α t kk from extendG_apply (α t) kk]
  set c := viscCoeff ν k
  set y : ℝ → ℂ := fun s => dot (kvec k) (α s kk)
  have hy : ∀ s ∈ Icc 0 T, HasDerivAt y ((-(c : ℂ)) • y s) s := by
    intro s hs
    have h1 := hasDerivAt_pi.1 (hasDerivAt_pi.1 (hα s hs) kk)
    have : HasDerivAt y (dot (kvec k) (galerkinNSField N ν (α s) kk)) s := by
      simp only [y, dot]
      exact HasDerivAt.fun_sum fun i _ => (h1 i).const_mul _
    exact this.congr_deriv (by rw [smul_eq_mul]; exact dot_galerkinNSField ν (α s) kk)
  have cy : ContinuousOn y (Icc 0 T) := fun s hs => (hy s hs).continuousAt.continuousWithinAt
  have hy0 : y 0 = 0 := by
    have := h0 k
    rwa [show extendG (α 0) k = α 0 kk from extendG_apply (α 0) kk] at this
  have := ODE_solution_unique_of_mem_Icc_right (v := fun _ (z : ℂ) => (-(c : ℂ)) • z)
    (s := fun _ => univ) (K := ‖(-(c : ℂ))‖₊)
    (fun _ _ => (lipschitzWith_smul _).lipschitzOnWith) cy
    (fun s hs => (hy s (Ico_subset_Icc_self hs)).hasDerivWithinAt) (fun _ _ => trivial)
    (continuousOn_const (c := (0 : ℂ)))
    (fun s _ => by simpa using (hasDerivWithinAt_const s (Ici s) (0 : ℂ)))
    (fun _ _ => trivial) hy0
  exact this ht

/-- **Proved.** Hermitian symmetry and `DivergenceFree` both persist on `[0,T]`. -/
theorem galerkinNS_structure_Icc (ν : ℝ) {α : ℝ → GState N} {T : ℝ}
    (hα : ∀ t ∈ Icc 0 T, HasDerivAt α (galerkinNSField N ν (α t)) t)
    (hH : HermitianField (extendG (α 0))) (hD : DivergenceFree (extendG (α 0))) :
    ∀ t ∈ Icc 0 T, HermitianField (extendG (α t)) ∧ DivergenceFree (extendG (α t)) :=
  fun t ht => ⟨galerkinNS_hermitian_Icc ν hα hH t ht, galerkinNS_divergenceFree_Icc ν hα hD t ht⟩

lemma hermitian_extendG_restrictG {a : FField} (h : HermitianField a) (N : ℕ) :
    HermitianField (extendG (restrictG N a)) := by
  intro k i
  by_cases hk : k ∈ modeBox N
  · have hk' : -k ∈ modeBox N := modeBox_neg hk
    simp [extendG, restrictG, hk, hk', h k i]
  · have hk' : -k ∉ modeBox N := fun h' => hk (by simpa using modeBox_neg h')
    simp [extendG, hk, hk']

lemma divergenceFree_extendG_restrictG {a : FField} (h : DivergenceFree a) (N : ℕ) :
    DivergenceFree (extendG (restrictG N a)) := by
  intro k
  by_cases hk : k ∈ modeBox N
  · have e : extendG (restrictG N a) k = a k := by funext i; simp [extendG, restrictG, hk]
    rw [e]; exact h k
  · simp [extendG, hk, dot]

end TorusFourierNS
