/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import TorusFourierNS.GalerkinEnergy
import TorusFourierNS.SobolevProduct

noncomputable section
open scoped BigOperators
open Complex

namespace TorusFourierNS

/-! ### Scalar and pointwise weight inequalities -/

/-- Mean-value bound for `x ↦ x^p`, `p ≥ 1`, via Bernoulli. -/
lemma rpow_sub_rpow_le_of_le {p x y : ℝ} (hp : 1 ≤ p) (hx : 0 < x) (hxy : x ≤ y) :
    y ^ p - x ^ p ≤ p * (y - x) * y ^ (p - 1) := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hb := one_add_mul_self_le_rpow_one_add (s := x / y - 1) (by
    have : 0 ≤ x / y := by positivity
    linarith) hp
  have h1 : (1 + (x / y - 1)) = x / y := by ring
  rw [h1, Real.div_rpow hx.le hy.le] at hb
  have hyp : 0 < y ^ p := Real.rpow_pos_of_pos hy p
  have hyp1 : y ^ p = y ^ (p - 1) * y := by
    rw [← Real.rpow_add_one hy.ne']; ring_nf
  have := mul_le_mul_of_nonneg_left hb hyp.le
  rw [mul_div_cancel₀ _ hyp.ne'] at this
  have e : y ^ p * (1 + p * (x / y - 1)) = y ^ p - p * (y - x) * y ^ (p - 1) := by
    rw [hyp1]; field_simp; ring
  linarith

lemma abs_rpow_sub_rpow_le {p x y M : ℝ} (hp : 1 ≤ p) (hx : 0 < x) (hy : 0 < y)
    (hxM : x ≤ M) (hyM : y ≤ M) :
    |y ^ p - x ^ p| ≤ p * |y - x| * M ^ (p - 1) := by
  rcases le_total x y with h | h
  · have := rpow_sub_rpow_le_of_le hp hx h
    have hm : y ^ (p - 1) ≤ M ^ (p - 1) := Real.rpow_le_rpow hy.le hyM (by linarith)
    rw [abs_of_nonneg (by linarith [Real.rpow_le_rpow hx.le h (by linarith : (0:ℝ) ≤ p)]),
      abs_of_nonneg (by linarith)]
    calc _ ≤ _ := this
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (mul_nonneg (by linarith) (by linarith))
  · have := rpow_sub_rpow_le_of_le hp hy h
    have hm : x ^ (p - 1) ≤ M ^ (p - 1) := Real.rpow_le_rpow hx.le hxM (by linarith)
    rw [abs_sub_comm, abs_sub_comm y x,
      abs_of_nonneg (by linarith [Real.rpow_le_rpow hy.le h (by linarith : (0:ℝ) ≤ p)]),
      abs_of_nonneg (by linarith)]
    calc _ ≤ _ := this
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (mul_nonneg (by linarith) (by linarith))

/-- Euclidean length `|x|` of a mode. -/
def nrm (x : Mode) : ℝ := Real.sqrt (nsq x)

/-- Japanese bracket `⟨x⟩ = (1+|x|²)^{1/2}`. -/
def br (x : Mode) : ℝ := Real.sqrt (1 + nsq x)

/-- Half weight `σ_s(x) = (1+|x|²)^{s/2} = √(sobW s x)`. -/
def sig (s : ℝ) (x : Mode) : ℝ := Real.sqrt (sobW s x)

lemma sobW_eq (s : ℝ) (x : Mode) : sobW s x = (1 + nsq x) ^ s := rfl

lemma sig_eq (s : ℝ) (x : Mode) : sig s x = (1 + nsq x) ^ (s / 2) := by
  unfold sig; rw [sobW_eq, Real.sqrt_eq_rpow, ← Real.rpow_mul (by have := nsq_nonneg x; linarith)]
  ring_nf

lemma sig_nonneg (s : ℝ) (x : Mode) : 0 ≤ sig s x := Real.sqrt_nonneg _
lemma br_nonneg (x : Mode) : 0 ≤ br x := Real.sqrt_nonneg _
lemma nrm_nonneg (x : Mode) : 0 ≤ nrm x := Real.sqrt_nonneg _

lemma nsq_neg (x : Mode) : nsq (-x) = nsq x := by simp [nsq]

lemma sig_neg (s : ℝ) (x : Mode) : sig s (-x) = sig s x := by simp only [sig_eq, nsq_neg]

lemma sig_sq (s : ℝ) (x : Mode) : sig s x ^ 2 = sobW s x := Real.sq_sqrt (sobW_pos s x).le

/-- Cauchy–Schwarz for modes: `|m·j| ≤ |m||j|`. -/
lemma abs_dotZ_le (m j : Mode) : |∑ l, (m l : ℝ) * (j l : ℝ)| ≤ nrm m * nrm j := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun l => (m l : ℝ)) (fun l => (j l : ℝ))
  rw [← Real.sqrt_sq_eq_abs, nrm, nrm, ← Real.sqrt_mul (nsq_nonneg m)]
  exact Real.sqrt_le_sqrt (by simpa [nsq] using h)

lemma nsq_add (m j : Mode) : nsq (m + j) = nsq m + 2 * ∑ l, (m l : ℝ) * (j l : ℝ) + nsq j := by
  simp only [nsq, Pi.add_apply, Int.cast_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr 1; funext l; ring

lemma nrm_sq (x : Mode) : nrm x ^ 2 = nsq x := Real.sq_sqrt (nsq_nonneg x)
lemma br_sq (x : Mode) : br x ^ 2 = 1 + nsq x := Real.sq_sqrt (by have := nsq_nonneg x; linarith)

lemma nsq_add_le (m j : Mode) : nsq (m + j) ≤ 2 * nsq m + 2 * nsq j := by
  have h := abs_dotZ_le m j
  have := nrm_sq m; have := nrm_sq j
  rw [nsq_add]
  nlinarith [abs_le.1 h, sq_nonneg (nrm m - nrm j)]

/-- Constant in the pointwise commutator bound. -/
def kpConst (s : ℝ) : ℝ := 3 * (s / 2) * (4:ℝ) ^ (s / 2 - 1) + (4:ℝ) ^ (s / 2) + 1

/-- **Proved.** Pointwise Kato–Ponce-type weight bound (`s ≥ 2`):
`|j| · |σ(m+j) - σ(j)| ≤ K (⟨m⟩ σ(j) + σ(m) ⟨j⟩)`. -/
theorem weight_commutator_le {s : ℝ} (hs : 2 ≤ s) (m j : Mode) :
    nrm j * |sig s (m + j) - sig s j| ≤ kpConst s * (br m * sig s j + sig s m * br j) := by
  set p := s / 2 with hp
  have hp1 : 1 ≤ p := by rw [hp]; linarith
  have hm0 := nsq_nonneg m; have hj0 := nsq_nonneg j; have hk0 := nsq_nonneg (m + j)
  have hadd := nsq_add_le m j
  have hbm := br_nonneg m; have hbj := br_nonneg j
  have hsm := sig_nonneg s m; have hsj := sig_nonneg s j
  have hnj := nrm_nonneg j; have hnm := nrm_nonneg m
  have h4p : 0 ≤ (4:ℝ) ^ (p - 1) := by positivity
  have h4p' : 0 ≤ (4:ℝ) ^ p := by positivity
  rcases le_total (nsq m) (nsq j) with hmj | hjm
  · -- low-frequency `m`: mean value
    have hA : 1 + nsq (m + j) ≤ 4 * (1 + nsq j) := by linarith
    have hB : 1 + nsq j ≤ 4 * (1 + nsq j) := by linarith
    have hmv := abs_rpow_sub_rpow_le (p := p) hp1 (by linarith : (0:ℝ) < 1 + nsq j)
      (by linarith : (0:ℝ) < 1 + nsq (m + j)) hB hA
    rw [← sig_eq, ← sig_eq] at hmv
    have hdiff : |(1 + nsq (m + j)) - (1 + nsq j)| ≤ 3 * nrm m * nrm j := by
      have h := abs_dotZ_le m j
      have e : (1 + nsq (m + j)) - (1 + nsq j) = nsq m + 2 * ∑ l, (m l : ℝ) * (j l : ℝ) := by
        rw [nsq_add]; ring
      rw [e]
      have hmm : nsq m ≤ nrm m * nrm j := by
        have := Real.sqrt_le_sqrt hmj
        rw [← nrm_sq m]; unfold nrm at *; nlinarith [Real.sqrt_nonneg (nsq m)]
      calc _ ≤ |nsq m| + |2 * ∑ l, (m l : ℝ) * (j l : ℝ)| := abs_add_le _ _
        _ ≤ _ := by rw [abs_of_nonneg hm0, abs_mul, abs_two]; linarith
    have h4 : (4 * (1 + nsq j)) ^ (p - 1) = (4:ℝ) ^ (p - 1) * (1 + nsq j) ^ (p - 1) :=
      Real.mul_rpow (by norm_num) (by linarith)
    have hsj' : sig s j = (1 + nsq j) ^ (p - 1) * (1 + nsq j) := by
      rw [sig_eq, ← hp, ← Real.rpow_add_one (by linarith)]; ring_nf
    have hq : 0 ≤ (1 + nsq j) ^ (p - 1) := by positivity
    have hnj2 : nrm j * nrm j ≤ 1 + nsq j := by nlinarith [nrm_sq j]
    have hnm_br : nrm m ≤ br m := Real.sqrt_le_sqrt (by linarith)
    calc nrm j * |sig s (m + j) - sig s j|
        ≤ nrm j * (p * (3 * nrm m * nrm j) * ((4:ℝ) ^ (p - 1) * (1 + nsq j) ^ (p - 1))) := by
          rw [← h4]; gcongr
          calc _ ≤ _ := hmv
            _ ≤ _ := by gcongr
      _ = 3 * p * (4:ℝ) ^ (p - 1) * nrm m * ((nrm j * nrm j) * (1 + nsq j) ^ (p - 1)) := by ring
      _ ≤ 3 * p * (4:ℝ) ^ (p - 1) * br m * ((1 + nsq j) * (1 + nsq j) ^ (p - 1)) := by
          gcongr
      _ = 3 * p * (4:ℝ) ^ (p - 1) * (br m * sig s j) := by rw [hsj']; ring
      _ ≤ kpConst s * (br m * sig s j + sig s m * br j) := by
          unfold kpConst; rw [← hp]
          have h1 : 0 ≤ br m * sig s j := by positivity
          have h2 : 0 ≤ sig s m * br j := by positivity
          have hc : 0 ≤ 3 * p * (4:ℝ) ^ (p - 1) := by positivity
          nlinarith [mul_nonneg hc h2, mul_nonneg (add_nonneg h4p' zero_le_one) h1,
            mul_nonneg (add_nonneg h4p' zero_le_one) h2]
  · -- high-frequency `m`: crude bound
    have hk : sig s (m + j) ≤ (4:ℝ) ^ p * sig s m := by
      rw [sig_eq, sig_eq, ← hp, ← Real.mul_rpow (by norm_num) (by linarith)]
      exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    have hj : sig s j ≤ sig s m := by
      rw [sig_eq, sig_eq]; exact Real.rpow_le_rpow (by linarith) (by linarith) (by linarith)
    have hsk := sig_nonneg s (m + j)
    have hnb : nrm j ≤ br j := Real.sqrt_le_sqrt (by linarith)
    calc nrm j * |sig s (m + j) - sig s j| ≤ br j * (((4:ℝ) ^ p + 1) * sig s m) := by
          gcongr
          rw [abs_le]; constructor <;> nlinarith
      _ = ((4:ℝ) ^ p + 1) * (sig s m * br j) := by ring
      _ ≤ kpConst s * (br m * sig s j + sig s m * br j) := by
          unfold kpConst; rw [← hp]
          have : 0 ≤ br m * sig s j := by positivity
          have : 0 ≤ sig s m * br j := by positivity
          have : 0 ≤ 3 * p * (4:ℝ) ^ (p - 1) := by positivity
          nlinarith

/-! ### Finite Young inequality on the mode box -/

lemma sum_shift_sq_le (B : Finset Mode) (Y : Mode → ℝ) (hY : ∀ k ∉ B, Y k = 0) (m : Mode) :
    ∑ j ∈ B, Y (m + j) ^ 2 ≤ ∑ k ∈ B, Y k ^ 2 := by
  classical
  rw [← Finset.sum_image (f := fun k => Y k ^ 2) (g := fun j => m + j)
    (fun a _ b _ h => add_left_cancel h)]
  rw [← Finset.sum_filter_of_ne (p := fun k => k ∈ B) (fun k _ hk => by
    by_contra h; exact hk (by simp [hY k h]))]
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => (Finset.mem_filter.1 hk).2)
    (fun _ _ _ => sq_nonneg _)

/-- **Proved.** `∑_{m,j} X_m Y_{m+j} Z_j ≤ ‖X‖₁ ‖Y‖₂ ‖Z‖₂` on the box. -/
theorem young_box (B : Finset Mode) (X Y Z : Mode → ℝ) (hX : ∀ k, 0 ≤ X k)
    (hY : ∀ k ∉ B, Y k = 0) :
    ∑ m ∈ B, ∑ j ∈ B, X m * Y (m + j) * Z j ≤
      (∑ m ∈ B, X m) * Real.sqrt (∑ k ∈ B, Y k ^ 2) * Real.sqrt (∑ j ∈ B, Z j ^ 2) := by
  rw [mul_assoc, Finset.sum_mul]
  refine Finset.sum_le_sum fun m _ => ?_
  simp_rw [mul_assoc]; rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (hX m)
  refine (Real.sum_mul_le_sqrt_mul_sqrt B (fun j => Y (m + j)) Z).trans ?_
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (sum_shift_sq_le B Y hY m))
    (Real.sqrt_nonneg _)

theorem young_box' (B : Finset Mode) (X Y Z : Mode → ℝ) (hZ : ∀ k, 0 ≤ Z k)
    (hY : ∀ k ∉ B, Y k = 0) :
    ∑ m ∈ B, ∑ j ∈ B, X m * Y (m + j) * Z j ≤
      (∑ j ∈ B, Z j) * Real.sqrt (∑ k ∈ B, Y k ^ 2) * Real.sqrt (∑ m ∈ B, X m ^ 2) := by
  rw [Finset.sum_comm]
  have := young_box B Z Y X hZ hY
  refine le_of_eq_of_le ?_ this
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
  rw [add_comm]; ring

/-! ### The trilinear form and the transport cancellation -/

/-- Pairs `(m, j)` in the box with `m + j` in the box. -/
def triDom (B : Finset Mode) : Finset (Mode × Mode) :=
  (B ×ˢ B).filter (fun p => p.1 + p.2 ∈ B)

/-- Coined: `g(m+j,j) (u_m · j) ∑ᵢ conj(u_{m+j,i}) u_{j,i}`. -/
def triTerm (u : FField) (g : Mode → Mode → ℝ) (p : Mode × Mode) : ℂ :=
  (g (p.1 + p.2) p.2 : ℂ) * (∑ l, u p.1 l * ((p.2 l : ℤ) : ℂ)) *
    ∑ i, (starRingEnd ℂ) (u (p.1 + p.2) i) * u p.2 i

lemma modeBox_neg {N : ℕ} {k : Mode} (hk : k ∈ modeBox N) : -k ∈ modeBox N := by
  simp only [modeBox, Fintype.mem_piFinset, Finset.mem_Icc, Pi.neg_apply] at hk ⊢
  intro i; have := hk i; constructor <;> omega

/-- **Proved (transport cancellation).** For a Hermitian, divergence-free field the symmetric
weight `σ(m+j)σ(j)` kills the trilinear form exactly. -/
theorem triTerm_sym_cancel {N : ℕ} (s : ℝ) {u : FField} (hH : HermitianField u)
    (hD : DivergenceFree u) :
    ∑ p ∈ triDom (modeBox N), triTerm u (fun k j => sig s k * sig s j) p = 0 := by
  set B := modeBox N
  set F := triTerm u (fun k j => sig s k * sig s j)
  let τ : Mode × Mode → Mode × Mode := fun p => (p.1, -(p.1 + p.2))
  have hτ : ∀ p ∈ triDom B, τ p ∈ triDom B := by
    intro p hp
    simp only [triDom, Finset.mem_filter, Finset.mem_product] at hp ⊢
    refine ⟨⟨hp.1.1, modeBox_neg hp.2⟩, ?_⟩
    have : p.1 + -(p.1 + p.2) = -p.2 := by abel
    simp only [τ]; rw [this]; exact modeBox_neg hp.1.2
  have hττ : ∀ p, τ (τ p) = p := by
    intro p; simp only [τ]; ext <;> simp
  have hswap : ∑ p ∈ triDom B, F p = ∑ p ∈ triDom B, F (τ p) :=
    Finset.sum_nbij' τ τ hτ hτ (fun p _ => hττ p) (fun p _ => hττ p) (fun p _ => by rw [hττ])
  have hpair : ∀ p : Mode × Mode, F p + F (τ p) = 0 := by
    rintro ⟨m, j⟩
    simp only [F, τ, triTerm]
    have e1 : m + -(m + j) = -j := by abel
    rw [e1, sig_neg, sig_neg]
    have hc1 : ∀ i, (starRingEnd ℂ) (u (-j) i) = u j i := by
      intro i; rw [hH j i]; simp
    have hc2 : ∀ i, u (-(m + j)) i = (starRingEnd ℂ) (u (m + j) i) := fun i => hH (m + j) i
    simp only [hc1, hc2]
    have hdiv : (∑ l, u m l * ((j l : ℤ) : ℂ)) + ∑ l, u m l * (((-(m + j)) l : ℤ) : ℂ) = 0 := by
      have := hD m
      simp only [dot, kvec] at this
      rw [← Finset.sum_add_distrib]
      rw [← neg_eq_zero, ← this, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [Pi.neg_apply, Pi.add_apply]; push_cast; ring
    have hs : ∑ i, (starRingEnd ℂ) (u (m + j) i) * u j i =
        ∑ i, u j i * (starRingEnd ℂ) (u (m + j) i) :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [← hs]
    push_cast at hdiv ⊢
    linear_combination ((sig s (m + j) : ℂ) * (sig s j : ℂ)) *
      (∑ i, (starRingEnd ℂ) (u (m + j) i) * u j i) * hdiv
  have h2 : 2 * ∑ p ∈ triDom B, F p = 0 := by
    rw [two_mul]; nth_rewrite 2 [hswap]
    rw [← Finset.sum_add_distrib]; exact Finset.sum_eq_zero fun p _ => hpair p
  simpa using h2

/-! ### Rewriting the Galerkin transport pairing as the trilinear form -/

/-- Coined: the summand before reindexing, at `(k, m)`. -/
def preTerm (u : FField) (w : Mode → ℝ) (k m : Mode) : ℂ :=
  (w k : ℂ) * (∑ l, u m l * (((k - m) l : ℤ) : ℂ)) * ∑ i, (starRingEnd ℂ) (u k i) * u (k - m) i

lemma leray_pairing (k : Mode) (a G : Fin 3 → ℂ) (ha : dot (kvec k) a = 0) :
    ∑ i, lerayP k G i * (starRingEnd ℂ) (a i) = ∑ i, G i * (starRingEnd ℂ) (a i) := by
  have h0 : ∑ i, (kvec k i : ℂ) * (starRingEnd ℂ) (a i) = 0 := by
    have := congrArg (starRingEnd ℂ) ha
    simp only [dot, map_sum, map_mul, Complex.conj_ofReal, map_zero] at this
    exact this
  simp only [lerayP, sub_mul, Finset.sum_sub_distrib]
  have : ∑ i, dot (kvec k) G / (ksq (kvec k) : ℂ) * (kvec k i : ℂ) * (starRingEnd ℂ) (a i) =
      dot (kvec k) G / (ksq (kvec k) : ℂ) * ∑ i, (kvec k i : ℂ) * (starRingEnd ℂ) (a i) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, h0, mul_zero, sub_zero]

theorem transport_pairing_eq {N : ℕ} (s : ℝ) (v : GState N) (hD : DivergenceFree (extendG v)) :
    ∑ k : modeBox N, ∑ i, sobW s k.1 * (2 * inner ℝ (v k i) (-(nsBilin v v k i))) =
      -2 * (2 * Real.pi * I *
        ∑ k ∈ modeBox N, ∑ m ∈ modeBox N, preTerm (extendG v) (sobW s) k m).re := by
  set u := extendG v
  have step1 : ∀ k : modeBox N, ∑ i, sobW s k.1 * (2 * inner ℝ (v k i) (-(nsBilin v v k i))) =
      -2 * ((sobW s k.1 : ℂ) * ∑ i, gconv v v k.1 i * (starRingEnd ℂ) (v k i)).re := by
    intro k
    have hdk : dot (kvec k.1) (v k) = 0 := by
      have := hD k.1; change dot _ (extendG v k.1) = 0 at this; rwa [extendG_apply] at this
    have := leray_pairing k.1 (v k) (gconv v v k.1) hdk
    simp only [nsBilin, Complex.inner]
    rw [Complex.re_ofReal_mul, ← this, Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp; ring
  simp only [step1]
  rw [← Finset.sum_coe_sort (modeBox N)]
  rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  rw [← Finset.sum_coe_sort (modeBox N), Finset.mul_sum]
  simp only [gconv, preTerm, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  have hv : ∀ (q : modeBox N) j, v q j = u q.1 j := fun q j => by simp only [u, extendG_apply]
  rw [hv k i, hv m l]; ring

theorem preTerm_sum_eq {N : ℕ} (u : FField) (hu : ∀ k ∉ modeBox N, u k = 0) (w : Mode → ℝ) :
    ∑ k ∈ modeBox N, ∑ m ∈ modeBox N, preTerm u w k m =
      ∑ p ∈ triDom (modeBox N), triTerm u (fun k _ => w k) p := by
  classical
  set B := modeBox N
  rw [← Finset.sum_product' (f := fun k m => preTerm u w k m)]
  rw [← Finset.sum_filter_of_ne (p := fun q : Mode × Mode => q.1 - q.2 ∈ B)]
  · refine Finset.sum_nbij' (fun q => (q.2, q.1 - q.2)) (fun p => (p.1 + p.2, p.1)) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_product] at hq
      simp only [triDom, Finset.mem_filter, Finset.mem_product, add_sub_cancel]
      exact ⟨⟨hq.1.2, hq.2⟩, hq.1.1⟩
    · intro p hp
      simp only [triDom, Finset.mem_filter, Finset.mem_product] at hp
      simp only [Finset.mem_filter, Finset.mem_product, add_sub_cancel_left]
      exact ⟨⟨hp.2, hp.1.1⟩, hp.1.2⟩
    · intro q _; simp
    · intro p _; simp
    · intro q _
      simp only [preTerm, triTerm, add_sub_cancel]
  · intro q _ hq
    by_contra h
    apply hq
    simp [preTerm, hu _ h]

/-! ### The commutator estimate -/

/-- Coined: componentwise `ℓ¹` size `∑ₗ |u_{k,l}|` of a mode. -/
def aC (u : FField) (k : Mode) : ℝ := ∑ l, ‖u k l‖

lemma aC_nonneg (u : FField) (k : Mode) : 0 ≤ aC u k := Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma abs_mode_le_nrm (j : Mode) (l : Fin 3) : |((j l : ℤ) : ℝ)| ≤ nrm j :=
  Real.abs_le_sqrt (Finset.single_le_sum (f := fun l => ((j l : ℝ)) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ l))

lemma norm_udot_le (u : FField) (m j : Mode) :
    ‖∑ l, u m l * ((j l : ℤ) : ℂ)‖ ≤ aC u m * nrm j := by
  refine (norm_sum_le _ _).trans ?_
  rw [aC, Finset.sum_mul]
  refine Finset.sum_le_sum fun l _ => ?_
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have := abs_mode_le_nrm j l
  rw [Complex.norm_intCast]; exact this

lemma norm_uconj_le (u : FField) (k j : Mode) :
    ‖∑ i, (starRingEnd ℂ) (u k i) * u j i‖ ≤ aC u k * aC u j := by
  refine (norm_sum_le _ _).trans ?_
  rw [aC, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_mul, Complex.norm_conj]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact Finset.single_le_sum (f := fun i => ‖u j i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

/-- **Proved.** Pointwise bound on the commutator part of the trilinear form. -/
theorem norm_triTerm_sub_le {s : ℝ} (hs : 2 ≤ s) (u : FField) (p : Mode × Mode) :
    ‖triTerm u (fun k _ => sobW s k) p - triTerm u (fun k j => sig s k * sig s j) p‖ ≤
      kpConst s * ((br p.1 * aC u p.1) * (sig s (p.1 + p.2) * aC u (p.1 + p.2)) *
          (sig s p.2 * aC u p.2) +
        (sig s p.1 * aC u p.1) * (sig s (p.1 + p.2) * aC u (p.1 + p.2)) *
          (br p.2 * aC u p.2)) := by
  obtain ⟨m, j⟩ := p
  simp only
  have e : triTerm u (fun k _ => sobW s k) (m, j) - triTerm u (fun k j => sig s k * sig s j) (m, j)
      = ((sig s (m + j) * (sig s (m + j) - sig s j) : ℝ) : ℂ) * (∑ l, u m l * ((j l : ℤ) : ℂ)) *
          ∑ i, (starRingEnd ℂ) (u (m + j) i) * u j i := by
    simp only [triTerm]; rw [← sig_sq s (m + j)]; push_cast; ring
  rw [e, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (sig_nonneg s (m + j))]
  have hA := norm_udot_le u m j
  have hC := norm_uconj_le u (m + j) j
  have hW := weight_commutator_le hs m j
  have h1 := aC_nonneg u m; have h2 := aC_nonneg u (m + j); have h3 := aC_nonneg u j
  have hsk := sig_nonneg s (m + j)
  calc sig s (m + j) * |sig s (m + j) - sig s j| * ‖∑ l, u m l * ((j l : ℤ) : ℂ)‖ *
        ‖∑ i, (starRingEnd ℂ) (u (m + j) i) * u j i‖
      ≤ sig s (m + j) * |sig s (m + j) - sig s j| * (aC u m * nrm j) * (aC u (m + j) * aC u j) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hA (by positivity)) hC (norm_nonneg _)
          (mul_nonneg (by positivity) (mul_nonneg h1 (nrm_nonneg j)))
    _ = (nrm j * |sig s (m + j) - sig s j|) * (sig s (m + j) * aC u m * aC u (m + j) * aC u j) := by ring
    _ ≤ (kpConst s * (br m * sig s j + sig s m * br j)) * (sig s (m + j) * aC u m * aC u (m + j) * aC u j) := by
        gcongr
    _ = _ := by ring

/-- Coined: constant of the transport bound. -/
def transportConst (s : ℝ) : ℝ :=
  24 * Real.sqrt 3 * Real.pi * kpConst s * Real.sqrt (∑' k : Mode, sobW (-(s - 1)) k)

lemma br_eq (s : ℝ) (m : Mode) : br m = Real.sqrt (sobW (-(s - 1)) m) * sig s m := by
  rw [sig, ← Real.sqrt_mul (sobW_pos _ m).le, br]
  congr 1
  rw [sobW_eq, sobW_eq, ← Real.rpow_add (by have := nsq_nonneg m; linarith)]
  ring_nf; simp

lemma sq_sum_fin3_le (x : Fin 3 → ℝ) : (∑ i, x i) ^ 2 ≤ 3 * ∑ i, x i ^ 2 := by
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1:ℝ)) x
  simpa using this

lemma kpConst_nonneg {s : ℝ} (hs : 2 ≤ s) : 0 ≤ kpConst s := by
  unfold kpConst
  have : 0 ≤ s / 2 := by linarith
  positivity

/-- **Proved (Kato–Ponce commutator estimate with transport cancellation, `s > 5/2`).**
The static Galerkin transport bound holds with the explicit constant `transportConst s`.
Hypotheses as in `GalerkinTransportBound`: the truncated field is Hermitian and
divergence-free. -/
theorem galerkinTransportBound_of_gt {s : ℝ} (hs : 5 / 2 < s) :
    GalerkinTransportBound s (transportConst s) := by
  classical
  intro N v hH hD
  have hs2 : 2 ≤ s := by linarith
  set B := modeBox N
  set u := extendG v
  have hu : ∀ k ∉ B, u k = 0 := fun k hk => by
    have hk' : k ∉ modeBox N := hk
    funext i; simp [u, extendG, hk']
  have haC : ∀ k ∉ B, aC u k = 0 := fun k hk => by simp [aC, hu k hk]
  set h := hsNormField s u ^ 2 with hh
  have hh' : h = ∑ k ∈ B, ∑ i, sobW s k * ‖u k i‖ ^ 2 := by
    rw [hh, hsNormSq_extendG, ← Finset.sum_coe_sort B]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    simp [u, extendG_apply]
  have h0 : 0 ≤ h := sq_nonneg _
  -- ℓ² and ℓ¹ sizes
  set Y : Mode → ℝ := fun k => sig s k * aC u k
  set X : Mode → ℝ := fun k => br k * aC u k
  have hY0 : ∀ k ∉ B, Y k = 0 := fun k hk => by simp [Y, haC k hk]
  have hX0 : ∀ k, 0 ≤ X k := fun k => mul_nonneg (br_nonneg k) (aC_nonneg u k)
  have hY0' : ∀ k, 0 ≤ Y k := fun k => mul_nonneg (sig_nonneg s k) (aC_nonneg u k)
  have hY2 : ∑ k ∈ B, Y k ^ 2 ≤ 3 * h := by
    rw [hh', Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    simp only [Y, mul_pow, sig_sq, aC]
    have := sq_sum_fin3_le (fun i => ‖u k i‖)
    have hw := (sobW_pos s k).le
    rw [← Finset.mul_sum]
    nlinarith
  set S := ∑' k : Mode, sobW (-(s - 1)) k
  have hSsum : Summable fun k : Mode => sobW (-(s - 1)) k := summable_sobW_neg (by linarith)
  have hS0 : 0 ≤ S := tsum_nonneg fun k => (sobW_pos _ k).le
  have hX1 : ∑ k ∈ B, X k ≤ Real.sqrt S * Real.sqrt (3 * h) := by
    have e : ∀ k, X k = Real.sqrt (sobW (-(s - 1)) k) * Y k := fun k => by
      simp only [X, Y, br_eq s k]; ring
    simp only [e]
    refine (Real.sum_mul_le_sqrt_mul_sqrt B _ _).trans ?_
    gcongr
    · simp only [Real.sq_sqrt (sobW_pos _ _).le]
      exact hSsum.sum_le_tsum B (fun k _ => (sobW_pos _ k).le)
  set Ysq := Real.sqrt (∑ k ∈ B, Y k ^ 2)
  have hYsq : Ysq ≤ Real.sqrt (3 * h) := Real.sqrt_le_sqrt hY2
  have hYsq0 : 0 ≤ Ysq := Real.sqrt_nonneg _
  -- the trilinear form
  set T := ∑ p ∈ triDom B, triTerm u (fun k _ => sobW s k) p
  have hT : T = ∑ p ∈ triDom B,
      (triTerm u (fun k _ => sobW s k) p - triTerm u (fun k j => sig s k * sig s j) p) := by
    rw [Finset.sum_sub_distrib, triTerm_sym_cancel s hH hD, sub_zero]
  have hK := kpConst_nonneg hs2
  have hTb : ‖T‖ ≤ kpConst s * (2 * (Real.sqrt S * Real.sqrt (3 * h) * Real.sqrt (3 * h) *
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
        Real.sqrt S * Real.sqrt (3 * h) * Real.sqrt (3 * h) * Real.sqrt (3 * h) := by
      have := Real.sqrt_nonneg S; have := Real.sqrt_nonneg (3 * h)
      calc (∑ m ∈ B, X m) * Ysq * Ysq ≤ (Real.sqrt S * Real.sqrt (3 * h)) * Real.sqrt (3 * h) *
            Real.sqrt (3 * h) := by gcongr
        _ = _ := by ring
    have hb2 : (∑ m ∈ B, X m) * Ysq * Ysq ≤
        Real.sqrt S * Real.sqrt (3 * h) * Real.sqrt (3 * h) * Real.sqrt (3 * h) := hb1
    linarith
  -- the pairing
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
  have h32 : h ^ (3 / 2 : ℝ) = h * Real.sqrt h := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add' h0 (by norm_num), Real.rpow_one]
  rw [h32]
  have e3 : Real.sqrt (3 * h) * Real.sqrt (3 * h) * Real.sqrt (3 * h) =
      3 * Real.sqrt 3 * (h * Real.sqrt h) := by
    rw [Real.sqrt_mul (by norm_num)]
    have a := Real.mul_self_sqrt h0
    have b := Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 3)
    calc Real.sqrt 3 * Real.sqrt h * (Real.sqrt 3 * Real.sqrt h) * (Real.sqrt 3 * Real.sqrt h)
        = (Real.sqrt 3 * Real.sqrt 3) * Real.sqrt 3 * ((Real.sqrt h * Real.sqrt h) * Real.sqrt h) := by
          ring
      _ = _ := by rw [a, b]
  have : ‖T‖ ≤ kpConst s * (6 * Real.sqrt 3 * Real.sqrt S * (h * Real.sqrt h)) := by
    refine hTb.trans (le_of_eq ?_)
    have e4 : Real.sqrt S * Real.sqrt (3 * h) * Real.sqrt (3 * h) * Real.sqrt (3 * h) =
        Real.sqrt S * (3 * Real.sqrt 3 * (h * Real.sqrt h)) := by rw [← e3]; ring
    rw [e4]; ring
  unfold transportConst
  have := Real.pi_pos
  nlinarith

end TorusFourierNS

namespace TorusFourierNS

/-- **Proved (`ν ≥ 0`, `s > 5/2`).** The Galerkin `H^s` energy inequality, unconditionally. -/
theorem galerkinHsEnergyInequality_of_gt {ν s : ℝ} (hν : 0 ≤ ν) (hs : 5 / 2 < s) :
    GalerkinHsEnergyInequality ν s (transportConst s) :=
  galerkinHsEnergyInequality_of_transport hν (galerkinTransportBound_of_gt hs)

lemma transportConst_nonneg {s : ℝ} (hs : 2 ≤ s) : 0 ≤ transportConst s := by
  unfold transportConst
  have := kpConst_nonneg hs
  have := Real.pi_pos.le
  positivity

/-- **Proved (`ν ≥ 0`, `s > 5/2`).** Uniform-in-`N` `H^s` bound on the explicit time
`barrierTime (transportConst s) ‖a‖²` for Galerkin solutions that stay Hermitian and
divergence-free. -/
theorem galerkin_uniform_bound_of_gt {ν s : ℝ} (hν : 0 ≤ ν) (hs : 5 / 2 < s)
    {a : FField} (ha : MemHsField s a) {N : ℕ} {α : ℝ → GState N} {T : ℝ}
    (hT : T ≤ barrierTime (transportConst s) (hsNormField s a ^ 2))
    (h0 : α 0 = restrictG N a)
    (hα : ∀ t ∈ Set.Icc 0 T, HasDerivAt α (galerkinNSField N ν (α t)) t)
    (hstruct : ∀ t ∈ Set.Icc 0 T, HermitianField (extendG (α t)) ∧ DivergenceFree (extendG (α t))) :
    ∀ t ∈ Set.Icc 0 T, hsNormField s (extendG (α t)) ^ 2 ≤ hsNormField s a ^ 2 + 1 :=
  galerkin_uniform_bound_of_energy (transportConst_nonneg (by linarith))
    (galerkinHsEnergyInequality_of_gt hν hs) ha hT h0 hα hstruct

end TorusFourierNS
