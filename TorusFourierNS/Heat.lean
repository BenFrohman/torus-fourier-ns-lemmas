/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import TorusFourierNS.Basic

/-!
# The heat semigroup on `L²(T³)` and Sobolev smoothing

`e^{tνΔ}` acts on the mode `n` by `e^{-ν|n|²t}` (Mathlib normalises `mFourier n x = e^{2πi n·x}`;
we absorb the factor `4π²` into `ν`). The `H^s` norm is `∑ₙ (1+|n|²)^s |f̂(n)|²`.
-/

noncomputable section

namespace TorusFourierNS

/-- Heat symbol `e^{-ν|n|²t}`. -/
def heatSymbol (ν t : ℝ) (n : Mode) : ℂ := (Real.exp (-(ν * nsq n * t)) : ℂ)

lemma norm_heatSymbol (ν t : ℝ) (n : Mode) : ‖heatSymbol ν t n‖ = Real.exp (-(ν * nsq n * t)) := by
  rw [heatSymbol, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

lemma norm_heatSymbol_le {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (n : Mode) : ‖heatSymbol ν t n‖ ≤ 1 := by
  rw [norm_heatSymbol, Real.exp_le_one_iff, neg_nonpos]
  have := nsq_nonneg n; positivity

/-- The heat semigroup `e^{tνΔ}` on `L²(T³)`, `ν, t ≥ 0`. -/
def heat {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (f : L2T3) : L2T3 :=
  multiplier (heatSymbol ν t) (norm_heatSymbol_le hν ht) f

lemma coeff_heat {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (f : L2T3) (n : Mode) :
    coeff (heat hν ht f) n = Real.exp (-(ν * nsq n * t)) * coeff f n := by
  simp [heat, heatSymbol]

/-- `e^{0·νΔ} = id`. -/
theorem heat_zero {ν : ℝ} (hν : 0 ≤ ν) (f : L2T3) : heat hν le_rfl f = f :=
  ext_coeff fun n => by simp [coeff_heat]

/-- **Semigroup law** `e^{sνΔ} e^{tνΔ} = e^{(s+t)νΔ}`. -/
theorem heat_add {ν s t : ℝ} (hν : 0 ≤ ν) (hs : 0 ≤ s) (ht : 0 ≤ t) (f : L2T3) :
    heat hν hs (heat hν ht f) = heat hν (add_nonneg hs ht) f := by
  refine ext_coeff fun n => ?_
  simp only [coeff_heat, ← mul_assoc]
  congr 1
  rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring

/-- **`L²` contraction** `‖e^{tνΔ} f‖₂ ≤ ‖f‖₂`. -/
theorem norm_heat_le {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 ≤ t) (f : L2T3) : ‖heat hν ht f‖ ≤ ‖f‖ :=
  norm_multiplier_le _ _ f

/-- Squared `H^s` norm `∑ₙ (1+|n|²)^s |f̂(n)|²` (meaningful when `InHs s f`). -/
def HsSq (s : ℝ) (f : L2T3) : ℝ := ∑' n, (1 + nsq n) ^ s * ‖coeff f n‖ ^ 2

/-- `f ∈ H^s(T³)`: the weighted coefficient series converges. -/
def InHs (s : ℝ) (f : L2T3) : Prop := Summable fun n => (1 + nsq n) ^ s * ‖coeff f n‖ ^ 2

/-- Every `L²` function lies in `H⁰`, and `HsSq 0 f = ‖f‖²`. -/
theorem inHs_zero (f : L2T3) : InHs 0 f := by simpa [InHs] using summable_coeff_sq f

theorem HsSq_zero (f : L2T3) : HsSq 0 f = ‖f‖ ^ 2 := by simp [HsSq, parseval_norm_sq]

/-- Elementary bound `(1+x)^k e^{-a x} ≤ k! e^a / a^k` for `x ≥ 0`, `a > 0`. -/
lemma one_add_pow_mul_exp_le (k : ℕ) {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    (1 + x) ^ k * Real.exp (-(a * x)) ≤ k.factorial * Real.exp a / a ^ k := by
  have h := Real.pow_div_factorial_le_exp (x := a * (1 + x)) (by positivity) k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hak : 0 < a ^ k := pow_pos ha k
  rw [div_le_iff₀ hk, mul_pow] at h
  rw [le_div_iff₀ hak]
  have he : Real.exp (-(a * x)) = Real.exp a * Real.exp (-(a * (1 + x))) := by
    rw [← Real.exp_add]; congr 1; ring
  have he2 : Real.exp (a * (1 + x)) * Real.exp (-(a * (1 + x))) = 1 := by
    rw [← Real.exp_add]; simp
  rw [he]
  have hpos : 0 < Real.exp (-(a * (1 + x))) := Real.exp_pos _
  calc (1 + x) ^ k * (Real.exp a * Real.exp (-(a * (1 + x)))) * a ^ k
      = Real.exp a * Real.exp (-(a * (1 + x))) * (a ^ k * (1 + x) ^ k) := by ring
    _ ≤ Real.exp a * Real.exp (-(a * (1 + x))) * (Real.exp (a * (1 + x)) * k.factorial) := by
        gcongr
    _ = k.factorial * Real.exp a := by
        rw [show Real.exp a * Real.exp (-(a * (1 + x))) * (Real.exp (a * (1 + x)) * k.factorial)
          = Real.exp a * k.factorial * (Real.exp (a * (1 + x)) * Real.exp (-(a * (1 + x)))) by ring,
          he2]; ring

/-- **Parabolic smoothing.** For `ν, t > 0`, `k ∈ ℕ` and `f ∈ H^s(T³)` (any real `s`; `s = 0` is
all of `L²`), `e^{tνΔ} f ∈ H^{s+k}` and
`‖e^{tνΔ} f‖²_{H^{s+k}} ≤ k! e^{2νt} (2νt)^{-k} ‖f‖²_{H^s}`. -/
theorem heat_smoothing {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (s : ℝ) (k : ℕ) (f : L2T3)
    (hf : InHs s f) :
    InHs (s + k) (heat hν.le ht.le f) ∧
      HsSq (s + k) (heat hν.le ht.le f) ≤
        k.factorial * Real.exp (2 * ν * t) / (2 * ν * t) ^ k * HsSq s f := by
  set K := (k.factorial : ℝ) * Real.exp (2 * ν * t) / (2 * ν * t) ^ k
  have ha : 0 < 2 * ν * t := by positivity
  have hpt : ∀ n, (1 + nsq n) ^ (s + k) * ‖coeff (heat hν.le ht.le f) n‖ ^ 2 ≤
      K * ((1 + nsq n) ^ s * ‖coeff f n‖ ^ 2) := by
    intro n
    have hx := nsq_nonneg n
    have h1 : 0 < 1 + nsq n := by linarith
    rw [coeff_heat, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.rpow_add h1, Real.rpow_natCast, mul_pow, ← Real.exp_nat_mul]
    have key := one_add_pow_mul_exp_le k ha hx
    have hexp : Real.exp (((2 : ℕ) : ℝ) * -(ν * nsq n * t)) = Real.exp (-(2 * ν * t * nsq n)) := by
      congr 1; push_cast; ring
    rw [hexp]
    have hs0 : 0 ≤ (1 + nsq n) ^ s := Real.rpow_nonneg h1.le _
    calc (1 + nsq n) ^ s * (1 + nsq n) ^ k * (Real.exp (-(2 * ν * t * nsq n)) * ‖coeff f n‖ ^ 2)
        = ((1 + nsq n) ^ k * Real.exp (-(2 * ν * t * nsq n))) * ((1 + nsq n) ^ s * ‖coeff f n‖ ^ 2)
          := by ring
      _ ≤ K * ((1 + nsq n) ^ s * ‖coeff f n‖ ^ 2) := by gcongr
  have hnn : ∀ n, 0 ≤ (1 + nsq n) ^ (s + k) * ‖coeff (heat hν.le ht.le f) n‖ ^ 2 := fun n => by
    have := nsq_nonneg n; positivity
  have hsum : InHs (s + k) (heat hν.le ht.le f) :=
    Summable.of_nonneg_of_le hnn hpt (hf.mul_left K)
  refine ⟨hsum, ?_⟩
  unfold HsSq
  rw [← tsum_mul_left]
  exact hsum.tsum_le_tsum hpt (hf.mul_left K)

/-- `y^k ≤ ⌈k⌉! e^y` for real `k ≥ 0`, `y ≥ 0`. -/
lemma rpow_le_factorial_ceil_mul_exp {k y : ℝ} (hk : 0 ≤ k) (hy : 0 ≤ y) :
    y ^ k ≤ (Nat.ceil k).factorial * Real.exp y := by
  have hf : (1 : ℝ) ≤ (Nat.ceil k).factorial := by exact_mod_cast (Nat.ceil k).factorial_pos
  have he : 1 ≤ Real.exp y := Real.one_le_exp hy
  rcases le_total y 1 with h | h
  · calc y ^ k ≤ 1 := Real.rpow_le_one hy h hk
      _ ≤ (Nat.ceil k).factorial * Real.exp y := by nlinarith
  · calc y ^ k ≤ y ^ ((Nat.ceil k : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le h (Nat.le_ceil k)
      _ = y ^ (Nat.ceil k) := Real.rpow_natCast y _
      _ ≤ (Nat.ceil k).factorial * Real.exp y := by
        have := Real.pow_div_factorial_le_exp (x := y) hy (Nat.ceil k)
        have hp : (0 : ℝ) < (Nat.ceil k).factorial := by exact_mod_cast (Nat.ceil k).factorial_pos
        rw [div_le_iff₀ hp] at this; linarith

/-- Real-exponent version of `one_add_pow_mul_exp_le`. -/
lemma one_add_rpow_mul_exp_le {k a x : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (hx : 0 ≤ x) :
    (1 + x) ^ k * Real.exp (-(a * x)) ≤ (Nat.ceil k).factorial * Real.exp a / a ^ k := by
  have h1 : 0 < 1 + x := by linarith
  have h := rpow_le_factorial_ceil_mul_exp hk (by positivity : 0 ≤ a * (1 + x))
  rw [Real.mul_rpow ha.le h1.le] at h
  have hak : 0 < a ^ k := Real.rpow_pos_of_pos ha k
  rw [le_div_iff₀ hak]
  have he : Real.exp (-(a * x)) = Real.exp a * Real.exp (-(a * (1 + x))) := by
    rw [← Real.exp_add]; congr 1; ring
  have he2 : Real.exp (a * (1 + x)) * Real.exp (-(a * (1 + x))) = 1 := by
    rw [← Real.exp_add]; simp
  rw [he]
  have hpos : 0 < Real.exp (-(a * (1 + x))) := Real.exp_pos _
  calc (1 + x) ^ k * (Real.exp a * Real.exp (-(a * (1 + x)))) * a ^ k
      = Real.exp a * Real.exp (-(a * (1 + x))) * (a ^ k * (1 + x) ^ k) := by ring
    _ ≤ Real.exp a * Real.exp (-(a * (1 + x))) *
          ((Nat.ceil k).factorial * Real.exp (a * (1 + x))) := by gcongr
    _ = (Nat.ceil k).factorial * Real.exp a := by
        rw [show Real.exp a * Real.exp (-(a * (1 + x))) *
            ((Nat.ceil k).factorial * Real.exp (a * (1 + x)))
          = Real.exp a * (Nat.ceil k).factorial *
            (Real.exp (a * (1 + x)) * Real.exp (-(a * (1 + x)))) by ring, he2]; ring

/-- **Parabolic smoothing, real gain.** For `ν, t > 0`, real `s`, real `k ≥ 0` and `f ∈ H^s`,
`e^{tνΔ} f ∈ H^{s+k}` and
`‖e^{tνΔ} f‖²_{H^{s+k}} ≤ ⌈k⌉! e^{2νt} (2νt)^{-k} ‖f‖²_{H^s}`. -/
theorem heat_smoothing_real {ν t : ℝ} (hν : 0 < ν) (ht : 0 < t) (s : ℝ) {k : ℝ} (hk : 0 ≤ k)
    (f : L2T3) (hf : InHs s f) :
    InHs (s + k) (heat hν.le ht.le f) ∧
      HsSq (s + k) (heat hν.le ht.le f) ≤
        (Nat.ceil k).factorial * Real.exp (2 * ν * t) / (2 * ν * t) ^ k * HsSq s f := by
  set K := ((Nat.ceil k).factorial : ℝ) * Real.exp (2 * ν * t) / (2 * ν * t) ^ k
  have ha : 0 < 2 * ν * t := by positivity
  have hpt : ∀ n, (1 + nsq n) ^ (s + k) * ‖coeff (heat hν.le ht.le f) n‖ ^ 2 ≤
      K * ((1 + nsq n) ^ s * ‖coeff f n‖ ^ 2) := by
    intro n
    have hx := nsq_nonneg n
    have h1 : 0 < 1 + nsq n := by linarith
    rw [coeff_heat, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Real.rpow_add h1, mul_pow, ← Real.exp_nat_mul]
    have key := one_add_rpow_mul_exp_le hk ha hx
    have hexp : Real.exp (((2 : ℕ) : ℝ) * -(ν * nsq n * t)) = Real.exp (-(2 * ν * t * nsq n)) := by
      congr 1; push_cast; ring
    rw [hexp]
    have hs0 : 0 ≤ (1 + nsq n) ^ s := Real.rpow_nonneg h1.le _
    calc (1 + nsq n) ^ s * (1 + nsq n) ^ k * (Real.exp (-(2 * ν * t * nsq n)) * ‖coeff f n‖ ^ 2)
        = ((1 + nsq n) ^ k * Real.exp (-(2 * ν * t * nsq n))) * ((1 + nsq n) ^ s * ‖coeff f n‖ ^ 2)
          := by ring
      _ ≤ K * ((1 + nsq n) ^ s * ‖coeff f n‖ ^ 2) := by gcongr
  have hnn : ∀ n, 0 ≤ (1 + nsq n) ^ (s + k) * ‖coeff (heat hν.le ht.le f) n‖ ^ 2 := fun n => by
    have := nsq_nonneg n; positivity
  have hsum : InHs (s + k) (heat hν.le ht.le f) :=
    Summable.of_nonneg_of_le hnn hpt (hf.mul_left K)
  refine ⟨hsum, ?_⟩
  unfold HsSq
  rw [← tsum_mul_left]
  exact hsum.tsum_le_tsum hpt (hf.mul_left K)

end TorusFourierNS
