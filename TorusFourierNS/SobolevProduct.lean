import Mathlib
import TorusFourierNS.SobolevField

/-!
# The `H^s` algebra (product) estimate on `T³`, `s > 3/2`

Proves `SobolevProductEstimate s` for every `s > 3/2`, with `fconv` the componentwise
Fourier convolution (Fourier side of the pointwise product of two fields).
Route: Peetre (`sobW_peetre`) → Young `ℓ² * ℓ¹ ⊂ ℓ²` (Cauchy–Schwarz + shift invariance,
done in `ℝ≥0∞`) → `ℓ¹ ⊂ H^s` by Cauchy–Schwarz and `∑ (1+|k|²)^{-s} < ∞`.

Coined names: `ennCS`, `young_l2_l1`, `young_l1_l2`, `summable_sobW_neg`, `hsConst`.
-/

noncomputable section
open scoped BigOperators ENNReal
open Filter Topology

namespace TorusFourierNS

lemma ennr_half_sq (a : ℝ≥0∞) : (a ^ (1/2 : ℝ)) ^ 2 = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

lemma ennCS_fin {ι : Type*} (s : Finset ι) (x y : ι → ℝ≥0∞) :
    (∑ i ∈ s, x i * y i)^2 ≤ (∑ i ∈ s, x i^2) * (∑ i ∈ s, y i^2) := by
  have h := ENNReal.inner_le_Lp_mul_Lq s x y (p := 2) (q := 2)
    (by exact Real.HolderConjugate.two_two)
  simp only [ENNReal.rpow_two] at h
  calc (∑ i ∈ s, x i * y i)^2
      ≤ ((∑ i ∈ s, x i ^ 2) ^ (1/2:ℝ) * (∑ i ∈ s, y i ^ 2) ^ (1/2:ℝ))^2 :=
        pow_le_pow_left₀ (zero_le _) h 2
    _ = _ := by rw [mul_pow, ennr_half_sq, ennr_half_sq]

/-- Cauchy–Schwarz for `ℝ≥0∞`-valued series. -/
lemma ennCS {ι : Type*} (x y : ι → ℝ≥0∞) :
    (∑' i, x i * y i)^2 ≤ (∑' i, x i^2) * (∑' i, y i^2) := by
  have ht := ((ENNReal.continuous_pow 2).tendsto _).comp
    (ENNReal.summable (f := fun i => x i * y i)).hasSum
  refine le_of_tendsto' ht (fun s => ?_)
  exact (ennCS_fin s x y).trans (mul_le_mul' (ENNReal.sum_le_tsum s) (ENNReal.sum_le_tsum s))

lemma ennr_add_sq_le (a b : ℝ≥0∞) : (a + b)^2 ≤ 2 * (a^2 + b^2) := by
  have := ennCS_fin (Finset.univ : Finset (Fin 2)) (fun _ => 1) ![a, b]
  simpa [Fin.sum_univ_two, one_add_one_eq_two] using this

/-- Young `ℓ² * ℓ¹ ⊂ ℓ²` on `ℤ³`. -/
theorem young_l2_l1 (F G : Mode → ℝ≥0∞) :
    ∑' k, (∑' j, F (k - j) * G j)^2 ≤ (∑' j, F j^2) * (∑' j, G j)^2 := by
  set h : Mode → ℝ≥0∞ := fun j => G j ^ (1/2 : ℝ)
  have hk : ∀ k, (∑' j, F (k - j) * G j)^2 ≤ (∑' j, F (k - j)^2 * G j) * ∑' j, G j := by
    intro k
    calc (∑' j, F (k - j) * G j)^2 = (∑' j, (F (k - j) * h j) * h j)^2 := by
          congr 2; funext j; rw [mul_assoc, ← sq, ennr_half_sq]
      _ ≤ (∑' j, (F (k - j) * h j)^2) * ∑' j, h j ^ 2 := ennCS _ _
      _ = _ := by
          congr 1
          · congr 1; funext j; rw [mul_pow, ennr_half_sq]
          · congr 1; funext j; rw [ennr_half_sq]
  calc ∑' k, (∑' j, F (k - j) * G j)^2
      ≤ ∑' k, (∑' j, F (k - j)^2 * G j) * ∑' j, G j := ENNReal.tsum_le_tsum hk
    _ = (∑' j, (∑' k, F (k - j)^2) * G j) * ∑' j, G j := by
          rw [ENNReal.tsum_mul_right, ENNReal.tsum_comm]
          congr 1; congr 1; funext j; rw [ENNReal.tsum_mul_right]
    _ = (∑' j, (∑' k, F k^2) * G j) * ∑' j, G j := by
          congr 1; congr 1; funext j; congr 1
          exact (Equiv.subRight j).tsum_eq (fun k => F k ^ 2)
    _ = _ := by rw [ENNReal.tsum_mul_left, sq, mul_assoc]

lemma tsum_conv_comm (F G : Mode → ℝ≥0∞) (k : Mode) :
    ∑' j, F (k - j) * G j = ∑' j, G (k - j) * F j := by
  rw [← (Equiv.subLeft k).tsum_eq]
  congr 1; funext j; simp [mul_comm]

/-- Young `ℓ¹ * ℓ² ⊂ ℓ²` on `ℤ³`. -/
theorem young_l1_l2 (F G : Mode → ℝ≥0∞) :
    ∑' k, (∑' j, F (k - j) * G j)^2 ≤ (∑' j, F j)^2 * (∑' j, G j^2) := by
  simp_rw [tsum_conv_comm F G]
  rw [mul_comm]; exact young_l2_l1 G F

/-! ### Weight summability for `s > 3/2` -/

lemma summable_one_add_sq_rpow' {r : ℝ} (hr : 1 / 2 < r) :
    Summable fun n : ℤ => (1 + (n : ℝ) ^ 2) ^ (-r) := by
  have h1 : Summable fun n : ℤ => |(n : ℝ)| ^ (-(2 * r)) := Real.summable_abs_int_rpow (by linarith)
  have h2 : Summable fun n : ℤ => if n = 0 then (1 : ℝ) else 0 :=
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  refine (h1.add h2).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  by_cases hn : n = 0
  · subst hn; simp
    positivity
  · simp only [hn, if_false, add_zero]
    have hpos : 0 < |(n : ℝ)| := abs_pos.2 (by exact_mod_cast hn)
    rw [show |(n : ℝ)| ^ (-(2 * r)) = (|(n : ℝ)| ^ (2 : ℝ)) ^ (-r) by
      rw [← Real.rpow_mul hpos.le]; ring_nf]
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
    rw [Real.rpow_two, sq_abs]; linarith

lemma sobW_neg_le_prod {s : ℝ} (hs : 0 ≤ s) (k : Mode) :
    sobW (-s) k ≤ ∏ i, (1 + ((k i : ℝ)) ^ 2) ^ (-(s / 3)) := by
  have hA := one_add_sq_pos k
  have hle : ∀ i, 1 + ((k i : ℝ)) ^ 2 ≤ 1 + ∑ i, ((k i : ℝ)) ^ 2 := fun i => by
    have := Finset.single_le_sum (f := fun j => ((k j : ℝ)) ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i)
    linarith
  rw [Real.finset_prod_rpow _ _ (fun i _ => by positivity)]
  have hprod : ∏ i, (1 + ((k i : ℝ)) ^ 2) ≤ (1 + ∑ i, ((k i : ℝ)) ^ 2) ^ (3 : ℕ) := by
    rw [Fin.prod_univ_three]
    have h0 := hle 0; have h1 := hle 1; have h2 := hle 2
    calc (1 + ((k 0 : ℝ)) ^ 2) * (1 + ((k 1 : ℝ)) ^ 2) * (1 + ((k 2 : ℝ)) ^ 2)
        ≤ (1 + ∑ i, ((k i : ℝ)) ^ 2) * (1 + ∑ i, ((k i : ℝ)) ^ 2) *
            (1 + ∑ i, ((k i : ℝ)) ^ 2) := by gcongr
      _ = _ := by ring
  have hp : 0 < ∏ i, (1 + ((k i : ℝ)) ^ 2) := Finset.prod_pos fun i _ => by positivity
  calc sobW (-s) k = ((1 + ∑ i, ((k i : ℝ)) ^ 2) ^ (3 : ℕ)) ^ (-(s / 3)) := by
        unfold sobW; rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]; norm_num; ring_nf
    _ ≤ (∏ i, (1 + ((k i : ℝ)) ^ 2)) ^ (-(s / 3)) :=
        Real.rpow_le_rpow_of_nonpos hp hprod (by linarith)

/-- `∑_{k ∈ ℤ³} (1+|k|²)^{-s} < ∞` for `s > 3/2`. -/
theorem summable_sobW_neg {s : ℝ} (hs : 3 / 2 < s) : Summable fun k : Mode => sobW (-s) k := by
  set g : ℤ → ℝ := fun n => (1 + (n : ℝ) ^ 2) ^ (-(s / 3))
  have hg : Summable g := summable_one_add_sq_rpow' (by linarith)
  have hg0 : ∀ n, 0 ≤ g n := fun n => by positivity
  let e : Mode ≃ ℤ × ℤ × ℤ :=
    { toFun := fun k => (k 0, k 1, k 2)
      invFun := fun p => ![p.1, p.2.1, p.2.2]
      left_inv := fun k => by funext i; fin_cases i <;> rfl
      right_inv := fun p => rfl }
  have hprod : Summable fun p : ℤ × ℤ × ℤ => g p.1 * (g p.2.1 * g p.2.2) :=
    hg.mul_of_nonneg (hg.mul_of_nonneg hg hg0 hg0) hg0
      (fun p => mul_nonneg (hg0 _) (hg0 _))
  have hP : Summable fun k : Mode => ∏ i, g (k i) := by
    have := (e.summable_iff).2 hprod
    refine this.congr fun k => ?_
    simp [e, Fin.prod_univ_three, mul_assoc]
  exact hP.of_nonneg_of_le (fun k => (sobW_pos _ k).le)
    fun k => sobW_neg_le_prod (by linarith) k

/-! ### Pointwise weight facts -/

lemma sqrt_sobW_peetre {s : ℝ} (hs : 0 ≤ s) (k j : Mode) :
    Real.sqrt (sobW s k) ≤
      (2:ℝ) ^ s * (Real.sqrt (sobW s (k - j)) + Real.sqrt (sobW s j)) := by
  have hP := sobW_peetre hs k j
  have ha := (sobW_pos s (k - j)).le
  have hb := (sobW_pos s j).le
  have h4 : (4:ℝ) ^ s = ((2:ℝ) ^ s) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num)]; norm_num
  have h2 : 0 ≤ (2:ℝ) ^ s := by positivity
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, hP.trans ?_⟩
  rw [h4, mul_pow]
  have sa := Real.sq_sqrt ha; have sb := Real.sq_sqrt hb
  have : sobW s (k - j) + sobW s j ≤ (Real.sqrt (sobW s (k - j)) + Real.sqrt (sobW s j)) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (sobW s (k - j)), Real.sqrt_nonneg (sobW s j)]
  exact mul_le_mul_of_nonneg_left this (by positivity)

lemma sqrt_sobW_neg_mul (s : ℝ) (k : Mode) :
    Real.sqrt (sobW (-s) k) * Real.sqrt (sobW s k) = 1 := by
  rw [← Real.sqrt_mul (sobW_pos _ k).le]
  unfold sobW
  rw [Real.rpow_neg (one_add_sq_pos k).le, inv_mul_cancel₀ (Real.rpow_pos_of_pos (one_add_sq_pos k) s).ne']
  simp

/-- `(√w_k · |x|)²` in `ℝ≥0∞`. -/
lemma wh_sq (s : ℝ) (k : Mode) (x : ℂ) :
    (ENNReal.ofReal (Real.sqrt (sobW s k)) * ‖x‖ₑ) ^ 2 = ENNReal.ofReal (sobW s k * ‖x‖ ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_pow
    (by positivity), mul_pow, Real.sq_sqrt (sobW_pos s k).le]

/-! ### The product estimate -/

/-- Constant in the product estimate. -/
def hsConst (s : ℝ) : ℝ := 2 * (2:ℝ) ^ s * Real.sqrt (∑' k : Mode, sobW (-s) k)

lemma hsNormSq_ennr {s : ℝ} {u : FField} (hu : MemHsField s u) :
    ∑' p : Mode × Fin 3, ENNReal.ofReal (sobW s p.1 * ‖u p.1 p.2‖ ^ 2) =
      ENNReal.ofReal (hsNormField s u ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun p => by have := (sobW_pos s p.1).le; positivity) hu,
    hsNormField, Real.sq_sqrt (tsum_nonneg fun p => by have := (sobW_pos s p.1).le; positivity)]

lemma comp_le_hsNormSq {s : ℝ} {u : FField} (hu : MemHsField s u) (i : Fin 3) :
    ∑' k, ENNReal.ofReal (sobW s k * ‖u k i‖ ^ 2) ≤ ENNReal.ofReal (hsNormField s u ^ 2) := by
  rw [← hsNormSq_ennr hu, ENNReal.tsum_prod (f := fun (k : Mode) (i : Fin 3) =>
    ENNReal.ofReal (sobW s k * ‖u k i‖ ^ 2))]
  exact ENNReal.tsum_le_tsum fun k =>
    ENNReal.le_tsum (f := fun i => ENNReal.ofReal (sobW s k * ‖u k i‖ ^ 2)) i

/-- `ℓ¹` bound: `(∑ₖ |ĝₖ|)² ≤ (∑ (1+|k|²)^{-s}) · ∑ (1+|k|²)^s |ĝₖ|²`. -/
lemma l1_le (s : ℝ) (G : Mode → ℂ) :
    (∑' k, ‖G k‖ₑ) ^ 2 ≤ (∑' k, ENNReal.ofReal (sobW (-s) k)) *
      ∑' k, ENNReal.ofReal (sobW s k * ‖G k‖ ^ 2) := by
  have := ennCS (fun k => ENNReal.ofReal (Real.sqrt (sobW (-s) k)))
    (fun k => ENNReal.ofReal (Real.sqrt (sobW s k)) * ‖G k‖ₑ)
  convert this using 2
  · congr 1; funext k
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), sqrt_sobW_neg_mul]; simp
  · congr 1; funext k
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (sobW_pos _ k).le]
  · congr 1; funext k; rw [wh_sq]

/-- Componentwise estimate in `ℝ≥0∞`. -/
lemma comp_product_bound {s : ℝ} (hs : 0 ≤ s) (f g : FField) (i : Fin 3) :
    ∑' k, ENNReal.ofReal (sobW s k * ‖fconv f g k i‖ ^ 2) ≤
      ENNReal.ofReal ((2:ℝ) ^ s) ^ 2 * 2 *
        (2 * ((∑' k, ENNReal.ofReal (sobW (-s) k)) *
          (∑' k, ENNReal.ofReal (sobW s k * ‖f k i‖ ^ 2)) *
          (∑' k, ENNReal.ofReal (sobW s k * ‖g k i‖ ^ 2)))) := by
  set W : Mode → ℝ≥0∞ := fun k => ENNReal.ofReal (Real.sqrt (sobW s k))
  set a : Mode → ℝ≥0∞ := fun k => ‖f k i‖ₑ
  set b : Mode → ℝ≥0∞ := fun k => ‖g k i‖ₑ
  set C := ENNReal.ofReal ((2:ℝ) ^ s)
  set K := ∑' k, ENNReal.ofReal (sobW (-s) k)
  set Sf := ∑' k, ENNReal.ofReal (sobW s k * ‖f k i‖ ^ 2)
  set Sg := ∑' k, ENNReal.ofReal (sobW s k * ‖g k i‖ ^ 2)
  set T1 : Mode → ℝ≥0∞ := fun k => ∑' j, (W (k - j) * a (k - j)) * b j
  set T2 : Mode → ℝ≥0∞ := fun k => ∑' j, a (k - j) * (W j * b j)
  have hpt : ∀ k, W k * ‖fconv f g k i‖ₑ ≤ C * (T1 k + T2 k) := by
    intro k
    calc W k * ‖fconv f g k i‖ₑ ≤ W k * ∑' j, a (k - j) * b j := by
          gcongr
          refine enorm_tsum_le_tsum_enorm.trans (le_of_eq ?_)
          congr 1; funext j; simp [a, b, enorm_mul]
      _ = ∑' j, W k * (a (k - j) * b j) := by rw [ENNReal.tsum_mul_left]
      _ ≤ ∑' j, C * ((W (k - j) * a (k - j)) * b j + a (k - j) * (W j * b j)) := by
          refine ENNReal.tsum_le_tsum fun j => ?_
          have hw : W k ≤ C * (W (k - j) + W j) := by
            simp only [W, C]
            rw [← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),
              ← ENNReal.ofReal_mul (by positivity)]
            exact ENNReal.ofReal_le_ofReal (sqrt_sobW_peetre hs k j)
          calc W k * (a (k - j) * b j) ≤ C * (W (k - j) + W j) * (a (k - j) * b j) := by gcongr
            _ = _ := by ring
      _ = C * (T1 k + T2 k) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
  have hWa : ∑' j, (W j * a j) ^ 2 = Sf := by
    congr 1; funext j; exact wh_sq s j _
  have hWb : ∑' j, (W j * b j) ^ 2 = Sg := by
    congr 1; funext j; exact wh_sq s j _
  have hT1 : ∑' k, T1 k ^ 2 ≤ Sf * (K * Sg) := by
    calc ∑' k, T1 k ^ 2 ≤ (∑' j, (W j * a j) ^ 2) * (∑' j, b j) ^ 2 :=
          young_l2_l1 (fun j => W j * a j) b
      _ ≤ Sf * (K * Sg) := by rw [hWa]; gcongr; exact l1_le s (fun k => g k i)
  have hT2 : ∑' k, T2 k ^ 2 ≤ (K * Sf) * Sg := by
    calc ∑' k, T2 k ^ 2 ≤ (∑' j, a j) ^ 2 * (∑' j, (W j * b j) ^ 2) :=
          young_l1_l2 a (fun j => W j * b j)
      _ ≤ (K * Sf) * Sg := by rw [hWb]; gcongr; exact l1_le s (fun k => f k i)
  calc ∑' k, ENNReal.ofReal (sobW s k * ‖fconv f g k i‖ ^ 2)
      = ∑' k, (W k * ‖fconv f g k i‖ₑ) ^ 2 := by congr 1; funext k; rw [wh_sq]
    _ ≤ ∑' k, C ^ 2 * (2 * (T1 k ^ 2 + T2 k ^ 2)) := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        calc (W k * ‖fconv f g k i‖ₑ) ^ 2 ≤ (C * (T1 k + T2 k)) ^ 2 := pow_le_pow_left₀ (zero_le _) (hpt k) 2
          _ ≤ C ^ 2 * (2 * (T1 k ^ 2 + T2 k ^ 2)) := by
              rw [mul_pow]; gcongr; exact ennr_add_sq_le _ _
    _ = C ^ 2 * 2 * (∑' k, T1 k ^ 2 + ∑' k, T2 k ^ 2) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_add, mul_assoc]
    _ ≤ C ^ 2 * 2 * (Sf * (K * Sg) + (K * Sf) * Sg) := by gcongr
    _ = C ^ 2 * 2 * (2 * (K * Sf * Sg)) := by ring

/-- **`H^s` algebra property, `s > 3/2`** (proved):
`‖f ⋆ g‖_{H^s} ≤ hsConst s · ‖f‖_{H^s} ‖g‖_{H^s}` and `f ⋆ g ∈ H^s`. -/
theorem sobolevProductEstimate {s : ℝ} (hs : 3 / 2 < s) : SobolevProductEstimate s := by
  have hs0 : 0 ≤ s := by linarith
  have hK := summable_sobW_neg hs
  set Kr := ∑' k : Mode, sobW (-s) k
  have hKr : 0 ≤ Kr := tsum_nonneg fun k => (sobW_pos _ k).le
  have hKe : ∑' k, ENNReal.ofReal (sobW (-s) k) = ENNReal.ofReal Kr :=
    (ENNReal.ofReal_tsum_of_nonneg (fun k => (sobW_pos _ k).le) hK).symm
  refine ⟨hsConst s, by unfold hsConst; positivity, fun f g hf hg => ?_⟩
  set A := hsNormField s f; set B := hsNormField s g
  set R : ℝ := ((2:ℝ) ^ s) ^ 2 * 2 * (2 * (Kr * A ^ 2 * B ^ 2))
  have hR0 : 0 ≤ R := by positivity
  -- total bound in `ℝ≥0∞`
  have htot : ∑' p : Mode × Fin 3, ENNReal.ofReal (sobW s p.1 * ‖fconv f g p.1 p.2‖ ^ 2) ≤
      ENNReal.ofReal R := by
    rw [ENNReal.tsum_prod (f := fun (k : Mode) (i : Fin 3) =>
      ENNReal.ofReal (sobW s k * ‖fconv f g k i‖ ^ 2))]
    calc ∑' k, ∑' i, ENNReal.ofReal (sobW s k * ‖fconv f g k i‖ ^ 2)
        = ∑ i, ∑' k, ENNReal.ofReal (sobW s k * ‖fconv f g k i‖ ^ 2) := by
          rw [ENNReal.tsum_comm, tsum_fintype]
      _ ≤ ∑ i, ENNReal.ofReal ((2:ℝ) ^ s) ^ 2 * 2 * (2 * (ENNReal.ofReal Kr *
            (∑' k, ENNReal.ofReal (sobW s k * ‖f k i‖ ^ 2)) *
            (∑' k, ENNReal.ofReal (sobW s k * ‖g k i‖ ^ 2)))) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← hKe]; exact comp_product_bound hs0 f g i
      _ = ENNReal.ofReal ((2:ℝ) ^ s) ^ 2 * 2 * (2 * (ENNReal.ofReal Kr *
            ∑ i, (∑' k, ENNReal.ofReal (sobW s k * ‖f k i‖ ^ 2)) *
            (∑' k, ENNReal.ofReal (sobW s k * ‖g k i‖ ^ 2)))) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]; congr 2; rw [Finset.mul_sum]
          congr 1; funext i; ring
      _ ≤ ENNReal.ofReal ((2:ℝ) ^ s) ^ 2 * 2 * (2 * (ENNReal.ofReal Kr *
            (ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (B ^ 2)))) := by
          gcongr
          calc ∑ i, (∑' k, ENNReal.ofReal (sobW s k * ‖f k i‖ ^ 2)) *
                (∑' k, ENNReal.ofReal (sobW s k * ‖g k i‖ ^ 2))
              ≤ ∑ i, ENNReal.ofReal (A ^ 2) *
                (∑' k, ENNReal.ofReal (sobW s k * ‖g k i‖ ^ 2)) :=
                Finset.sum_le_sum fun i _ => by gcongr; exact comp_le_hsNormSq hf i
            _ = ENNReal.ofReal (A ^ 2) *
                ∑ i, ∑' k, ENNReal.ofReal (sobW s k * ‖g k i‖ ^ 2) := by rw [Finset.mul_sum]
            _ ≤ _ := by
                gcongr
                rw [← hsNormSq_ennr hg, ENNReal.tsum_prod (f := fun (k : Mode) (i : Fin 3) =>
                  ENNReal.ofReal (sobW s k * ‖g k i‖ ^ 2)), ENNReal.tsum_comm, tsum_fintype]
      _ = ENNReal.ofReal R := by
          simp only [R]
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul hKr,
            ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (2:ℝ) ^ s), ENNReal.ofReal_ofNat]
          ring
  have hnn : ∀ p : Mode × Fin 3, 0 ≤ sobW s p.1 * ‖fconv f g p.1 p.2‖ ^ 2 := fun p => by
    have := (sobW_pos s p.1).le; positivity
  have hsum : MemHsField s (fconv f g) := by
    have hne : ∑' p : Mode × Fin 3, ENNReal.ofReal (sobW s p.1 * ‖fconv f g p.1 p.2‖ ^ 2) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top htot
    exact ENNReal.summable_toReal hne |>.congr fun p => ENNReal.toReal_ofReal (hnn p)
  refine ⟨hsum, ?_⟩
  have hreal : hsNormField s (fconv f g) ^ 2 ≤ R := by
    have := htot
    rw [hsNormSq_ennr hsum] at this
    exact (ENNReal.ofReal_le_ofReal_iff hR0).1 this
  have hA := hsNormField_nonneg s f; have hB := hsNormField_nonneg s g
  have hrhs : R = (hsConst s * A * B) ^ 2 := by
    simp only [R, hsConst]
    rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hKr]; ring
  rw [hrhs] at hreal
  exact abs_le_of_sq_le_sq' hreal (by unfold hsConst; positivity) |>.2

end TorusFourierNS
