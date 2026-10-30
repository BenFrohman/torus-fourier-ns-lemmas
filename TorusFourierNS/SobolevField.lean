import Mathlib
import TorusFourierNS.FieldBiotSavart

/-!
# Vector-valued `H^s` fields on `T³` (Fourier side)

Coined names (not from the user's original vocabulary): `sobW`, `MemHsField`,
`hsWeighted`, `hsNormField`, `hsLp`, `SobolevProductEstimate`,
`SobolevCommutatorEstimate`, `galerkinField`, `GalerkinUniformHsBound`,
`GalerkinCompactnessLimit`.  `FField`, `DivergenceFree` are the user's.

Proved: triangle inequality, completeness, closedness of `DivergenceFree` in `H^s`,
Peetre weight inequality, Galerkin (finite-dimensional, quadratic) local existence.
Stated only (named Props, NOT proved): product and commutator estimates, uniform
Galerkin bounds and the compactness passage to the limit.
-/

noncomputable section
open scoped BigOperators ENNReal
open Filter Topology

namespace TorusFourierNS

/-- Sobolev weight `(1+|k|²)^s`. -/
def sobW (s : ℝ) (k : Mode) : ℝ := (1 + ∑ i, ((k i : ℝ))^2) ^ s

lemma one_add_sq_pos (k : Mode) : 0 < 1 + ∑ i, ((k i : ℝ))^2 := by positivity

lemma sobW_pos (s : ℝ) (k : Mode) : 0 < sobW s k := Real.rpow_pos_of_pos (one_add_sq_pos k) s

/-- `u ∈ H^s`: `∑_{k,i} (1+|k|²)^s |û_k,i|² < ∞`. -/
def MemHsField (s : ℝ) (u : FField) : Prop :=
  Summable fun p : Mode × Fin 3 => sobW s p.1 * ‖u p.1 p.2‖ ^ 2

/-- The weighted ℓ² sequence `√w_k · û_k,i`. -/
def hsWeighted (s : ℝ) (u : FField) : Mode × Fin 3 → ℂ :=
  fun p => (Real.sqrt (sobW s p.1) : ℂ) * u p.1 p.2

/-- `H^s` norm. -/
def hsNormField (s : ℝ) (u : FField) : ℝ :=
  Real.sqrt (∑' p : Mode × Fin 3, sobW s p.1 * ‖u p.1 p.2‖ ^ 2)

lemma norm_hsWeighted_sq (s : ℝ) (u : FField) (p : Mode × Fin 3) :
    ‖hsWeighted s u p‖ ^ 2 = sobW s p.1 * ‖u p.1 p.2‖ ^ 2 := by
  simp only [hsWeighted, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs,
    Real.sq_sqrt (sobW_pos s p.1).le]

lemma hsWeighted_add (s : ℝ) (u v : FField) :
    hsWeighted s (u + v) = hsWeighted s u + hsWeighted s v := by
  funext p; simp [hsWeighted, mul_add]

lemma hsWeighted_sub (s : ℝ) (u v : FField) :
    hsWeighted s (u - v) = hsWeighted s u - hsWeighted s v := by
  funext p; simp [hsWeighted, mul_sub]

lemma hs_two_toReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num

lemma memHsField_iff (s : ℝ) (u : FField) :
    MemHsField s u ↔ Memℓp (hsWeighted s u) 2 := by
  rw [memℓp_gen_iff (by norm_num), hs_two_toReal]
  simp only [Real.rpow_two, norm_hsWeighted_sq]; rfl

/-- The `lp` element attached to an `H^s` field. -/
def hsLp (s : ℝ) (u : FField) (h : MemHsField s u) : lp (fun _ : Mode × Fin 3 => ℂ) 2 :=
  ⟨hsWeighted s u, (memHsField_iff s u).1 h⟩

lemma hsNormField_eq (s : ℝ) (u : FField) (h : MemHsField s u) :
    hsNormField s u = ‖hsLp s u h‖ := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (hsLp s u h)
  rw [hs_two_toReal] at this
  simp only [Real.rpow_two] at this
  have e : ∑' p, ‖(hsLp s u h) p‖ ^ 2 = ∑' p : Mode × Fin 3, sobW s p.1 * ‖u p.1 p.2‖ ^ 2 := by
    congr 1; funext p; exact norm_hsWeighted_sq s u p
  rw [hsNormField, ← e, ← this, Real.sqrt_sq (norm_nonneg _)]

lemma hsNormField_nonneg (s : ℝ) (u : FField) : 0 ≤ hsNormField s u := Real.sqrt_nonneg _

lemma MemHsField.add {s : ℝ} {u v : FField} (hu : MemHsField s u) (hv : MemHsField s v) :
    MemHsField s (u + v) := by
  rw [memHsField_iff, hsWeighted_add]
  exact ((memHsField_iff s u).1 hu).add ((memHsField_iff s v).1 hv)

lemma MemHsField.sub {s : ℝ} {u v : FField} (hu : MemHsField s u) (hv : MemHsField s v) :
    MemHsField s (u - v) := by
  rw [memHsField_iff, hsWeighted_sub]
  exact ((memHsField_iff s u).1 hu).sub ((memHsField_iff s v).1 hv)

/-- **Triangle inequality** in `H^s`. -/
theorem hsNormField_add_le {s : ℝ} {u v : FField} (hu : MemHsField s u) (hv : MemHsField s v) :
    hsNormField s (u + v) ≤ hsNormField s u + hsNormField s v := by
  rw [hsNormField_eq s _ (hu.add hv), hsNormField_eq s u hu, hsNormField_eq s v hv]
  have : hsLp s (u + v) (hu.add hv) = hsLp s u hu + hsLp s v hv := by
    ext p; simp [hsLp, hsWeighted_add]; rfl
  rw [this]; exact norm_add_le _ _

lemma hsNormField_sub_eq {s : ℝ} {u v : FField} (hu : MemHsField s u) (hv : MemHsField s v) :
    hsNormField s (u - v) = ‖hsLp s u hu - hsLp s v hv‖ := by
  rw [hsNormField_eq s _ (hu.sub hv)]
  congr 1; ext p; simp [hsLp, hsWeighted_sub]; rfl

/-- **Completeness** of `H^s`: every `H^s`-Cauchy sequence converges in `H^s`. -/
theorem hsField_complete {s : ℝ} (u : ℕ → FField) (hu : ∀ n, MemHsField s (u n))
    (hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, hsNormField s (u m - u n) < ε) :
    ∃ v, MemHsField s v ∧ Tendsto (fun n => hsNormField s (u n - v)) atTop (𝓝 0) := by
  have hcs : CauchySeq fun n => hsLp s (u n) (hu n) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hC ε hε
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm, ← hsNormField_sub_eq]; exact hN n hn N le_rfl
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
  let v : FField := fun k i => L (k, i) / (Real.sqrt (sobW s k) : ℂ)
  have hw : hsWeighted s v = L := by
    funext p
    have h0 : (Real.sqrt (sobW s p.1) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 (sobW_pos s p.1)).ne'
    simp [hsWeighted, v, mul_div_cancel₀ _ h0]
  have hv : MemHsField s v := by rw [memHsField_iff, hw]; exact L.2
  refine ⟨v, hv, ?_⟩
  have hLv : hsLp s v hv = L := by ext p; simp [hsLp, hw]
  have := (tendsto_iff_norm_sub_tendsto_zero.1 hL)
  refine this.congr (fun n => ?_)
  rw [hsNormField_sub_eq (hu n) hv, hLv]

/-- Coefficients are controlled by the `H^s` norm: `√w_k |û_k,i| ≤ ‖u‖_{H^s}`. -/
lemma coeff_le_hsNorm {s : ℝ} {u : FField} (hu : MemHsField s u) (k : Mode) (i : Fin 3) :
    Real.sqrt (sobW s k) * ‖u k i‖ ≤ hsNormField s u := by
  rw [hsNormField_eq s u hu]
  have := lp.norm_apply_le_norm (by norm_num) (hsLp s u hu) (k, i)
  simpa [hsLp, hsWeighted, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)] using this

/-- `H^s` convergence implies coefficientwise convergence. -/
lemma tendsto_coeff_of_hs {s : ℝ} {u : ℕ → FField} {v : FField} (hu : ∀ n, MemHsField s (u n))
    (hv : MemHsField s v) (h : Tendsto (fun n => hsNormField s (u n - v)) atTop (𝓝 0))
    (k : Mode) (i : Fin 3) : Tendsto (fun n => u n k i) atTop (𝓝 (v k i)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hpos := Real.sqrt_pos.2 (sobW_pos s k)
  have h2 : Tendsto (fun n => hsNormField s (u n - v) / Real.sqrt (sobW s k)) atTop (𝓝 0) := by
    simpa using h.div_const (Real.sqrt (sobW s k))
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) h2
  rw [le_div_iff₀ hpos, mul_comm]
  have := coeff_le_hsNorm ((hu n).sub hv) k i
  simpa using this

/-- `DivergenceFree` is closed under `H^s` limits. -/
theorem divergenceFree_of_hs_limit {s : ℝ} {u : ℕ → FField} {v : FField}
    (hu : ∀ n, MemHsField s (u n)) (hv : MemHsField s v)
    (hdf : ∀ n, DivergenceFree (u n))
    (h : Tendsto (fun n => hsNormField s (u n - v)) atTop (𝓝 0)) : DivergenceFree v := by
  intro k
  have ht : Tendsto (fun n => dot (kvec k) (u n k)) atTop (𝓝 (dot (kvec k) (v k))) := by
    unfold dot
    exact tendsto_finset_sum _ fun i _ =>
      (tendsto_coeff_of_hs hu hv h k i).const_mul _
  have h0 : (fun n => dot (kvec k) (u n k)) = fun _ => (0 : ℂ) := funext fun n => hdf n k
  rw [h0] at ht
  exact (tendsto_nhds_unique ht tendsto_const_nhds)

lemma DivergenceFree.add' {u v : FField} (hu : DivergenceFree u) (hv : DivergenceFree v) :
    DivergenceFree (u + v) := by
  intro k; have a := hu k; have b := hv k
  unfold dot at *; simp [mul_add, Finset.sum_add_distrib, a, b]

lemma DivergenceFree.smul' (c : ℂ) {u : FField} (hu : DivergenceFree u) :
    DivergenceFree (c • u) := by
  intro k; have a := hu k
  unfold dot at *
  simp only [Pi.smul_apply, smul_eq_mul]
  calc ∑ i, (kvec k i : ℂ) * (c * u k i) = c * ∑ i, (kvec k i : ℂ) * u k i := by
        rw [Finset.mul_sum]; congr 1; funext i; ring
    _ = 0 := by rw [a, mul_zero]

/-- Peetre-type weight inequality, the first step of the `H^s` product estimate:
`(1+|k|²)^s ≤ 4^s ((1+|k-j|²)^s + (1+|j|²)^s)` for `s ≥ 0`. -/
theorem sobW_peetre {s : ℝ} (hs : 0 ≤ s) (k j : Mode) :
    sobW s k ≤ 4 ^ s * (sobW s (k - j) + sobW s j) := by
  set a := 1 + ∑ i, (((k - j) i : ℤ) : ℝ) ^ 2
  set b := 1 + ∑ i, ((j i : ℝ)) ^ 2
  have ha : 0 < a := one_add_sq_pos _
  have hb : 0 < b := one_add_sq_pos _
  have key : 1 + ∑ i, ((k i : ℝ)) ^ 2 ≤ 4 * max a b := by
    have : 1 + ∑ i, ((k i : ℝ)) ^ 2 ≤ 2 * a + 2 * b := by
      simp only [a, b, Pi.sub_apply, Int.cast_sub, Fin.sum_univ_three]
      nlinarith [sq_nonneg ((k 0 : ℝ) - 2 * j 0), sq_nonneg ((k 1 : ℝ) - 2 * j 1),
        sq_nonneg ((k 2 : ℝ) - 2 * j 2)]
    have := le_max_left a b; have := le_max_right a b; linarith
  have hm : 0 < max a b := lt_max_of_lt_left ha
  calc sobW s k ≤ (4 * max a b) ^ s := Real.rpow_le_rpow (one_add_sq_pos k).le key hs
    _ = 4 ^ s * (max a b) ^ s := Real.mul_rpow (by norm_num) hm.le
    _ ≤ 4 ^ s * (sobW s (k - j) + sobW s j) := by
        gcongr
        rcases le_total a b with h | h
        · rw [max_eq_right h]; have := Real.rpow_nonneg ha.le s
          show b ^ s ≤ a ^ s + b ^ s; linarith
        · rw [max_eq_left h]; have := Real.rpow_nonneg hb.le s
          show a ^ s ≤ a ^ s + b ^ s; linarith

/-! ### Named sub-Props (stated, NOT proved) -/

/-- Fourier convolution (componentwise product of fields), as a `tsum`. -/
def fconv (f g : FField) : FField := fun k i => ∑' j : Mode, f (k - j) i * g j i

/-- **Algebra property** of `H^s`, `s > 3/2` (NOT proved here). -/
def SobolevProductEstimate (s : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : FField, MemHsField s f → MemHsField s g →
    MemHsField s (fconv f g) ∧ hsNormField s (fconv f g) ≤ C * hsNormField s f * hsNormField s g

/-- **Kato–Ponce type commutator estimate** in the transport form
`‖Λ^s (u·∇v) - u·∇Λ^s v‖_{L²} ≤ C ‖u‖_{H^s} ‖v‖_{H^s}` for `s > 5/2`, encoded via
an abstract transport operator `transport` (NOT proved here). -/
def SobolevCommutatorEstimate (s : ℝ) (transport : FField → FField → FField)
    (lam : ℝ → FField → FField) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : FField, MemHsField s u → MemHsField s v →
    hsNormField 0 (transport u (lam s v) - lam s (transport u v)) ≤
      C * hsNormField s u * hsNormField s v

/-! ### Galerkin local existence (proved, finite-dimensional) -/

/-- Galerkin vector field `u ↦ A u + B u u` on a finite-dimensional truncation space. -/
def galerkinField {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (u : E) : E := A u + B u u

/-- **Galerkin local existence**: any linear-plus-quadratic ODE (in particular a
Galerkin truncation of NS: `A` = viscous term, `B` = projected nonlinearity) on a
finite-dimensional real space has a local `C¹` solution from every initial datum. -/
theorem galerkin_local_existence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (A : E →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (u₀ : E) :
    ∃ α : ℝ → E, α 0 = u₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioo (0 - ε) (0 + ε), HasDerivAt α (galerkinField A B (α t)) t := by
  have hB : ContDiff ℝ 1 (fun u : E => B u u) :=
    B.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)
  have hF : ContDiff ℝ 1 (galerkinField A B) := A.contDiff.add hB
  exact hF.contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ 0

/-- Remaining gap 1 (NOT proved): uniform-in-truncation `H^s` bound on a common time. -/
def GalerkinUniformHsBound (s : ℝ) (uN : ℕ → ℝ → FField) : Prop :=
  ∃ T > (0 : ℝ), ∃ M : ℝ, ∀ N, ∀ t ∈ Set.Icc 0 T, MemHsField s (uN N t) ∧ hsNormField s (uN N t) ≤ M

/-- Remaining gap 2 (NOT proved): passage to the limit producing a solution, phrased
abstractly via a predicate `IsSolutionOn` supplied by the caller. -/
def GalerkinCompactnessLimit (s : ℝ) (uN : ℕ → ℝ → FField)
    (IsSolutionOn : ℝ → (ℝ → FField) → Prop) : Prop :=
  ∀ T > (0 : ℝ), (∀ N, ∀ t ∈ Set.Icc 0 T, MemHsField s (uN N t)) →
    ∃ u : ℝ → FField, IsSolutionOn T u

end TorusFourierNS
