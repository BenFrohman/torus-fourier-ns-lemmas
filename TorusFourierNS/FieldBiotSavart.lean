/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import TorusFourierNS.GateauxBridge

/-!
# Biot–Savart, `δH/δω = ψ` and `curl(δH/δω) = u` for whole fields on `T³`

A vector field on `T³ = UnitAddTorus (Fin 3)` is described by its Fourier coefficients
`v : Mode → (Fin 3 → ℂ)`. The function space used throughout is the space of
**finite-kinetic-energy vorticities**

  `FinEnergy ω :⇔ ∑ₙ H_n(ω̂ₙ) < ∞`,  `H_n(ω̂) = |ω̂|² / (8π²|n|²)`  (`H_0 = 0`),

i.e. `ω ∈ Ḣ⁻¹(T³)`. Directions of variation range over the same space. On it:

* `fieldEnergy ω = ∑ₙ H_n(ω̂ₙ)` is the kinetic energy (`fieldEnergy_curl`:
  `fieldEnergy (curl u) = ½ ∑ₙ |ûₙ|²`, and `fieldEnergy_curl_L2`: `= ½ ∑ᵢ ‖uᵢ‖²_{L²(T³)}` for
  `uᵢ ∈ L²(T³)`, by Parseval), for every divergence-free, mean-zero `u` with `∑|ûₙ|² < ∞`;
* the Biot–Savart stream function is `ψ̂ₙ = ω̂ₙ/(4π²|n|²)` (`n ≠ 0`), `ψ̂₀ = 0`;
* `fieldEnergy_expand`: `H(ω+εη) = H(ω) + ε⟨ψ, η⟩ + ε² H(η)` (the integration by parts
  `½‖u‖² = ½⟨ω, ψ⟩`, in Fourier form);
* `fieldStream_isGateauxRep`, `fieldGateauxRep_unique`: `ψ` is a Gateaux representative of `H`
  and the only one;
* `streamFunctionRepresentative_T3`: there is `ψ` that is the unique representative and has
  `curl ψ = u`;
* `fieldCurl_functionalDerivative_eq`: `curl(δH/δω) = u` for the choice-based functional
  derivative, with no hypothesis on the derivative.
-/

noncomputable section

open Complex

namespace TorusFourierNS

/-- Fourier-side vector field on `T³`. -/
abbrev FField := Mode → Fin 3 → ℂ

/-- Mode energy at lattice mode `n`. -/
def modeE (n : Mode) (ω : Fin 3 → ℂ) : ℝ := modeEnergy (kvec n) ω

lemma modeEnergy_nonneg (k : Fin 3 → ℝ) (ω : Fin 3 → ℂ) : 0 ≤ modeEnergy k ω := by
  have : 0 ≤ ksq k := by unfold ksq; positivity
  unfold modeEnergy; positivity

/-- Finite kinetic energy: `ω ∈ Ḣ⁻¹(T³)`. -/
def FinEnergy (ω : FField) : Prop := Summable fun n => modeE n (ω n)

/-- Kinetic energy of a vorticity field, `H(ω) = ∑ₙ |ω̂ₙ|²/(8π²|n|²)`. -/
def fieldEnergy (ω : FField) : ℝ := ∑' n, modeE n (ω n)

/-- Real `L²` pairing `⟨δ, η⟩ = Re ∑ₙ ∑ᵢ conj(δ̂ₙᵢ) η̂ₙᵢ`. -/
def fieldPairing (δ η : FField) : ℝ := ∑' n, modePairing (δ n) (η n)

/-- Biot–Savart stream function `ψ̂ₙ = ω̂ₙ/(4π²|n|²)` (`ψ̂₀ = 0` since `|0|² = 0`). -/
def fieldStream (ω : FField) : FField := fun n => streamSym (kvec n) (ω n)

/-- Curl, `(curl v)̂ₙ = 2πi n × v̂ₙ`. -/
def fieldCurl (v : FField) : FField := fun n => curlSym (kvec n) (v n)

/-- `δ` is a Gateaux representative of `F` at `ω` along all finite-energy directions. -/
def IsFieldGateauxRep (F : FField → ℝ) (ω δ : FField) : Prop :=
  ∀ η, FinEnergy η → HasDerivAt (fun ε : ℝ => F (ω + ε • η)) (fieldPairing δ η) 0

open Classical in
/-- Functional derivative by choice: the representative when one exists, else `0`. -/
def fieldFunctionalDerivative (F : FField → ℝ) (ω : FField) : FField :=
  if h : ∃ δ, IsFieldGateauxRep F ω δ then Classical.choose h else 0

/-! ### Energy expansion -/

lemma abs_pairing_le (n : Mode) (ω η : Fin 3 → ℂ) :
    |modePairing (streamSym (kvec n) ω) η| ≤ modeE n ω + modeE n η := by
  have h1 := modeEnergy_expand (kvec n) ω η 1
  have h2 := modeEnergy_expand (kvec n) ω η (-1)
  have a := modeEnergy_nonneg (kvec n) (ω + (1:ℝ) • η)
  have b := modeEnergy_nonneg (kvec n) (ω + (-1:ℝ) • η)
  have c := modeEnergy_nonneg (kvec n) ω
  have d := modeEnergy_nonneg (kvec n) η
  simp only [one_pow, neg_one_sq, one_mul, neg_one_mul, mul_one] at h1 h2
  unfold modeE
  change |∑ i, ((starRingEnd ℂ) (streamSym (kvec n) ω i) * η i).re| ≤ _
  rw [abs_le]; constructor <;> linarith

lemma summable_pairing {ω η : FField} (hω : FinEnergy ω) (hη : FinEnergy η) :
    Summable fun n => modePairing (fieldStream ω n) (η n) := by
  refine Summable.of_norm_bounded (hω.add hη) (fun n => ?_)
  rw [Real.norm_eq_abs]; exact abs_pairing_le n (ω n) (η n)

/-- **Energy expansion** (integration by parts in Fourier form): for finite-energy `ω, η`,
`H(ω+εη) = H(ω) + ε ⟨ψ, η⟩ + ε² H(η)` with `ψ = fieldStream ω`. -/
theorem fieldEnergy_expand {ω η : FField} (hω : FinEnergy ω) (hη : FinEnergy η) (ε : ℝ) :
    fieldEnergy (ω + ε • η) =
      fieldEnergy ω + ε * fieldPairing (fieldStream ω) η + ε ^ 2 * fieldEnergy η := by
  have hb := summable_pairing hω hη
  have hpt : (fun n => modeE n ((ω + ε • η) n)) = fun n =>
      (modeE n (ω n) + ε * modePairing (fieldStream ω n) (η n)) + ε ^ 2 * modeE n (η n) := by
    funext n
    exact modeEnergy_expand (kvec n) (ω n) (η n) ε
  unfold fieldEnergy fieldPairing
  rw [hpt, Summable.tsum_add (hω.add (hb.mul_left ε)) (hη.mul_left _),
    Summable.tsum_add hω (hb.mul_left ε), tsum_mul_left, tsum_mul_left]

lemma finEnergy_add_smul {ω η : FField} (hω : FinEnergy ω) (hη : FinEnergy η) (ε : ℝ) :
    FinEnergy (ω + ε • η) := by
  have hb := summable_pairing hω hη
  have hpt : (fun n => modeE n ((ω + ε • η) n)) = fun n =>
      (modeE n (ω n) + ε * modePairing (fieldStream ω n) (η n)) + ε ^ 2 * modeE n (η n) := by
    funext n
    exact modeEnergy_expand (kvec n) (ω n) (η n) ε
  unfold FinEnergy; rw [hpt]
  exact (hω.add (hb.mul_left ε)).add (hη.mul_left _)

/-! ### `δH/δω = ψ`, existence and uniqueness -/

/-- The Biot–Savart stream function is a Gateaux representative of the kinetic energy. -/
theorem fieldStream_isGateauxRep {ω : FField} (hω : FinEnergy ω) :
    IsFieldGateauxRep fieldEnergy ω (fieldStream ω) := by
  intro η hη
  have hexp : (fun ε : ℝ => fieldEnergy (ω + ε • η)) = fun ε =>
      fieldEnergy ω + ε * fieldPairing (fieldStream ω) η + ε ^ 2 * fieldEnergy η := by
    funext ε; exact fieldEnergy_expand hω hη ε
  rw [hexp]
  have h1 : HasDerivAt (fun ε : ℝ => ε * fieldPairing (fieldStream ω) η)
      (1 * fieldPairing (fieldStream ω) η) 0 := (hasDerivAt_id (0 : ℝ)).mul_const _
  have h2 : HasDerivAt (fun ε : ℝ => ε ^ 2 * fieldEnergy η)
      ((↑2 * (0 : ℝ) ^ (2 - 1)) * fieldEnergy η) 0 :=
    (hasDerivAt_pow 2 (0 : ℝ)).mul_const _
  have := ((hasDerivAt_const (0 : ℝ) (fieldEnergy ω)).add h1).add h2
  simpa using this

/-- Single-mode, single-component direction. -/
def singleDir (n : Mode) (i : Fin 3) (z : ℂ) : FField := Pi.single n (Pi.single i z)

lemma finEnergy_singleDir (n : Mode) (i : Fin 3) (z : ℂ) : FinEnergy (singleDir n i z) := by
  unfold FinEnergy
  apply summable_of_ne_finset_zero (s := {n})
  intro m hm
  have : m ≠ n := by simpa using hm
  simp [singleDir, this, modeE, modeEnergy]

lemma fieldPairing_singleDir (δ : FField) (n : Mode) (i : Fin 3) (z : ℂ) :
    fieldPairing δ (singleDir n i z) = modePairing (δ n) (Pi.single i z) := by
  unfold fieldPairing
  rw [tsum_eq_single n]
  · simp [singleDir]
  · intro m hm
    simp [singleDir, hm, modePairing]

/-- Gateaux representatives along finite-energy directions are unique (no regularity or
summability is assumed on the candidates). -/
theorem fieldGateauxRep_unique {F : FField → ℝ} {ω δ δ' : FField}
    (h : IsFieldGateauxRep F ω δ) (h' : IsFieldGateauxRep F ω δ') : δ = δ' := by
  have key : ∀ η, FinEnergy η → fieldPairing δ η = fieldPairing δ' η :=
    fun η hη => (h η hη).unique (h' η hη)
  funext n i
  have hre := key _ (finEnergy_singleDir n i 1)
  have him := key _ (finEnergy_singleDir n i I)
  rw [fieldPairing_singleDir, fieldPairing_singleDir] at hre him
  have e1 : ∀ d : Fin 3 → ℂ, modePairing d (Pi.single i 1) = (d i).re := by
    intro d; simp [modePairing, Pi.single_apply, Fin.sum_univ_three]; fin_cases i <;> simp
  have e2 : ∀ d : Fin 3 → ℂ, modePairing d (Pi.single i I) = (d i).im := by
    intro d; simp [modePairing, Pi.single_apply, Fin.sum_univ_three]; fin_cases i <;> simp
  rw [e1, e1] at hre
  rw [e2, e2] at him
  exact Complex.ext hre him

theorem fieldFunctionalDerivative_eq {F : FField → ℝ} {ω δ : FField}
    (h : IsFieldGateauxRep F ω δ) : fieldFunctionalDerivative F ω = δ := by
  have hex : ∃ d, IsFieldGateauxRep F ω d := ⟨δ, h⟩
  rw [fieldFunctionalDerivative, dif_pos hex]
  exact fieldGateauxRep_unique (Classical.choose_spec hex) h

/-- **`δH/δω = ψ`** on finite-energy vorticities. -/
theorem fieldFunctionalDerivative_energy {ω : FField} (hω : FinEnergy ω) :
    fieldFunctionalDerivative fieldEnergy ω = fieldStream ω :=
  fieldFunctionalDerivative_eq (fieldStream_isGateauxRep hω)

/-! ### Velocity fields: finite energy, curl identity -/

/-- Divergence-free, mean-zero velocity with `∑ₙ |ûₙ|² < ∞` (i.e. `u ∈ L²(T³)`). -/
structure IsL2DivFreeMeanZero (u : FField) : Prop where
  summable : Summable fun n => ∑ i, ‖u n i‖ ^ 2
  div_free : ∀ n, dot (kvec n) (u n) = 0
  mean_zero : u 0 = 0

lemma kvec_ksq_ne_zero {n : Mode} (hn : n ≠ 0) : ksq (kvec n) ≠ 0 := by
  intro h
  apply hn; funext i
  have hle : (kvec n i) ^ 2 ≤ ksq (kvec n) := by
    unfold ksq
    exact Finset.single_le_sum (f := fun j => kvec n j ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  have : (kvec n i) ^ 2 = 0 := le_antisymm (h ▸ hle) (sq_nonneg _)
  have : (n i : ℝ) = 0 := by simpa [kvec] using this
  exact_mod_cast this

lemma modeE_curl (u : FField) (hu : IsL2DivFreeMeanZero u) (n : Mode) :
    modeE n (fieldCurl u n) = (1 / 2) * ∑ i, ‖u n i‖ ^ 2 := by
  by_cases hn : n = 0
  · subst hn; simp [modeE, modeEnergy, hu.mean_zero, fieldCurl, curlSym, cross, ksq, kvec]
  · exact modeEnergy_curl _ _ (kvec_ksq_ne_zero hn) (hu.div_free n)

theorem finEnergy_curl {u : FField} (hu : IsL2DivFreeMeanZero u) : FinEnergy (fieldCurl u) := by
  unfold FinEnergy
  simp only [modeE_curl u hu]
  exact hu.summable.mul_left _

/-- `H(curl u) = ½ ∑ₙ |ûₙ|²`. -/
theorem fieldEnergy_curl {u : FField} (hu : IsL2DivFreeMeanZero u) :
    fieldEnergy (fieldCurl u) = (1 / 2) * ∑' n, ∑ i, ‖u n i‖ ^ 2 := by
  unfold fieldEnergy; simp only [modeE_curl u hu]; exact tsum_mul_left

/-- **Biot–Savart:** `curl ψ = u` where `ψ` is the stream function of `ω = curl u`. -/
theorem fieldCurl_stream_eq {u : FField} (hu : IsL2DivFreeMeanZero u) :
    fieldCurl (fieldStream (fieldCurl u)) = u := by
  funext n
  by_cases hn : n = 0
  · subst hn
    rw [hu.mean_zero]; funext i
    fin_cases i <;> simp [fieldCurl, curlSym, cross, kvec]
  · exact curl_stream_eq _ _ (kvec_ksq_ne_zero hn) (hu.div_free n)

/-- **Stream-function representative on `T³`.** For every divergence-free, mean-zero
`u ∈ L²(T³)` and `ω = curl u`, there is `ψ` that is a Gateaux representative of the kinetic
energy at `ω`, is the only one, and has `curl ψ = u`. -/
theorem streamFunctionRepresentative_T3 {u : FField} (hu : IsL2DivFreeMeanZero u) :
    ∃ ψ : FField, IsFieldGateauxRep fieldEnergy (fieldCurl u) ψ ∧
      (∀ d, IsFieldGateauxRep fieldEnergy (fieldCurl u) d → d = ψ) ∧
      fieldCurl ψ = u :=
  ⟨fieldStream (fieldCurl u), fieldStream_isGateauxRep (finEnergy_curl hu),
    fun _ hd => fieldGateauxRep_unique hd (fieldStream_isGateauxRep (finEnergy_curl hu)),
    fieldCurl_stream_eq hu⟩

/-- **Kinetic-energy curl identity on `T³`, unconditional:** `curl(δH/δω) = u` for the
choice-based functional derivative at `ω = curl u`, for every divergence-free, mean-zero
`u ∈ L²(T³)`. -/
theorem fieldCurl_functionalDerivative_eq {u : FField} (hu : IsL2DivFreeMeanZero u) :
    fieldCurl (fieldFunctionalDerivative fieldEnergy (fieldCurl u)) = u := by
  rw [fieldFunctionalDerivative_energy (finEnergy_curl hu)]
  exact fieldCurl_stream_eq hu

/-! ### `L²(T³)` form -/

/-- Fourier coefficients of a vector of `L²(T³)` functions. -/
def coeffField (u : Fin 3 → L2T3) : FField := fun n i => coeff (u i) n

lemma summable_coeffField (u : Fin 3 → L2T3) :
    Summable fun n => ∑ i, ‖coeffField u n i‖ ^ 2 :=
  summable_sum fun i _ => summable_coeff_sq (u i)

/-- For `u ∈ L²(T³)³` divergence-free with zero mean, `H(curl u) = ½ ∑ᵢ ‖uᵢ‖²_{L²}` and
`curl(δH/δω) = u` at `ω = curl u`. -/
theorem fieldEnergy_curl_L2 (u : Fin 3 → L2T3)
    (hdiv : ∀ n, dot (kvec n) (coeffField u n) = 0) (hmean : coeffField u 0 = 0) :
    fieldEnergy (fieldCurl (coeffField u)) = (1 / 2) * ∑ i, ‖u i‖ ^ 2 ∧
      fieldCurl (fieldFunctionalDerivative fieldEnergy (fieldCurl (coeffField u))) =
        coeffField u := by
  have hu : IsL2DivFreeMeanZero (coeffField u) := ⟨summable_coeffField u, hdiv, hmean⟩
  refine ⟨?_, fieldCurl_functionalDerivative_eq hu⟩
  rw [fieldEnergy_curl hu]
  congr 1
  simp only [parseval_norm_sq, coeffField]
  exact Summable.tsum_finsetSum (fun i _ => summable_coeff_sq (u i))

end TorusFourierNS
