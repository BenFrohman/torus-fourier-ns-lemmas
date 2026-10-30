/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import TorusFourierNS.Basic

/-!
# Strain, vorticity, stream function on `T³` in Fourier variables

With `mFourier n x = e^{2πi n·x}`, `∂ⱼ` acts on mode `n` by `2πi nⱼ`. For a velocity mode
`û ∈ ℂ³` at wave vector `k ∈ ℝ³`:
* strain `Ŝᵢⱼ = πi (kᵢ ûⱼ + kⱼ ûᵢ)`  (`S = ½(∇u + ∇uᵀ)`),
* vorticity `ω̂ = 2πi k × û`,
* stream function `ψ̂ = ω̂ / (4π²|k|²)`  (`-Δψ = ω`).
-/

noncomputable section

open Complex

namespace TorusFourierNS

/-- Cross product on `ℂ³` with a real first factor. -/
def cross (k : Fin 3 → ℝ) (u : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![(k 1 : ℂ) * u 2 - (k 2 : ℂ) * u 1, (k 2 : ℂ) * u 0 - (k 0 : ℂ) * u 2,
    (k 0 : ℂ) * u 1 - (k 1 : ℂ) * u 0]

def dot (k : Fin 3 → ℝ) (u : Fin 3 → ℂ) : ℂ := ∑ i, (k i : ℂ) * u i

def ksq (k : Fin 3 → ℝ) : ℝ := ∑ i, k i ^ 2

def strainSym (k : Fin 3 → ℝ) (u : Fin 3 → ℂ) (i j : Fin 3) : ℂ :=
  (Real.pi : ℂ) * I * ((k i : ℂ) * u j + (k j : ℂ) * u i)

def curlSym (k : Fin 3 → ℝ) (u : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  2 * (Real.pi : ℂ) * I * cross k u i

def streamSym (k : Fin 3 → ℝ) (ω : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  ω i / (4 * (Real.pi : ℂ) ^ 2 * (ksq k : ℂ))

lemma normsq_eq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-- **Pointwise strain–vorticity identity.** For a divergence-free mode (`k · û = 0`),
`∑ᵢⱼ |Ŝᵢⱼ|² = ½ ∑ᵢ |ω̂ᵢ|²`. -/
theorem strain_sq_eq_half_curl_sq (k : Fin 3 → ℝ) (u : Fin 3 → ℂ) (hdiv : dot k u = 0) :
    ∑ i, ∑ j, ‖strainSym k u i j‖ ^ 2 = (1 / 2) * ∑ i, ‖curlSym k u i‖ ^ 2 := by
  have hre : k 0 * (u 0).re + k 1 * (u 1).re + k 2 * (u 2).re = 0 := by
    have := congrArg Complex.re hdiv
    simpa [dot, Fin.sum_univ_three] using this
  have him : k 0 * (u 0).im + k 1 * (u 1).im + k 2 * (u 2).im = 0 := by
    have := congrArg Complex.im hdiv
    simpa [dot, Fin.sum_univ_three] using this
  simp only [Fin.sum_univ_three, normsq_eq, strainSym, curlSym, cross]
  simp [Complex.mul_re, Complex.mul_im]
  linear_combination (4 * Real.pi ^ 2 * (k 0 * (u 0).re + k 1 * (u 1).re + k 2 * (u 2).re)) * hre
    + (4 * Real.pi ^ 2 * (k 0 * (u 0).im + k 1 * (u 1).im + k 2 * (u 2).im)) * him

/-- Consequently `∑ᵢⱼ |Ŝᵢⱼ|² ≤ ∑ᵢ |ω̂ᵢ|²` mode by mode. -/
theorem strain_sq_le_curl_sq (k : Fin 3 → ℝ) (u : Fin 3 → ℂ) (hdiv : dot k u = 0) :
    ∑ i, ∑ j, ‖strainSym k u i j‖ ^ 2 ≤ ∑ i, ‖curlSym k u i‖ ^ 2 := by
  rw [strain_sq_eq_half_curl_sq k u hdiv]
  have : 0 ≤ ∑ i, ‖curlSym k u i‖ ^ 2 := by positivity
  linarith

/-- **Biot–Savart on one mode.** If `k ≠ 0` and `k · û = 0`, then the curl of the stream
function `ψ̂ = ω̂/(4π²|k|²)`, `ω̂ = curl û`, is `û`. -/
theorem curl_stream_eq (k : Fin 3 → ℝ) (u : Fin 3 → ℂ) (hk : ksq k ≠ 0) (hdiv : dot k u = 0) :
    curlSym k (streamSym k (curlSym k u)) = u := by
  have hk' : (ksq k : ℂ) ≠ 0 := by exact_mod_cast hk
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hks : (ksq k : ℂ) = (k 0 : ℂ) ^ 2 + (k 1 : ℂ) ^ 2 + (k 2 : ℂ) ^ 2 := by
    simp [ksq, Fin.sum_univ_three]
  have hd : (k 0 : ℂ) * u 0 + (k 1 : ℂ) * u 1 + (k 2 : ℂ) * u 2 = 0 := by
    simpa [dot, Fin.sum_univ_three] using hdiv
  funext i
  fin_cases i <;>
  · simp only [curlSym, streamSym, cross, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk]
    field_simp
    rw [hks] at *
    ring_nf
    rw [Complex.I_sq]
    first
      | linear_combination (-4 * (k 0 : ℂ)) * hd
      | linear_combination (-4 * (k 1 : ℂ)) * hd
      | linear_combination (-4 * (k 2 : ℂ)) * hd

/-- For a divergence-free mode, `|ω̂|² = 4π²|k|² |û|²`. -/
theorem curl_sq_eq (k : Fin 3 → ℝ) (u : Fin 3 → ℂ) (hdiv : dot k u = 0) :
    ∑ i, ‖curlSym k u i‖ ^ 2 = 4 * Real.pi ^ 2 * ksq k * ∑ i, ‖u i‖ ^ 2 := by
  have hre : k 0 * (u 0).re + k 1 * (u 1).re + k 2 * (u 2).re = 0 := by
    have := congrArg Complex.re hdiv
    simpa [dot, Fin.sum_univ_three] using this
  have him : k 0 * (u 0).im + k 1 * (u 1).im + k 2 * (u 2).im = 0 := by
    have := congrArg Complex.im hdiv
    simpa [dot, Fin.sum_univ_three] using this
  simp only [Fin.sum_univ_three, normsq_eq, curlSym, cross, ksq]
  simp [Complex.mul_re, Complex.mul_im]
  linear_combination (-4 * Real.pi ^ 2 * (k 0 * (u 0).re + k 1 * (u 1).re + k 2 * (u 2).re)) * hre
    + (-4 * Real.pi ^ 2 * (k 0 * (u 0).im + k 1 * (u 1).im + k 2 * (u 2).im)) * him

/-- Kinetic energy of one mode as a functional of vorticity:
`H(ω̂) = ½ G |ω̂|²`, `G = 1/(4π²|k|²)` (the Green's function of `-Δ`). -/
def modeEnergy (k : Fin 3 → ℝ) (ω : Fin 3 → ℂ) : ℝ :=
  (1 / 2) * (1 / (4 * Real.pi ^ 2 * ksq k)) * ∑ i, ‖ω i‖ ^ 2

/-- `H(curl û) = ½ |û|²` for a divergence-free mode with `k ≠ 0`: `modeEnergy` is the kinetic
energy. -/
theorem modeEnergy_curl (k : Fin 3 → ℝ) (u : Fin 3 → ℂ) (hk : ksq k ≠ 0) (hdiv : dot k u = 0) :
    modeEnergy k (curlSym k u) = (1 / 2) * ∑ i, ‖u i‖ ^ 2 := by
  rw [modeEnergy, curl_sq_eq k u hdiv]
  have : 4 * Real.pi ^ 2 * ksq k ≠ 0 := by
    have := Real.pi_ne_zero; positivity
  field_simp

/-- **Functional derivative `δH/δω = ψ`.** For every direction `η` and real `ε`,
`H(ω + εη) = H(ω) + ε Re⟨ψ̂, η⟩ + ε² H(η)`, where `ψ̂ = streamSym k ω`. So the Gateaux
derivative of `H` at `ω` is the real pairing against the stream function. -/
theorem modeEnergy_expand (k : Fin 3 → ℝ) (ω η : Fin 3 → ℂ) (ε : ℝ) :
    modeEnergy k (ω + ε • η) = modeEnergy k ω +
      ε * ∑ i, ((starRingEnd ℂ) (streamSym k ω i) * η i).re + ε ^ 2 * modeEnergy k η := by
  have hG : streamSym k ω = fun i => ((1 / (4 * Real.pi ^ 2 * ksq k) : ℝ) : ℂ) * ω i := by
    funext i; simp [streamSym, div_eq_mul_inv, mul_comm]
  rw [hG]
  simp only [modeEnergy, Fin.sum_univ_three, normsq_eq, Pi.add_apply, Pi.smul_apply,
    Complex.real_smul, map_mul, Complex.conj_ofReal]
  simp [Complex.mul_re, Complex.mul_im, ← Complex.ofReal_pow]
  have := Real.pi_ne_zero
  field_simp
  ring

/-- **Concrete curl identity** `curl(δH/δω) = u`: for a divergence-free mode with `k ≠ 0`, the
derivative `δH/δω` at `ω̂ = curl û` (namely `ψ̂`, `modeEnergy_expand`) has curl equal to `û`. -/
theorem curl_deltaH_eq_u (k : Fin 3 → ℝ) (u : Fin 3 → ℂ) (hk : ksq k ≠ 0) (hdiv : dot k u = 0) :
    curlSym k (streamSym k (curlSym k u)) = u :=
  curl_stream_eq k u hk hdiv

/-! ### `L²(T³)` form via Parseval -/

/-- Wave vector of a mode as a real vector. -/
def kvec (n : Mode) : Fin 3 → ℝ := fun i => (n i : ℝ)

/-- **`L²` strain bound on `T³`.** Let `u, ω, S` be `L²` fields on `T³` whose Fourier coefficients
are those of a divergence-free velocity, its vorticity `ω = curl u`, and its strain
`S = ½(∇u + ∇uᵀ)`. Then `∑ᵢⱼ ‖Sᵢⱼ‖₂² = ½ ∑ᵢ ‖ωᵢ‖₂²`, so `‖S‖₂ ≤ ‖ω‖₂`. -/
theorem L2_strain_eq (u ω : Fin 3 → L2T3) (S : Fin 3 → Fin 3 → L2T3)
    (hdiv : ∀ n, dot (kvec n) (fun j => coeff (u j) n) = 0)
    (hω : ∀ n i, coeff (ω i) n = curlSym (kvec n) (fun j => coeff (u j) n) i)
    (hS : ∀ n i j, coeff (S i j) n = strainSym (kvec n) (fun j => coeff (u j) n) i j) :
    ∑ i, ∑ j, ‖S i j‖ ^ 2 = (1 / 2) * ∑ i, ‖ω i‖ ^ 2 := by
  simp only [parseval_norm_sq]
  rw [← (Summable.tsum_finsetSum (fun i _ => summable_coeff_sq (ω i)))]
  have hsS : ∀ i, ∑ j, ∑' n, ‖coeff (S i j) n‖ ^ 2 = ∑' n, ∑ j, ‖coeff (S i j) n‖ ^ 2 :=
    fun i => (Summable.tsum_finsetSum (fun j _ => summable_coeff_sq (S i j))).symm
  simp only [hsS]
  rw [← (Summable.tsum_finsetSum (fun i _ => summable_sum fun j _ => summable_coeff_sq (S i j))),
    ← tsum_mul_left]
  congr 1; funext n
  simp only [hS, hω]
  exact strain_sq_eq_half_curl_sq _ _ (hdiv n)

theorem L2_strain_le (u ω : Fin 3 → L2T3) (S : Fin 3 → Fin 3 → L2T3)
    (hdiv : ∀ n, dot (kvec n) (fun j => coeff (u j) n) = 0)
    (hω : ∀ n i, coeff (ω i) n = curlSym (kvec n) (fun j => coeff (u j) n) i)
    (hS : ∀ n i j, coeff (S i j) n = strainSym (kvec n) (fun j => coeff (u j) n) i j) :
    ∑ i, ∑ j, ‖S i j‖ ^ 2 ≤ ∑ i, ‖ω i‖ ^ 2 := by
  rw [L2_strain_eq u ω S hdiv hω hS]
  have : 0 ≤ ∑ i, ‖ω i‖ ^ 2 := by positivity
  linarith

end TorusFourierNS
