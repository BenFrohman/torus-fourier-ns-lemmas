/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import TorusFourierNS.Strain

/-!
# Gateaux derivative of the mode energy and the curl identity

On one Fourier mode `k`, the kinetic energy as a functional of vorticity is `modeEnergy k`.
We define the Gateaux representative of a functional on `ℂ³` against the real pairing
`Re ∑ᵢ conj(δᵢ) ηᵢ`, show the representative is unique (the pairing is nondegenerate),
define the functional derivative by choice exactly as an abstract encoding would, and prove:

* `modeFunctionalDerivative k (modeEnergy k) ω = streamSym k ω` (`δH/δω = ψ̂`);
* `curlSym k (modeFunctionalDerivative k (modeEnergy k) (curlSym k u)) = u` for a
  divergence-free mode with `k ≠ 0` (`curl(δH/δω) = u`, with no hypothesis on the derivative).
-/

noncomputable section

open Complex

namespace TorusFourierNS

/-- Real `L²`-type pairing on one mode. -/
def modePairing (δ η : Fin 3 → ℂ) : ℝ := ∑ i, ((starRingEnd ℂ) (δ i) * η i).re

/-- `δ` represents the Gateaux derivative of `F` at `ω`: for every direction `η`,
`d/dε |₀ F(ω + ε η) = modePairing δ η`. -/
def IsModeGateauxRep (F : (Fin 3 → ℂ) → ℝ) (ω δ : Fin 3 → ℂ) : Prop :=
  ∀ η : Fin 3 → ℂ, HasDerivAt (fun ε : ℝ => F (ω + ε • η)) (modePairing δ η) 0

open Classical in
/-- Functional derivative by choice: the Gateaux representative when one exists, else `0`. -/
def modeFunctionalDerivative (F : (Fin 3 → ℂ) → ℝ) (ω : Fin 3 → ℂ) : Fin 3 → ℂ :=
  if h : ∃ δ, IsModeGateauxRep F ω δ then Classical.choose h else 0

/-- The real pairing is nondegenerate, so Gateaux representatives are unique. -/
theorem modeGateauxRep_unique {F : (Fin 3 → ℂ) → ℝ} {ω δ δ' : Fin 3 → ℂ}
    (h : IsModeGateauxRep F ω δ) (h' : IsModeGateauxRep F ω δ') : δ = δ' := by
  have key : ∀ η, modePairing δ η = modePairing δ' η := fun η => (h η).unique (h' η)
  funext i
  have hre := key (Pi.single i 1)
  have him := key (Pi.single i I)
  have e1 : ∀ d : Fin 3 → ℂ, modePairing d (Pi.single i 1) = (d i).re := by
    intro d; simp [modePairing, Pi.single_apply, Fin.sum_univ_three]; fin_cases i <;> simp
  have e2 : ∀ d : Fin 3 → ℂ, modePairing d (Pi.single i I) = (d i).im := by
    intro d; simp [modePairing, Pi.single_apply, Fin.sum_univ_three]; fin_cases i <;> simp
  rw [e1, e1] at hre
  rw [e2, e2] at him
  exact Complex.ext hre him

/-- If `δ` is a Gateaux representative, the choice-based derivative equals `δ`. -/
theorem modeFunctionalDerivative_eq {F : (Fin 3 → ℂ) → ℝ} {ω δ : Fin 3 → ℂ}
    (h : IsModeGateauxRep F ω δ) : modeFunctionalDerivative F ω = δ := by
  have hex : ∃ d, IsModeGateauxRep F ω d := ⟨δ, h⟩
  rw [modeFunctionalDerivative, dif_pos hex]
  exact modeGateauxRep_unique (Classical.choose_spec hex) h

/-- The stream function `ψ̂ = streamSym k ω` is the Gateaux representative of `modeEnergy k`. -/
theorem streamSym_isModeGateauxRep (k : Fin 3 → ℝ) (ω : Fin 3 → ℂ) :
    IsModeGateauxRep (modeEnergy k) ω (streamSym k ω) := by
  intro η
  have hexp : (fun ε : ℝ => modeEnergy k (ω + ε • η)) = fun ε =>
      modeEnergy k ω + ε * modePairing (streamSym k ω) η + ε ^ 2 * modeEnergy k η := by
    funext ε; rw [modeEnergy_expand]; rfl
  rw [hexp]
  have h1 : HasDerivAt (fun ε : ℝ => ε * modePairing (streamSym k ω) η)
      (1 * modePairing (streamSym k ω) η) 0 := (hasDerivAt_id (0 : ℝ)).mul_const _
  have h2 : HasDerivAt (fun ε : ℝ => ε ^ 2 * modeEnergy k η)
      ((↑2 * (0 : ℝ) ^ (2 - 1)) * modeEnergy k η) 0 :=
    (hasDerivAt_pow 2 (0 : ℝ)).mul_const _
  have := ((hasDerivAt_const (0 : ℝ) (modeEnergy k ω)).add h1).add h2
  simpa using this

/-- **`δH/δω = ψ̂`** for the choice-based functional derivative. -/
theorem modeFunctionalDerivative_modeEnergy (k : Fin 3 → ℝ) (ω : Fin 3 → ℂ) :
    modeFunctionalDerivative (modeEnergy k) ω = streamSym k ω :=
  modeFunctionalDerivative_eq (streamSym_isModeGateauxRep k ω)

/-- **Curl identity, discharged at mode level.** For a divergence-free mode with `k ≠ 0`,
`curl(δH/δω) = u` where `δH/δω` is the choice-based Gateaux derivative at `ω̂ = curl û`. -/
theorem curl_modeFunctionalDerivative_eq_u (k : Fin 3 → ℝ) (u : Fin 3 → ℂ)
    (hk : ksq k ≠ 0) (hdiv : dot k u = 0) :
    curlSym k (modeFunctionalDerivative (modeEnergy k) (curlSym k u)) = u := by
  rw [modeFunctionalDerivative_modeEnergy]
  exact curl_stream_eq k u hk hdiv

end TorusFourierNS
