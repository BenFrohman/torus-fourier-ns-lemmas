/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import TorusFourierNS.Heat

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/main.tex
PAPER_SECTION: Section "Sobolev smoothing", Theorem `heat_smoothing` (with the definitions it uses from Sections "Setting", "Heat semigroup" and "Sobolev smoothing")
PAPER_SHA256: 331ec5aebb67be9849456a23cddd209ce6a50b9b9e6b0731c97441ae40029447

Locked paper claim, quoted verbatim (the theorem, then the paper's definitions of its terms):

PAPER_QUOTE_BEGIN
\begin{theorem}[\texttt{heat\_smoothing}] For $\nu,t>0$, $s\in\mathbb R$, $k\in\mathbb N$, $f\in H^s$:
$e^{t\nu\Delta}f\in H^{s+k}$ and $\|e^{t\nu\Delta}f\|_{H^{s+k}}^2\le k!\,e^{2\nu t}(2\nu t)^{-k}\|f\|_{H^s}^2$.\end{theorem}
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
$\mathbb T^3$ carries normalised Haar measure; $e_n(x)=e^{2\pi i n\cdot x}$, $n\in\mathbb Z^3$, is a
Hilbert basis of $L^2(\mathbb T^3)$ (Mathlib's \texttt{mFourierBasis}), and
$\hat f(n)=\int f\,\overline{e_n}$.
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{theorem} For $\nu,s,t\ge0$: $\widehat{e^{t\nu\Delta}f}(n)=e^{-\nu|n|^2t}\hat f(n)$,
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
$\|f\|_{H^s}^2=\sum_n(1+|n|^2)^s|\hat f(n)|^2$.
PAPER_QUOTE_END

Reading of the paper's terms:
* `f ∈ L²(T³)` is an element of `Lp ℂ 2` for Haar measure on `UnitAddTorus (Fin 3)`;
  `f̂(n)` is `mFourierCoeff f n` (`∫ f · conj e_n`), `n ∈ ℤ³`, `|n|² = n₀² + n₁² + n₂²`;
* `e^{tνΔ}f` is the `L²` function whose coefficients are `e^{-ν|n|²t} f̂(n)`, as the paper's
  heat-semigroup theorem states (the paper absorbs the `4π²` of `e_n` into `ν`); the
  transcription quantifies over any `g` with these coefficients;
* `f ∈ H^s` means the series `∑ₙ (1+|n|²)^s |f̂(n)|²` converges, and `‖f‖²_{H^s}` is its sum;
* `(2νt)^{-k}` is `((2νt)^k)⁻¹`.

`formal_claim` is the statement of `TorusFourierNS.heat_smoothing`, phrased with the repository's
`heat`, `InHs`, `HsSq`, `coeff` and `nsq`. `paper_claim` uses only Mathlib's `mFourierCoeff`
and the formulas above. The correspondence identifies `g` with `heat f` by injectivity of the
Fourier coefficient map and unfolds the repository's definitions.

Scope: a Fourier-side smoothing estimate for the heat semigroup on `T³`. Nothing here proves
existence or regularity of Navier-Stokes solutions; the Clay Millennium problem remains open.
-/

namespace TruthGate

open TorusFourierNS UnitAddTorus

-- TRUTH-GATE LOCK BEGIN
/-- The repository's statement (`TorusFourierNS.heat_smoothing`). -/
def formal_claim : Prop :=
  ∀ (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) (s : ℝ) (k : ℕ) (f : L2T3), InHs s f →
    InHs (s + k) (heat hν.le ht.le f) ∧
      HsSq (s + k) (heat hν.le ht.le f) ≤
        k.factorial * Real.exp (2 * ν * t) / (2 * ν * t) ^ k * HsSq s f

/-- Paper Theorem `heat_smoothing`: for `ν, t > 0`, `s ∈ ℝ`, `k ∈ ℕ`, `f ∈ H^s`:
`e^{tνΔ}f ∈ H^{s+k}` and `‖e^{tνΔ}f‖²_{H^{s+k}} ≤ k! e^{2νt} (2νt)^{-k} ‖f‖²_{H^s}`. -/
def paper_claim : Prop :=
  ∀ (ν t : ℝ), 0 < ν → 0 < t → ∀ (s : ℝ) (k : ℕ)
    (f g : MeasureTheory.Lp ℂ 2
      (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus (Fin 3)))),
    (∀ n : Fin 3 → ℤ,
      mFourierCoeff g n = (Real.exp (-(ν * (∑ i, ((n i : ℝ)) ^ 2) * t)) : ℂ) * mFourierCoeff f n) →
    Summable (fun n : Fin 3 → ℤ => (1 + ∑ i, ((n i : ℝ)) ^ 2) ^ s * ‖mFourierCoeff f n‖ ^ 2) →
    Summable (fun n : Fin 3 → ℤ =>
        (1 + ∑ i, ((n i : ℝ)) ^ 2) ^ (s + k) * ‖mFourierCoeff g n‖ ^ 2) ∧
      ∑' n : Fin 3 → ℤ, (1 + ∑ i, ((n i : ℝ)) ^ 2) ^ (s + k) * ‖mFourierCoeff g n‖ ^ 2 ≤
        (k.factorial : ℝ) * Real.exp (2 * ν * t) * ((2 * ν * t) ^ k)⁻¹ *
          ∑' n : Fin 3 → ℤ, (1 + ∑ i, ((n i : ℝ)) ^ 2) ^ s * ‖mFourierCoeff f n‖ ^ 2

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  constructor
  · intro h ν t hν ht s k f g hg hf
    have hgeq : g = heat hν.le ht.le f := by
      apply mFourierBasis.repr.injective
      ext n
      change coeff g n = coeff (heat hν.le ht.le f) n
      rw [coeff_heat, coeff_eq_mFourierCoeff, coeff_eq_mFourierCoeff, hg n] <;> rfl
    subst hgeq
    have hf' : InHs s f := by
      simpa only [InHs, nsq, coeff_eq_mFourierCoeff] using hf
    obtain ⟨h1, h2⟩ := h ν t hν ht s k f hf'
    refine ⟨?_, ?_⟩
    · simpa only [InHs, nsq, coeff_eq_mFourierCoeff] using h1
    · simpa only [HsSq, nsq, coeff_eq_mFourierCoeff, div_eq_mul_inv] using h2
  · intro h ν t hν ht s k f hf
    have hf' : Summable (fun n : Fin 3 → ℤ =>
        (1 + ∑ i, ((n i : ℝ)) ^ 2) ^ s * ‖mFourierCoeff f n‖ ^ 2) := by
      simpa only [InHs, nsq, coeff_eq_mFourierCoeff] using hf
    have hg : ∀ n : Fin 3 → ℤ, mFourierCoeff (heat hν.le ht.le f) n =
        (Real.exp (-(ν * (∑ i, ((n i : ℝ)) ^ 2) * t)) : ℂ) * mFourierCoeff f n := by
      intro n
      rw [← coeff_eq_mFourierCoeff, ← coeff_eq_mFourierCoeff, coeff_heat] <;> rfl
    obtain ⟨h1, h2⟩ := h ν t hν ht s k f (heat hν.le ht.le f) hg hf'
    refine ⟨?_, ?_⟩
    · simpa only [InHs, nsq, coeff_eq_mFourierCoeff] using h1
    · simpa only [HsSq, nsq, coeff_eq_mFourierCoeff, div_eq_mul_inv] using h2
-- TRUTH-GATE LOCK END

/-- The repository's theorem proves `formal_claim`. -/
theorem formal_claim_holds : formal_claim := by
  intro ν t hν ht s k f hf
  exact heat_smoothing hν ht s k f hf

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

end TruthGate
