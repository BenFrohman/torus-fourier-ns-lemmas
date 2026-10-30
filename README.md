# torus-fourier-ns-lemmas

Lean 4 + Mathlib (`v4.30.0-rc1`) lemmas on the flat 3-torus `T³ = UnitAddTorus (Fin 3)`, the
product of three unit circles, built on Mathlib's multi-dimensional Fourier series
(`mFourier`, `mFourierCoeff`, `mFourierBasis`, Parseval). Every result below is kernel-checked with
0 `sorry` and depends only on `propext`, `Classical.choice`, `Quot.sound`
(`lake env lean AxiomAudit.lean`).

Conventions: `mFourier n x = e^{2πi n·x}`, so `∂ⱼ` acts on mode `n` by `2πi nⱼ`; `|n|² = n₀²+n₁²+n₂²`;
the measure is the normalised Haar measure; the heat symbol is written `e^{-ν|n|²t}` with the
factor `4π²` absorbed into `ν`.

## Proved

**Fourier setup** (`TorusFourierNS/Basic.lean`), unconditional:
- `parseval_norm_sq`: `‖f‖₂² = ∑ₙ |f̂(n)|²` for every `f ∈ L²(T³)`.
- `multiplier`, `norm_multiplier_le`: every Fourier multiplier with `|m(n)| ≤ 1` is a bounded
  operator on `L²(T³)` with norm at most 1.

**Heat semigroup** (`TorusFourierNS/Heat.lean`), for all `f ∈ L²(T³)` and `ν, s, t ≥ 0`:
- `coeff_heat`: `e^{tνΔ}` multiplies mode `n` by `e^{-ν|n|²t}`.
- `heat_zero`: `e^{0·νΔ} f = f`.
- `heat_add`: `e^{sνΔ} e^{tνΔ} f = e^{(s+t)νΔ} f`.
- `norm_heat_le`: `‖e^{tνΔ} f‖₂ ≤ ‖f‖₂`.

**Sobolev smoothing** (`TorusFourierNS/Heat.lean`). The squared `H^s` norm is
`HsSq s f = ∑ₙ (1+|n|²)^s |f̂(n)|²`, and `InHs s f` means that series converges.
- `inHs_zero`, `HsSq_zero`: every `L²` function is in `H⁰` and `HsSq 0 f = ‖f‖₂²`.
- `heat_smoothing`: for `ν, t > 0`, every real `s`, every `k ∈ ℕ` and every `f ∈ L²(T³)` with
  `f ∈ H^s`, `e^{tνΔ} f ∈ H^{s+k}` and
  `‖e^{tνΔ} f‖²_{H^{s+k}} ≤ k! · e^{2νt} · (2νt)^{-k} · ‖f‖²_{H^s}`.
  Taking `s = 0` covers all of `L²(T³)`. The constant `C = (k! e^{2νt})^{1/2} 2^{-k/2}` is bounded
  for `t` in any bounded interval, which gives `‖e^{tνΔ} f‖_{H^{s+k}} ≤ C (νt)^{-k/2} ‖f‖_{H^s}`.
- `heat_smoothing_real`: the same for every real `k ≥ 0`, with `k!` replaced by `⌈k⌉!`.

**Strain, vorticity, stream function** (`TorusFourierNS/Strain.lean`). For a wave vector `k ∈ ℝ³`
and velocity mode `û ∈ ℂ³` with `k·û = 0` (divergence free):
- `strain_sq_eq_half_curl_sq`: `∑ᵢⱼ |Ŝᵢⱼ|² = ½ ∑ᵢ |ω̂ᵢ|²`, where `Ŝᵢⱼ = πi(kᵢûⱼ + kⱼûᵢ)` and
  `ω̂ = 2πi k×û`.
- `curl_sq_eq`: `|ω̂|² = 4π²|k|²|û|²`.
- `curl_stream_eq` (also `k ≠ 0`): the stream function `ψ̂ = ω̂/(4π²|k|²)` satisfies `curl ψ̂ = û`
  (Biot–Savart on one mode).
- `modeEnergy_curl` (also `k ≠ 0`): the vorticity functional `H(ω̂) = |ω̂|²/(8π²|k|²)` equals the
  kinetic energy `½|û|²` at `ω̂ = curl û`.
- `modeEnergy_expand`: `H(ω+εη) = H(ω) + ε Re⟨ψ̂, η⟩ + ε² H(η)` for all `ω, η, ε`, so the
  functional derivative `δH/δω` is the stream function `ψ̂`.
- `curl_deltaH_eq_u` (also `k ≠ 0`): `curl(δH/δω) = u` on every divergence-free mode. These
  are per-mode identities, so they hold for every field mode by mode, including all trigonometric
  polynomials with zero mean.

**Gateaux derivative** (`TorusFourierNS/GateauxBridge.lean`):
- `IsModeGateauxRep F ω δ`: `d/dε|₀ F(ω+εη) = Re ∑ᵢ conj(δᵢ)ηᵢ` for every `η`.
  `modeFunctionalDerivative F ω` is the representative chosen by `Classical.choose` (else `0`).
- `modeGateauxRep_unique`: the representative is unique.
- `modeFunctionalDerivative_eq`: any representative equals the choice-based derivative.
- `modeFunctionalDerivative_modeEnergy`: `δH/δω = ψ̂`.
- `curl_modeFunctionalDerivative_eq_u` (`k ≠ 0`, `k·û = 0`): `curl(δH/δω) = û` for the
  choice-based derivative at `ω̂ = curl û`, with no hypothesis on the derivative.

**Whole-field Biot–Savart and the curl identity** (`TorusFourierNS/FieldBiotSavart.lean`),
unconditional. A field is given by its Fourier coefficients `v : ℤ³ → ℂ³`. Function space:
vorticities of finite kinetic energy, `FinEnergy ω :⇔ ∑ₙ |ω̂ₙ|²/(8π²|n|²) < ∞` (that is,
`ω ∈ Ḣ⁻¹(T³)`, the `n = 0` term being `0`); variations range over the same space. Velocities:
`DivergenceFreeL2MeanZero u` means `∑ₙ |ûₙ|² < ∞` (`u ∈ L²(T³)³`), `n·ûₙ = 0` for all `n`, and `û₀ = 0`.
- `fieldEnergy ω = ∑ₙ |ω̂ₙ|²/(8π²|n|²)`; `fieldStream ω`: `ψ̂ₙ = ω̂ₙ/(4π²|n|²)`, `ψ̂₀ = 0`;
  `fieldCurl v`: `(curl v)̂ₙ = 2πi n×v̂ₙ`.
- `fieldEnergy_expand`: for finite-energy `ω, η` and real `ε`,
  `H(ω+εη) = H(ω) + ε⟨ψ, η⟩ + ε²H(η)`, `⟨δ, η⟩ = Re ∑ₙ ∑ᵢ conj(δ̂ₙᵢ)η̂ₙᵢ` (all series converge).
- `fieldStream_isGateauxRep`: `ψ` is a Gateaux representative of `H` at `ω`.
- `fieldGateauxRep_unique`: any two representatives are equal (no condition on the candidates).
- `fieldFunctionalDerivative_energy`: the choice-based derivative `δH/δω` equals `ψ`.
- `fieldEnergy_curl`: `H(curl u) = ½ ∑ₙ |ûₙ|²` for `DivergenceFreeL2MeanZero u`.
- `fieldCurl_stream_eq`: `curl ψ = u` at `ω = curl u` (Biot–Savart).
- `streamFunctionRepresentative_T3`: for `DivergenceFreeL2MeanZero u` there is `ψ` that is the unique
  Gateaux representative of `H` at `curl u` and has `curl ψ = u`.
- `fieldCurl_functionalDerivative_eq`: `curl(δH/δω) = u` at `ω = curl u` for every
  `DivergenceFreeL2MeanZero u`.
- `fieldEnergy_curl_L2`: for `u : (L²(T³))³` whose coefficients are divergence free with zero
  mean, `H(curl u) = ½ ∑ᵢ ‖uᵢ‖²_{L²}` (Parseval) and `curl(δH/δω) = û`.

**`L²` strain bound** (`TorusFourierNS/Strain.lean`):
- `L2_strain_eq`, `L2_strain_le`: if `u, ω, S` are `L²(T³)` fields whose Fourier coefficients are
  those of a divergence-free velocity `u`, its vorticity `ω = curl u` and its strain
  `S = ½(∇u+∇uᵀ)`, then `∑ᵢⱼ ‖Sᵢⱼ‖₂² = ½ ∑ᵢ ‖ωᵢ‖₂²`, hence `‖S‖₂ ≤ ‖ω‖₂`. The hypotheses are the
  Fourier-side definitions of divergence-free, curl and strain; the result covers every
  velocity field whose vorticity and strain lie in `L²`.

### Vector `H^s` fields on T³ (`TorusFourierNS/SobolevField.lean`)

Proved (0 sorry, audit clean): `MemHsField`/`hsNormField` on `FField` via weights
`(1+|k|²)^s`; closure under `+`/`-`; **triangle inequality** (`hsNormField_add_le`);
**completeness** (`hsField_complete`, via `lp` completeness); coefficient bound and
coefficientwise convergence; **`DivergenceFree` is closed under `H^s` limits** and under
`+`, scalar `•`; Peetre weight inequality `sobW_peetre` (first step of the product
estimate); **Galerkin local existence** `galerkin_local_existence` for any linear+quadratic
ODE `u' = Au + B(u,u)` on a finite-dimensional space (Picard–Lindelöf).

## Not proved here
- `SobolevProductEstimate`, `SobolevCommutatorEstimate`, `GalerkinUniformHsBound`,
  `GalerkinCompactnessLimit` are **named Props, stated but not proved**. The concrete
  Leray-projected NS Galerkin bilinear form is not constructed; `galerkin_local_existence`
  is for an abstract `B`. Nothing here proves `PeriodicLocalExistence` or any Clay statement.

- `Lᵖ` strain bounds for `p ≠ 2` (these need Calderón–Zygmund theory, absent from Mathlib).
- Any statement about existence, uniqueness or regularity of Navier–Stokes solutions.

## Build

```
lake build
lake env lean AxiomAudit.lean
```

Copyright 2026 Benjamin Stanley Frohman (ORCID 0009-0006-7068-3718). Apache-2.0.
