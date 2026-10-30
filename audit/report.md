# titan-audit report: `torus-fourier-ns-lemmas`

**Verdict: PASS**

- Generated (UTC): 2026-10-30T10:46:31+00:00
- Tool: titan-audit 1.0.0 (Benjamin Stanley Frohman (ORCID: 0009-0006-7068-3718))
- Toolchain: `leanprover/lean4:v4.30.0-rc1`  Git HEAD: `c18f2e1d5d9f9832af3c6ab95c06600d5bbbff49`
- Tree SHA-256: `67d35205bc42829a52da474470c5f896476bb44245dd62c437335daa63f5e1b1` over 9 files

## Build

- Build skipped (`--no-build`); audit used existing .olean files.

## Axiom audit

- Modules: 4  Theorems: 47  Clean (only propext/Classical.choice/Quot.sound): 47
- Nonstandard: 0

| Module | Theorems | Nonstandard |
|---|---:|---:|
| `TorusFourierNS.Basic` | 11 | 0 |
| `TorusFourierNS.Heat` | 19 | 0 |
| `TorusFourierNS.Strain` | 17 | 0 |

## Source scan

Counts: none


### Vacuity heuristics (in build)

- none

Heuristics are advisory: a flag means *look here*, not *wrong*.

## Signature

- ed25519 public key (base64): `YoEHEghXFxrXvYKQoWQb+oDunzwdxBgpk03gxrdC7WI=`
- Verify: `titan-audit verify report.json`
