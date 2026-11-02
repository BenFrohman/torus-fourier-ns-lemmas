# Naming glossary

This file follows the naming standard in [`BenFrohman/Clay-` `NAMING.md`](https://github.com/BenFrohman/Clay-/blob/main/NAMING.md).
**Nothing in this file is proved. The canonical open statement is OPEN.**

## Canonical names

| Role | Canonical name | Status |
|---|---|---|
| Core object | **Frohmanian Tether** (𝔉𝕋) | definition |
| Open statement | **Frohmanian Tether Hypothesis** (FT), parts (A) and (B) | **open** |
| Result, once proved | **Frohmanian Tether Theorem** | *reserved*: not used, because FT is not proved |

FT (A): the bending strain $(I-\tau\otimes\tau)S\tau$, with $\tau=\omega/|\omega|$, stays bounded where $|\omega|$ is large on $[0,T^*)$.
FT (B): that bound gives a $\tfrac12$-Hölder vorticity direction. Both parts are open; their Lean forms live in
[`periodic-ns-classical-continuation`](https://github.com/BenFrohman/periodic-ns-classical-continuation).

## Rules

- An open statement is called a **Hypothesis**. It is never called a "Law" or a "Theorem" in a paper or README.
  It becomes a Theorem only once it is proved.
- A Lean declaration written `theorem` is a kernel-checked implication from its stated hypotheses. When those
  hypotheses are open, the result is **conditional**, and the text says so.
- Code names in this repository are kept as historical records; this file maps them to the canonical names.
- Navier–Stokes global regularity remains open. Nothing here is a certificate.
