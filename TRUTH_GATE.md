# TRUTH GATE — the GOD gate. Read this first.

Author: Benjamin Stanley Frohman. This file is the root instruction for every person and every
automated agent (every bot) that touches this repository. Load it before any other file.

**Only truth and honest, kernel-proved theorems pass this gate. Nothing from this repository is
published, released, deposited on Zenodo, cited or claimed unless the `truth-gate` check is green
on the exact commit being cited.** That is why it is the GOD gate: it sits above every other
check, and no other green check can stand in for it.

## The issue this gate fixes

A paper states its claim in English. Lean can only prove `formal_claim ↔ paper_claim` once
`paper_claim` is itself written in Lean. If `paper_claim` were simply *defined to be*
`formal_claim` (or an alias of it, or something that unfolds to it), the theorem
`intended_correspondence` would be `Iff.rfl`: it would be empty and prove nothing about the
paper. A green certificate could then "certify" a statement different from the one the paper
makes (drift), whether by accident or by an injected instruction.

## The fix rule (binding, permanent)

1. `paper_claim` is an **independent Lean transcription of the paper's exact claim**, written in
   the paper's own terms, with every hypothesis the paper states. The verbatim English quote,
   the paper path, its sha256 and the section are recorded in the doc comment of
   `Semantics.lean` **and** in this file (below).
2. `paper_claim` must **not** be defined as, reference, or trivially alias `formal_claim`.
3. `intended_correspondence : formal_claim ↔ paper_claim` must have a **substantive proof**. It
   may not be `Iff.rfl`, `rfl`, `exact Iff.rfl` or similar, and it may not use the main theorem
   (it is a statement-level equivalence, not "both sides happen to be provable").
4. `formal_claim` is exactly the statement of the repository's main theorem, and
   `paper_claim_holds` is the main theorem transported across the correspondence.
5. Only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, `admit`, `native_decide` or
   new `axiom` anywhere outside the draft directories in `TRUTH_GATE.lock`.
6. If the paper's English claim cannot be faithfully transcribed, or is not what Lean proves,
   the gate stays **red** and the mismatch is reported. Never patch over it: never weaken
   `paper_claim`, drop a hypothesis, or redefine it to match the formal side. If the
   formalization drifted, rewrite the formalization so it transports across the lock again.
7. Open problems stay hypotheses. No Millennium Prize problem is claimed solved; the gate only
   ensures the certificate proves precisely the locked claim and nothing else.
8. The locked region of `Semantics.lean`, the quote and `TRUTH_GATE.lock` change only with the
   author's explicit sign-off, as a PR that says "new lock" in its title.
9. Commits are authored by Benjamin Stanley Frohman only, with no AI co-author trailers. No
   force-push and no history rewriting.

## What `scripts/verify-lock.sh` checks mechanically

* `lake build` succeeds, with no `sorry` warning outside the draft directories;
* no `sorry` / `admit` / `native_decide` / `axiom` token outside the draft directories
  (comments and strings excluded);
* `Semantics.lean` has `PAPER_PATH`, `PAPER_SHA256`, `PAPER_SECTION` and a verbatim
  `PAPER_QUOTE`; the hash matches the paper file and the quote occurs in it; this file carries
  the same path, hash and quote;
* the lock region hash matches `TRUTH_GATE.lock`;
* `paper_claim`'s body does not mention `formal_claim`; the correspondence is not proved by
  `Iff.rfl`/`rfl`;
* in Lean: the bodies of `formal_claim` and `paper_claim` differ, the two are not
  definitionally equal, the correspondence proof does not reach the main theorem, the main
  theorem's statement is `formal_claim`, `paper_claim_holds` goes through the correspondence,
  and `#print axioms` shows only the three standard axioms.

What it cannot check: whether the transcription is the right reading of the English. That
reading is fixed once, in writing, below and in `Semantics.lean`, and is the author's sign-off.

## Running the gate locally

```
lake exe cache get
bash scripts/verify-lock.sh
```

Reports are written to `truth-gate-report/`.

## The locked claim of this repository

* Paper: `paper/main.tex`
* sha256: `331ec5aebb67be9849456a23cddd209ce6a50b9b9e6b0731c97441ae40029447`
* Section: Section "Sobolev smoothing", Theorem `heat_smoothing` (with the definitions it uses from Sections "Setting", "Heat semigroup" and "Sobolev smoothing")
* Main theorem(s): `TorusFourierNS.heat_smoothing`
* Lock file: `TRUTH_GATE.lock`; semantics: `TorusFourierNS/Semantics.lean`

Verbatim quote:

```
\begin{theorem}[\texttt{heat\_smoothing}] For $\nu,t>0$, $s\in\mathbb R$, $k\in\mathbb N$, $f\in H^s$:
$e^{t\nu\Delta}f\in H^{s+k}$ and $\|e^{t\nu\Delta}f\|_{H^{s+k}}^2\le k!\,e^{2\nu t}(2\nu t)^{-k}\|f\|_{H^s}^2$.\end{theorem}

$\mathbb T^3$ carries normalised Haar measure; $e_n(x)=e^{2\pi i n\cdot x}$, $n\in\mathbb Z^3$, is a
Hilbert basis of $L^2(\mathbb T^3)$ (Mathlib's \texttt{mFourierBasis}), and
$\hat f(n)=\int f\,\overline{e_n}$.

\begin{theorem} For $\nu,s,t\ge0$: $\widehat{e^{t\nu\Delta}f}(n)=e^{-\nu|n|^2t}\hat f(n)$,

$\|f\|_{H^s}^2=\sum_n(1+|n|^2)^s|\hat f(n)|^2$.
```

```lean
def formal_claim : Prop :=
  ∀ (ν t : ℝ) (hν : 0 < ν) (ht : 0 < t) (s : ℝ) (k : ℕ) (f : L2T3), InHs s f →
    InHs (s + k) (heat hν.le ht.le f) ∧
      HsSq (s + k) (heat hν.le ht.le f) ≤
        k.factorial * Real.exp (2 * ν * t) / (2 * ν * t) ^ k * HsSq s f

def paper_claim : Prop :=
  ∀ (ν t : ℝ), 0 < ν → 0 < t → ∀ (s : ℝ) (k : ℕ)
    (f g : MeasureTheory.Lp ℂ 2
      (MeasureTheory.Measure.pi fun _ : Fin 3 =>
        (AddCircle.haarAddCircle : MeasureTheory.Measure UnitAddCircle))),
    (∀ n : Fin 3 → ℤ,
      mFourierCoeff g n = (Real.exp (-(ν * (∑ i, ((n i : ℝ)) ^ 2) * t)) : ℂ) * mFourierCoeff f n) →
    Summable (fun n : Fin 3 → ℤ => (1 + ∑ i, ((n i : ℝ)) ^ 2) ^ s * ‖mFourierCoeff f n‖ ^ 2) →
    Summable (fun n : Fin 3 → ℤ =>
        (1 + ∑ i, ((n i : ℝ)) ^ 2) ^ (s + k) * ‖mFourierCoeff g n‖ ^ 2) ∧
      ∑' n : Fin 3 → ℤ, (1 + ∑ i, ((n i : ℝ)) ^ 2) ^ (s + k) * ‖mFourierCoeff g n‖ ^ 2 ≤
        (k.factorial : ℝ) * Real.exp (2 * ν * t) * ((2 * ν * t) ^ k)⁻¹ *
          ∑' n : Fin 3 → ℤ, (1 + ∑ i, ((n i : ℝ)) ^ 2) ^ s * ‖mFourierCoeff f n‖ ^ 2
```

See the doc comment of `TorusFourierNS/Semantics.lean` for the fixed reading of the paper's terms and the scope.
