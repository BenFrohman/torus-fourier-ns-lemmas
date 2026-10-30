/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import TorusFourierNS.SobolevField

/-!
# Convergence of the inner convolution sum in `fconv`

Proved: for `f g ∈ H^s` with `0 ≤ s` (in particular `s > 3/2`) the series
`∑_j f (k-j) i * g j i` defining `fconv f g k i` is absolutely summable (Cauchy–Schwarz in ℓ²).
-/

noncomputable section
namespace TorusFourierNS

lemma one_le_sobW {s : ℝ} (hs : 0 ≤ s) (k : Mode) : 1 ≤ sobW s k :=
  Real.one_le_rpow (by have : 0 ≤ ∑ i, ((k i : ℝ))^2 := by positivity
                       linarith) hs

/-- An `H^s` field (`s ≥ 0`) has square-summable components. -/
lemma summable_sq_of_memHs {s : ℝ} (hs : 0 ≤ s) {f : FField} (hf : MemHsField s f) (i : Fin 3) :
    Summable fun j : Mode => ‖f j i‖ ^ 2 := by
  have h1 : Summable fun j : Mode => sobW s j * ‖f j i‖ ^ 2 :=
    hf.comp_injective (i := fun j : Mode => (j, i)) (fun a b h => (Prod.mk.inj h).1)
  refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun j => ?_) h1
  have := one_le_sobW hs j
  nlinarith [sq_nonneg ‖f j i‖]

/-- **Proved.** Absolute summability of the inner convolution series. -/
theorem summable_norm_fconv_inner {s : ℝ} (hs : 0 ≤ s) {f g : FField}
    (hf : MemHsField s f) (hg : MemHsField s g) (k : Mode) (i : Fin 3) :
    Summable fun j : Mode => ‖f (k - j) i * g j i‖ := by
  have hF : Summable fun j : Mode => ‖f (k - j) i‖ ^ (2:ℝ) := by
    have := (Equiv.subLeft k).summable_iff.2 (summable_sq_of_memHs hs hf i)
    simpa [Real.rpow_two, Function.comp_def] using this
  have hG : Summable fun j : Mode => ‖g j i‖ ^ (2:ℝ) := by
    simpa [Real.rpow_two] using summable_sq_of_memHs hs hg i
  have := Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hF hG
  simpa [norm_mul] using this

/-- **Proved.** The inner series of `fconv` converges (so `fconv` is the genuine sum). -/
theorem summable_fconv_inner {s : ℝ} (hs : 0 ≤ s) {f g : FField}
    (hf : MemHsField s f) (hg : MemHsField s g) (k : Mode) (i : Fin 3) :
    Summable fun j : Mode => f (k - j) i * g j i :=
  (summable_norm_fconv_inner hs hf hg k i).of_norm

theorem summable_fconv_inner_of_gt {s : ℝ} (hs : 3/2 < s) {f g : FField}
    (hf : MemHsField s f) (hg : MemHsField s g) (k : Mode) (i : Fin 3) :
    Summable fun j : Mode => f (k - j) i * g j i :=
  summable_fconv_inner (by linarith) hf hg k i

end TorusFourierNS
