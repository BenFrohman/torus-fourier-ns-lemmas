import Mathlib
import TorusFourierNS.SobolevField

/-!
# The Galerkin-truncated, Leray-projected Navier–Stokes system on `T³`

Concrete construction on the mode box `|kᵢ| ≤ N`:
`u̇_k = -4π²ν|k|² u_k - P_k (2πi ∑_{m+j=k} (u_m·j) u_j)`, with `P_k` the Leray projector.
Proved: `P_k` lands in `DivergenceFree` modes; the system has a local `C¹` solution
(`galerkinNS_local_existence`); and the solution stays `DivergenceFree` if the datum is
(`galerkinNS_divergenceFree`).

Coined names: `modeBox`, `GState`, `extendG`, `lerayP`, `gconv`, `nsBilin`, `nsBilinCLM`,
`viscCLM`, `galerkinNSField`.
-/

noncomputable section
open scoped BigOperators
open Filter Topology Complex

namespace TorusFourierNS

/-- Mode box `|kᵢ| ≤ N`. -/
def modeBox (N : ℕ) : Finset Mode := Fintype.piFinset fun _ => Finset.Icc (-(N : ℤ)) N

/-- Galerkin state space: coefficients on the mode box. -/
abbrev GState (N : ℕ) := (modeBox N) → Fin 3 → ℂ

/-- Extension by zero to a full Fourier field. -/
def extendG {N : ℕ} (v : GState N) : FField :=
  fun k i => if h : k ∈ modeBox N then v ⟨k, h⟩ i else 0

lemma extendG_add {N : ℕ} (v w : GState N) : extendG (v + w) = extendG v + extendG w := by
  funext k i; by_cases h : k ∈ modeBox N <;> simp [extendG, h]

lemma extendG_smul {N : ℕ} (c : ℝ) (v : GState N) : extendG (c • v) = c • extendG v := by
  funext k i; by_cases h : k ∈ modeBox N <;> simp [extendG, h]

lemma extendG_apply {N : ℕ} (v : GState N) (k : modeBox N) : extendG v k.1 = v k := by
  funext i; simp [extendG, k.2]

lemma dot_add' (k : Fin 3 → ℝ) (a b : Fin 3 → ℂ) : dot k (a + b) = dot k a + dot k b := by
  simp [dot, mul_add, Finset.sum_add_distrib]

lemma dot_smulC (k : Fin 3 → ℝ) (c : ℂ) (a : Fin 3 → ℂ) : dot k (c • a) = c * dot k a := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]; congr 1; funext i; ring

lemma dot_smulR (k : Fin 3 → ℝ) (c : ℝ) (a : Fin 3 → ℂ) : dot k (c • a) = c * dot k a := by
  rw [show c • a = (c : ℂ) • a by funext i; simp [Complex.real_smul]]; exact dot_smulC _ _ _

lemma dot_neg' (k : Fin 3 → ℝ) (a : Fin 3 → ℂ) : dot k (-a) = - dot k a := by
  simp [dot, Finset.sum_neg_distrib]

/-- Leray projector at mode `k`: `w - (k·w/|k|²) k` (identity at `k = 0`). -/
def lerayP (k : Mode) (w : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => w i - dot (kvec k) w / (ksq (kvec k) : ℂ) * (kvec k i : ℂ)

lemma dot_self_kvec (k : Mode) : ∑ i, (kvec k i : ℂ) * (kvec k i : ℂ) = (ksq (kvec k) : ℂ) := by
  simp [ksq, sq]

theorem lerayP_divFree (k : Mode) (w : Fin 3 → ℂ) : dot (kvec k) (lerayP k w) = 0 := by
  have e : dot (kvec k) (lerayP k w) =
      dot (kvec k) w - dot (kvec k) w / (ksq (kvec k) : ℂ) * (ksq (kvec k) : ℂ) := by
    simp only [dot, lerayP, mul_sub, Finset.sum_sub_distrib]
    rw [← dot_self_kvec, Finset.mul_sum]; congr 1; congr 1; funext i; ring
  rw [e]
  by_cases hk : ksq (kvec k) = 0
  · have hz : ∀ i, kvec k i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (kvec k j))).1 hk i
        (Finset.mem_univ _)
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    simp [dot, hz]
  · have : (ksq (kvec k) : ℂ) ≠ 0 := by exact_mod_cast hk
    field_simp; ring

lemma lerayP_add (k : Mode) (a b : Fin 3 → ℂ) : lerayP k (a + b) = lerayP k a + lerayP k b := by
  funext i; simp only [lerayP, dot_add', Pi.add_apply]; ring

lemma lerayP_smul (k : Mode) (c : ℝ) (a : Fin 3 → ℂ) : lerayP k (c • a) = c • lerayP k a := by
  funext i; simp only [lerayP, dot_smulR, Pi.smul_apply, Complex.real_smul]; ring

/-- Galerkin convective term `2πi ∑_{m ∈ box} (u_m · (k-m)) v_{k-m}` (with `v` extended by 0). -/
def gconv {N : ℕ} (u v : GState N) (k : Mode) : Fin 3 → ℂ := fun i =>
  2 * Real.pi * I * ∑ m : modeBox N,
    (∑ l, u m l * ((((k - m.1) l : ℤ)) : ℂ)) * extendG v (k - m.1) i

lemma gconv_add_left {N : ℕ} (u u' v : GState N) (k : Mode) :
    gconv (u + u') v k = gconv u v k + gconv u' v k := by
  funext i; simp only [gconv, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

lemma gconv_add_right {N : ℕ} (u v v' : GState N) (k : Mode) :
    gconv u (v + v') k = gconv u v k + gconv u v' k := by
  funext i; simp only [gconv, extendG_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma gconv_smul_left {N : ℕ} (c : ℝ) (u v : GState N) (k : Mode) :
    gconv (c • u) v k = c • gconv u v k := by
  funext i
  simp only [gconv, Pi.smul_apply, Complex.real_smul, Finset.mul_sum, Finset.sum_mul]
  congr 1; funext m; congr 1; funext l; ring

lemma gconv_smul_right {N : ℕ} (c : ℝ) (u v : GState N) (k : Mode) :
    gconv u (c • v) k = c • gconv u v k := by
  funext i
  simp only [gconv, extendG_smul, Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
  congr 1; funext m; ring

/-- Leray-projected Galerkin nonlinearity `B_N(u,v)_k = P_k (gconv u v k)`. -/
def nsBilin {N : ℕ} (u v : GState N) : GState N := fun k => lerayP k.1 (gconv u v k.1)

/-- `B_N` as a continuous `ℝ`-bilinear map. -/
def nsBilinCLM (N : ℕ) : GState N →L[ℝ] GState N →L[ℝ] GState N :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (GState N →ₗ[ℝ] GState N) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ nsBilin
        (fun u u' v => by funext k; simp [nsBilin, gconv_add_left, lerayP_add])
        (fun c u v => by
          funext k
          exact (congrArg (lerayP k.1) (gconv_smul_left c u v k.1)).trans (lerayP_smul _ _ _))
        (fun u v v' => by funext k; simp [nsBilin, gconv_add_right, lerayP_add])
        (fun c u v => by
          funext k
          exact (congrArg (lerayP k.1) (gconv_smul_right c u v k.1)).trans (lerayP_smul _ _ _)))

lemma nsBilinCLM_apply {N : ℕ} (u v : GState N) : nsBilinCLM N u v = nsBilin u v := rfl

/-- Viscous coefficient `4π²ν|k|²`. -/
def viscCoeff (ν : ℝ) (k : Mode) : ℝ := 4 * Real.pi ^ 2 * ν * ksq (kvec k)

/-- Viscous term `u ↦ (-4π²ν|k|² u_k)_k`. -/
def viscCLM (N : ℕ) (ν : ℝ) : GState N →L[ℝ] GState N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u k => (-viscCoeff ν k.1) • u k
      map_add' := fun u v => by funext k; exact smul_add _ _ _
      map_smul' := fun c u => by funext k; simp [smul_comm] }

/-- The Galerkin NS vector field `u ↦ -4π²ν|k|²u - B_N(u,u)`. -/
def galerkinNSField (N : ℕ) (ν : ℝ) : GState N → GState N :=
  galerkinField (viscCLM N ν) (-nsBilinCLM N)

/-- **Galerkin NS local existence** (proved). -/
theorem galerkinNS_local_existence (N : ℕ) (ν : ℝ) (u₀ : GState N) :
    ∃ α : ℝ → GState N, α 0 = u₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioo (0 - ε) (0 + ε), HasDerivAt α (galerkinNSField N ν (α t)) t :=
  galerkin_local_existence _ _ u₀

lemma dot_galerkinNSField {N : ℕ} (ν : ℝ) (u : GState N) (k : modeBox N) :
    dot (kvec k.1) (galerkinNSField N ν u k) = -(viscCoeff ν k.1 : ℂ) * dot (kvec k.1) (u k) := by
  simp only [galerkinNSField, galerkinField, ContinuousLinearMap.neg_apply, nsBilinCLM_apply]
  change dot (kvec k.1) ((-viscCoeff ν k.1) • u k + -(lerayP k.1 (gconv u u k.1))) = _
  rw [dot_add', dot_neg', lerayP_divFree, dot_smulR]; push_cast; ring

/-- **The Galerkin NS flow preserves `DivergenceFree`** (proved): on its interval of
existence, a solution from divergence-free data is divergence-free. -/
theorem galerkinNS_divergenceFree {N : ℕ} (ν : ℝ) {α : ℝ → GState N} {ε : ℝ}
    (hα : ∀ t ∈ Set.Ioo (0 - ε) (0 + ε), HasDerivAt α (galerkinNSField N ν (α t)) t)
    (h0 : DivergenceFree (extendG (α 0))) :
    ∀ t ∈ Set.Ioo (0 - ε) (0 + ε), DivergenceFree (extendG (α t)) := by
  intro t ht k
  by_cases hk : k ∈ modeBox N
  swap
  · simp [extendG, hk, dot]
  set kk : modeBox N := ⟨k, hk⟩
  have hex : ∀ s, extendG (α s) k = α s kk := fun s => extendG_apply (α s) kk
  set c := viscCoeff ν k
  set y : ℝ → ℂ := fun s => dot (kvec k) (α s kk)
  have hy : ∀ s ∈ Set.Ioo (0 - ε) (0 + ε), HasDerivAt y (-(c : ℂ) * y s) s := by
    intro s hs
    have h1 := hasDerivAt_pi.1 (hasDerivAt_pi.1 (hα s hs) kk)
    have : HasDerivAt y (dot (kvec k) (galerkinNSField N ν (α s) kk)) s := by
      simp only [y, dot]
      exact HasDerivAt.fun_sum fun i _ => (h1 i).const_mul _
    exact this.congr_deriv (dot_galerkinNSField ν (α s) kk)
  set z : ℝ → ℂ := fun s => (Real.exp (c * s) : ℂ) * y s
  have hz : ∀ s ∈ Set.Ioo (0 - ε) (0 + ε), HasDerivAt z 0 s := by
    intro s hs
    have he : HasDerivAt (fun s : ℝ => (Real.exp (c * s) : ℂ)) ((Real.exp (c * s) * c : ℝ) : ℂ) s :=
      (((hasDerivAt_id s).const_mul c).exp.congr_deriv (by simp [mul_comm])).ofReal_comp
    have := he.mul (hy s hs)
    convert this using 1; push_cast; ring
  have hopen : IsOpen (Set.Ioo (0 - ε) (0 + ε)) := isOpen_Ioo
  have h0mem : (0:ℝ) ∈ Set.Ioo (0 - ε) (0 + ε) := by
    rcases ht with ⟨a, b⟩; constructor <;> linarith
  have hc := hopen.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun s hs => (hz s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hz s hs).deriv) ht h0mem
  have hy0 : y 0 = 0 := by
    have := h0 k; simp only [hex] at this; exact this
  have hzt : z t = 0 := by rw [hc]; simp [z, hy0]
  have hne : (Real.exp (c * t) : ℂ) ≠ 0 := by exact_mod_cast (Real.exp_pos _).ne'
  show dot (kvec k) (extendG (α t) k) = 0
  rw [hex]
  exact (mul_eq_zero.1 hzt).resolve_left hne

end TorusFourierNS
