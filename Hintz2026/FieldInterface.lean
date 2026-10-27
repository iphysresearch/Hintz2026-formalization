import Hintz2026.Smooth
import Hintz2026.SolutionCorr

/-!
# Hintz 2026 — Field interface, reverse iff, negative-control witness

Unknown fields are real C∞ (`∞` in the `ContDiff` scope). The explicit
coefficients retain their stronger real-analytic order `⊤ = ω`; `of_le`
lowers only the coefficient regularity needed by the field interface.
-/

open Complex Matrix Function Filter Real
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-! ═══ Xᴴ entry smooth ═══ -/

theorem contDiffOn_Xstar_entry (i j : Fin 2) :
    ContDiffOn ℝ ⊤ (fun x => (X p x)ᴴ i j) (U p) := by
  simp_rw [fun x => show (X p x)ᴴ i j = starRingEnd ℂ (X p x j i) from conjTranspose_apply _ _ _]
  exact Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_X_entry p j i)

/-! ═══ mulVec regularity ═══ -/

theorem contDiffOn_X_mulVec {v : (Fin 2 → ℝ) → Fin 2 → ℂ}
    (hv : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => v x j) (U p)) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => (X p x *ᵥ v x) i) (U p) := by
  simp only [mulVec, dotProduct, Fin.sum_univ_two]
  exact (((contDiffOn_X_entry p i 0).of_le le_top).mul (hv 0)).add
    (((contDiffOn_X_entry p i 1).of_le le_top).mul (hv 1))

theorem contDiffOn_Xinv_mulVec {v : (Fin 2 → ℝ) → Fin 2 → ℂ}
    (hv : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => v x j) (U p)) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => ((X p x)⁻¹ *ᵥ v x) i) (U p) := by
  simp only [mulVec, dotProduct, Fin.sum_univ_two]
  exact (((contDiffOn_Xinv_entry p i 0).of_le le_top).mul (hv 0)).add
    (((contDiffOn_Xinv_entry p i 1).of_le le_top).mul (hv 1))

theorem contDiffOn_Y_mulVec {v : (Fin 2 → ℝ) → Fin 2 → ℂ}
    (hv : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => v x j) (U p)) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => (((X p x)ᴴ)⁻¹ *ᵥ v x) i) (U p) := by
  simp only [mulVec, dotProduct, Fin.sum_univ_two]
  exact (((contDiffOn_Y_entry p i 0).of_le le_top).mul (hv 0)).add
    (((contDiffOn_Y_entry p i 1).of_le le_top).mul (hv 1))

theorem contDiffOn_Xstar_mulVec {v : (Fin 2 → ℝ) → Fin 2 → ℂ}
    (hv : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => v x j) (U p)) (i : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => ((X p x)ᴴ *ᵥ v x) i) (U p) := by
  simp only [mulVec, dotProduct, Fin.sum_univ_two]
  exact (((contDiffOn_Xstar_entry p i 0).of_le le_top).mul (hv 0)).add
    (((contDiffOn_Xstar_entry p i 1).of_le le_top).mul (hv 1))

/-! ═══ DifferentiableAt discharge ═══ -/

private theorem differentiableAt_update (x : Fin 2 → ℝ) (k : Fin 2) :
    DifferentiableAt ℝ (update x k) (x k) := by
  apply differentiableAt_pi.mpr; intro i
  fin_cases k <;> fin_cases i <;> simp [update, Fin.val] <;>
    first | exact differentiableAt_id | exact differentiableAt_const _

theorem differentiableAt_slice {f : (Fin 2 → ℝ) → ℂ} (hf : ContDiffOn ℝ ∞ f (U p))
    {x : Fin 2 → ℝ} (hx : x ∈ U p) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => f (update x k u)) (x k) := by
  have hdf : DifferentiableAt ℝ f x :=
    (hf.contDiffAt ((isOpen_U p).mem_nhds hx)).differentiableAt (by simp)
  conv at hdf => rw [show x = update x k (x k) from (update_eq_self k x).symm]
  exact hdf.comp (x k) (differentiableAt_update x k)

theorem hX_of_smooth {x : Fin 2 → ℝ} (hx : x ∈ U p) (i j k : Fin 2) :
    DifferentiableAt ℝ (fun u => X p (update x k u) i j) (x k) :=
  differentiableAt_slice p ((contDiffOn_X_entry p i j).of_le le_top) hx k

theorem hY_of_smooth {x : Fin 2 → ℝ} (hx : x ∈ U p) (i j k : Fin 2) :
    DifferentiableAt ℝ (fun u => (Matrix.conjTranspose (X p (update x k u)))⁻¹ i j) (x k) :=
  differentiableAt_slice p ((contDiffOn_Y_entry p i j).of_le le_top) hx k

theorem hv_of_smooth {v : (Fin 2 → ℝ) → Fin 2 → ℂ}
    (hv : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => v x j) (U p))
    {x : Fin 2 → ℝ} (hx : x ∈ U p) (j k : Fin 2) :
    DifferentiableAt ℝ (fun u => v (update x k u) j) (x k) :=
  differentiableAt_slice p (hv j) hx k

/-! ═══ Dm/Dp congr ═══ -/

theorem cpd_congr (k : Fin 2) {f g : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ}
    (hU : x ∈ U p) (h : Set.EqOn f g (U p)) : cpd k f x = cpd k g x := by
  unfold cpd; apply Filter.EventuallyEq.deriv_eq
  have hcont : Continuous (fun u : ℝ => update x k u) := continuous_pi (fun i => by
    by_cases hi : i = k
    · subst hi; simp only [update_self]; exact continuous_id
    · simp only [update_of_ne hi]; exact continuous_const)
  exact eventually_of_mem
    (hcont.continuousAt.preimage_mem_nhds ((isOpen_U p).mem_nhds (by simp [update_eq_self]; exact hU)))
    (fun u hu => h hu)

theorem Dm_congr {f g : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ}
    (hU : x ∈ U p) (h : Set.EqOn f g (U p)) : Dm p f x = Dm p g x := by
  unfold Dm; rw [cpd_congr p 0 hU h, cpd_congr p 1 hU h]

theorem Dp_congr {f g : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ}
    (hU : x ∈ U p) (h : Set.EqOn f g (U p)) : Dp p f x = Dp p g x := by
  unfold Dp; rw [cpd_congr p 0 hU h, cpd_congr p 1 hU h]

/-! ═══ ∀ x ∈ U iff ═══ -/

theorem Dm_zero_iff_Xv_residual_zero_on_U
    (v : (Fin 2 → ℝ) → Fin 2 → ℂ)
    (hv : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => v x j) (U p)) :
    (∀ x ∈ U p, (fun j => Dm p (fun z => v z j) x) = 0) ↔
    (∀ x ∈ U p, (fun i => Dm p (fun z => (X p z *ᵥ v z) i) x) -
      A p x *ᵥ (X p x *ᵥ v x) = 0) := by
  constructor <;> intro h x hx
  · rw [← Dm_v_zero_iff_Xv_residual_zero p hx v
      (fun i j k => hX_of_smooth p hx i j k) (fun j k => hv_of_smooth p hv hx j k)]
    exact h x hx
  · rw [Dm_v_zero_iff_Xv_residual_zero p hx v
      (fun i j k => hX_of_smooth p hx i j k) (fun j k => hv_of_smooth p hv hx j k)]
    exact h x hx

theorem Dp_zero_iff_Yv_residual_zero_on_U
    (v : (Fin 2 → ℝ) → Fin 2 → ℂ)
    (hv : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => v x j) (U p)) :
    (∀ x ∈ U p, (fun j => Dp p (fun z => v z j) x) = 0) ↔
    (∀ x ∈ U p, (fun i => Dp p (fun z => (((X p z)ᴴ)⁻¹ *ᵥ v z) i) x) +
      A p x *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ v x) = 0) := by
  constructor <;> intro h x hx
  · rw [← Dp_v_zero_iff_Yv_residual_zero p hx v
      (fun i j k => hY_of_smooth p hx i j k) (fun j k => hv_of_smooth p hv hx j k)]
    exact h x hx
  · rw [Dp_v_zero_iff_Yv_residual_zero p hx v
      (fun i j k => hY_of_smooth p hx i j k) (fun j k => hv_of_smooth p hv hx j k)]
    exact h x hx

/-! ═══ Reverse: Rminus(u)=0 ↔ Dminus(X⁻¹u)=0 ═══ -/

theorem Rminus_zero_iff_Dm_Xinv_zero
    (u : (Fin 2 → ℝ) → Fin 2 → ℂ)
    (hu : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => u x j) (U p))
    {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (fun j => Dm p (fun z => ((X p z)⁻¹ *ᵥ u z) j) x) = 0 ↔
    (fun i => Dm p (fun z => u z i) x) - A p x *ᵥ u x = 0 := by
  set v : (Fin 2 → ℝ) → Fin 2 → ℂ := fun z => (X p z)⁻¹ *ᵥ u z
  have hvs : ∀ j, ContDiffOn ℝ ∞ (fun x => v x j) (U p) :=
    fun j => contDiffOn_Xinv_mulVec p hu j
  have hXv : ∀ z ∈ U p, X p z *ᵥ v z = u z := fun z hz => X_Xinv_mulVec p hz (u z)
  have hres := Dm_Xv_sub_AXv p hx v
    (fun i j k => hX_of_smooth p hx i j k) (fun j k => hv_of_smooth p hvs hx j k)
  have key : (fun i => Dm p (fun z => u z i) x) - A p x *ᵥ u x =
      X p x *ᵥ (fun j => Dm p (fun z => v z j) x) := by
    conv_lhs => ext i; rw [Pi.sub_apply,
      ← show Dm p (fun z => (X p z *ᵥ v z) i) x = Dm p (fun z => u z i) x from
        Dm_congr p hx (fun z hz => congr_fun (hXv z hz) i),
      ← show (A p x *ᵥ (X p x *ᵥ v x)) i = (A p x *ᵥ u x) i from by rw [hXv x hx]]
    exact hres
  rw [key]; constructor
  · intro h; rw [h, mulVec_zero]
  · intro h
    have := congr_arg ((X p x)⁻¹ *ᵥ ·) h
    rwa [mulVec_mulVec, inv_mul_X p hx, one_mulVec, mulVec_zero] at this

theorem Rplus_zero_iff_Dp_Xstar_zero
    (u : (Fin 2 → ℝ) → Fin 2 → ℂ)
    (hu : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => u x j) (U p))
    {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (fun j => Dp p (fun z => ((X p z)ᴴ *ᵥ u z) j) x) = 0 ↔
    (fun i => Dp p (fun z => u z i) x) + A p x *ᵥ u x = 0 := by
  set v : (Fin 2 → ℝ) → Fin 2 → ℂ := fun z => (X p z)ᴴ *ᵥ u z
  have hvs : ∀ j, ContDiffOn ℝ ∞ (fun x => v x j) (U p) :=
    fun j => contDiffOn_Xstar_mulVec p hu j
  have hYv : ∀ z ∈ U p, ((X p z)ᴴ)⁻¹ *ᵥ v z = u z := fun z hz => Y_Xstar_mulVec p hz (u z)
  have hres := Dp_Yv_add_AYv p hx v
    (fun i j k => hY_of_smooth p hx i j k) (fun j k => hv_of_smooth p hvs hx j k)
  have key : (fun i => Dp p (fun z => u z i) x) + A p x *ᵥ u x =
      ((X p x)ᴴ)⁻¹ *ᵥ (fun j => Dp p (fun z => v z j) x) := by
    conv_lhs => ext i; rw [Pi.add_apply,
      ← show Dp p (fun z => (((X p z)ᴴ)⁻¹ *ᵥ v z) i) x = Dp p (fun z => u z i) x from
        Dp_congr p hx (fun z hz => congr_fun (hYv z hz) i),
      ← show (A p x *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ v x)) i = (A p x *ᵥ u x) i from by rw [hYv x hx]]
    exact hres
  rw [key]; constructor
  · intro h; rw [h, mulVec_zero]
  · intro h
    have := congr_arg ((X p x)ᴴ *ᵥ ·) h
    rwa [mulVec_mulVec, Xstar_mul_inv p hx, one_mulVec, mulVec_zero] at this

/-! ═══ Negative-control witness ═══ -/

def p0 : SubextremalKN where
  M := 2; a := 1; Q := 1
  hM := by norm_num
  hQ := by norm_num
  hSub := by norm_num

def x0 : Fin 2 → ℝ := ![4, Real.pi / 2]

theorem rPlus_p0_lt : rPlus p0 < 4 := by
  unfold rPlus p0; simp only
  have harg : (2 : ℝ) ^ 2 - (1 : ℝ) ^ 2 - (1 : ℝ) ^ 2 = 2 := by ring
  rw [harg]
  have : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2^2) from (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem x0_mem : x0 ∈ U p0 := by
  refine ⟨rPlus_p0_lt, ?_, ?_⟩
  · show (0 : ℝ) < (![4, Real.pi / 2] : Fin 2 → ℝ) 1
    simp [Matrix.cons_val_one, Matrix.head_cons]; positivity
  · show (![4, Real.pi / 2] : Fin 2 → ℝ) 1 < Real.pi
    simp [Matrix.cons_val_one, Matrix.head_cons]; linarith [Real.pi_pos]

theorem neg_control_witness :
    (of fun i j => Dbad p0 (fun z => X p0 z i j) x0) ≠ A p0 x0 * X p0 x0 :=
  Dbad_X_ne_AX p0 x0_mem (show p0.a ≠ 0 from one_ne_zero)

/-! ═══ Axiom audit ═══ -/

#print axioms contDiffOn_Xstar_entry
#print axioms contDiffOn_X_mulVec
#print axioms contDiffOn_Xinv_mulVec
#print axioms contDiffOn_Y_mulVec
#print axioms contDiffOn_Xstar_mulVec
#print axioms Dm_zero_iff_Xv_residual_zero_on_U
#print axioms Dp_zero_iff_Yv_residual_zero_on_U
#print axioms Rminus_zero_iff_Dm_Xinv_zero
#print axioms Rplus_zero_iff_Dp_Xstar_zero
#print axioms neg_control_witness

end Hintz2026

end
