import Hintz2026.Assembly

/-!
# Hintz 2026 — Smoothness of X, A, X⁻¹, Y on U

ContDiffOn ℝ ⊤ (real analytic, `ω` in the pinned Mathlib) for all matrix entries
of X, A, X⁻¹, and Y = (Xᴴ)⁻¹ on U = {r > rPlus, 0 < θ < π}.
This implies real C∞ at order `∞` by `ContDiffOn.of_le le_top`.
-/

open Complex Real Function Matrix
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-! ═══ Building blocks ═══ -/

private theorem smooth_r : ContDiff ℝ ⊤ (fun x : Fin 2 → ℝ => x 0) :=
  contDiff_pi.mp contDiff_id 0
private theorem smooth_th : ContDiff ℝ ⊤ (fun x : Fin 2 → ℝ => x 1) :=
  contDiff_pi.mp contDiff_id 1
private theorem smooth_Del : ContDiff ℝ ⊤ (fun x : Fin 2 → ℝ => Del p (x 0)) := by
  unfold Del; fun_prop
private theorem smooth_coe {f : (Fin 2 → ℝ) → ℝ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (fun x => (↑(f x) : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
private theorem smooth_sin : ContDiff ℝ ⊤ (fun x : Fin 2 → ℝ => Real.sin (x 1)) :=
  Real.contDiff_sin.comp smooth_th
private theorem smooth_complex_mk {f g : (Fin 2 → ℝ) → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) :
    ContDiff ℝ ⊤ (fun x => (⟨f x, g x⟩ : ℂ)) := by
  have : (fun x => (⟨f x, g x⟩ : ℂ)) = fun x => ↑(f x) + ↑(g x) * I := by
    ext x; exact Complex.mk_eq_add_mul_I (f x) (g x)
  rw [this]; exact (smooth_coe hf).add ((smooth_coe hg).mul contDiff_const)

private theorem smooth_rhoBar : ContDiff ℝ ⊤ (rhoBar p) := by
  unfold rhoBar; exact smooth_complex_mk smooth_r ((Real.contDiff_cos.comp smooth_th).const_smul p.a)
private theorem smooth_rhoBarStar : ContDiff ℝ ⊤ (rhoBarStar p) := by
  unfold rhoBarStar; exact smooth_complex_mk smooth_r (((Real.contDiff_cos.comp smooth_th).const_smul p.a).neg)

private theorem contDiffOn_sqrtDel :
    ContDiffOn ℝ ⊤ (fun x : Fin 2 → ℝ => Real.sqrt (Del p (x 0))) (U p) := by
  intro x hx; exact ((smooth_Del p).contDiffAt.sqrt (ne_of_gt (Del_pos p hx.1))).contDiffWithinAt
private theorem contDiffOn_coe_sqrtDel :
    ContDiffOn ℝ ⊤ (fun x => (↑(Real.sqrt (Del p (x 0))) : ℂ)) (U p) :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_sqrtDel p)

private theorem cdoU_inv_rhoBar : ContDiffOn ℝ ⊤ (fun x => (rhoBar p x)⁻¹) (U p) :=
  (smooth_rhoBar p).contDiffOn.inv (fun x hx => rhoBar_ne_zero p hx)
private theorem cdoU_inv_rhoBarStar : ContDiffOn ℝ ⊤ (fun x => (rhoBarStar p x)⁻¹) (U p) :=
  (smooth_rhoBarStar p).contDiffOn.inv (fun x hx => rhoBarStar_ne_zero p hx)
private theorem cdoU_inv_rhoBar_sq : ContDiffOn ℝ ⊤ (fun x => ((rhoBar p x) ^ 2)⁻¹) (U p) :=
  ((smooth_rhoBar p).contDiffOn.pow 2).inv (fun x hx => pow_ne_zero 2 (rhoBar_ne_zero p hx))
private theorem cdoU_inv_rhoBarStar_sq : ContDiffOn ℝ ⊤ (fun x => ((rhoBarStar p x) ^ 2)⁻¹) (U p) :=
  ((smooth_rhoBarStar p).contDiffOn.pow 2).inv (fun x hx => pow_ne_zero 2 (rhoBarStar_ne_zero p hx))

/-! ═══ X entries ═══ -/

private theorem contDiffOn_X00 : ContDiffOn ℝ ⊤ (fun x => X p x 0 0) (U p) := by
  show ContDiffOn ℝ ⊤ (fun x =>
    ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) / rhoBar p x) (U p)
  exact ContDiffOn.mul (ContDiffOn.mul contDiffOn_const
    ((contDiffOn_coe_sqrtDel p).add (ContDiffOn.mul contDiffOn_const (smooth_coe smooth_sin).contDiffOn)))
    (cdoU_inv_rhoBar p)

private theorem contDiffOn_X01 : ContDiffOn ℝ ⊤ (fun x => X p x 0 1) (U p) := by
  show ContDiffOn ℝ ⊤ (fun x => -I * (↑p.M - ↑(p.Q ^ 2) / rhoBar p x)) (U p)
  exact ContDiffOn.mul contDiffOn_const
    (contDiffOn_const.sub (ContDiffOn.mul contDiffOn_const (cdoU_inv_rhoBar p)))

private theorem contDiffOn_X10 : ContDiffOn ℝ ⊤ (fun x => X p x 1 0) (U p) := by
  show ContDiffOn ℝ ⊤ (fun x => I * (↑p.M - ↑(p.Q ^ 2) / rhoBarStar p x)) (U p)
  exact ContDiffOn.mul contDiffOn_const
    (contDiffOn_const.sub (ContDiffOn.mul contDiffOn_const (cdoU_inv_rhoBarStar p)))

private theorem contDiffOn_X11 : ContDiffOn ℝ ⊤ (fun x => X p x 1 1) (U p) := by
  show ContDiffOn ℝ ⊤ (fun x =>
    ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) / rhoBarStar p x) (U p)
  exact ContDiffOn.mul (ContDiffOn.mul contDiffOn_const
    ((contDiffOn_coe_sqrtDel p).sub (ContDiffOn.mul contDiffOn_const (smooth_coe smooth_sin).contDiffOn)))
    (cdoU_inv_rhoBarStar p)

/-- Every entry of X is C∞ on U. -/
theorem contDiffOn_X_entry (i j : Fin 2) : ContDiffOn ℝ ⊤ (fun x => X p x i j) (U p) := by
  fin_cases i <;> fin_cases j
  · exact contDiffOn_X00 p
  · exact contDiffOn_X01 p
  · exact contDiffOn_X10 p
  · exact contDiffOn_X11 p

/-! ═══ A entries ═══ -/

private theorem contDiffOn_A01 : ContDiffOn ℝ ⊤ (fun x => A p x 0 1) (U p) := by
  show ContDiffOn ℝ ⊤ (fun x => -I * ↑p.Q * rhoBarStar p x / rhoBar p x ^ 2) (U p)
  exact ContDiffOn.mul (ContDiffOn.mul contDiffOn_const (smooth_rhoBarStar p).contDiffOn)
    (cdoU_inv_rhoBar_sq p)

private theorem contDiffOn_A10 : ContDiffOn ℝ ⊤ (fun x => A p x 1 0) (U p) := by
  show ContDiffOn ℝ ⊤ (fun x => I * ↑p.Q * rhoBar p x / rhoBarStar p x ^ 2) (U p)
  exact ContDiffOn.mul (ContDiffOn.mul contDiffOn_const (smooth_rhoBar p).contDiffOn)
    (cdoU_inv_rhoBarStar_sq p)

/-- Every entry of A is C∞ on U. -/
theorem contDiffOn_A_entry (i j : Fin 2) : ContDiffOn ℝ ⊤ (fun x => A p x i j) (U p) := by
  fin_cases i <;> fin_cases j
  · show ContDiffOn ℝ ⊤ (fun _ => (0 : ℂ)) (U p); exact contDiffOn_const
  · exact contDiffOn_A01 p
  · exact contDiffOn_A10 p
  · show ContDiffOn ℝ ⊤ (fun _ => (0 : ℂ)) (U p); exact contDiffOn_const

/-! ═══ X⁻¹ entries ═══ -/

private theorem contDiffOn_det_inv : ContDiffOn ℝ ⊤ (fun x => (X p x).det⁻¹) (U p) :=
  contDiffOn_const.congr (fun x hx => by rw [det_X p hx])

/-- Every entry of X⁻¹ is C∞ on U. Uses det(X) = const and adjugate formulas. -/
theorem contDiffOn_Xinv_entry (i j : Fin 2) :
    ContDiffOn ℝ ⊤ (fun x => (X p x)⁻¹ i j) (U p) := by
  have h00 : ContDiffOn ℝ ⊤ (fun x => (X p x)⁻¹ 0 0) (U p) :=
    ((contDiffOn_det_inv p).mul (contDiffOn_X11 p)).congr (fun x _ => Xinv_00 p x)
  have h01 : ContDiffOn ℝ ⊤ (fun x => (X p x)⁻¹ 0 1) (U p) :=
    ((contDiffOn_det_inv p).mul (contDiffOn_X01 p).neg).congr (fun x _ => Xinv_01 p x)
  have h10 : ContDiffOn ℝ ⊤ (fun x => (X p x)⁻¹ 1 0) (U p) :=
    ((contDiffOn_det_inv p).mul (contDiffOn_X10 p).neg).congr (fun x _ => Xinv_10 p x)
  have h11 : ContDiffOn ℝ ⊤ (fun x => (X p x)⁻¹ 1 1) (U p) :=
    ((contDiffOn_det_inv p).mul (contDiffOn_X00 p)).congr (fun x _ => Xinv_11 p x)
  fin_cases i <;> fin_cases j <;> assumption

/-! ═══ Y = (Xᴴ)⁻¹ entries ═══ -/

/-- Every entry of Y = (Xᴴ)⁻¹ is C∞ on U. Uses (Xᴴ)⁻¹ i j = star(X⁻¹ j i). -/
theorem contDiffOn_Y_entry (i j : Fin 2) :
    ContDiffOn ℝ ⊤ (fun x => ((X p x)ᴴ)⁻¹ i j) (U p) := by
  have key : ∀ x, ((X p x)ᴴ)⁻¹ i j = starRingEnd ℂ ((X p x)⁻¹ j i) := by
    intro x; rw [← conjTranspose_nonsing_inv, conjTranspose_apply]; rfl
  simp_rw [key]
  exact Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_Xinv_entry p j i)

/-! ═══ Axiom audit ═══ -/

#print axioms contDiffOn_X_entry
#print axioms contDiffOn_A_entry
#print axioms contDiffOn_Xinv_entry
#print axioms contDiffOn_Y_entry

end Hintz2026

end
