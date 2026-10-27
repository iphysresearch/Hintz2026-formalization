import Hintz2026.Equivalence1to4

-- Hintz 2026 - C∞ regularity on U of the chiral variables (3) for C∞ fields,
-- and the slice-differentiability data PosDiff/NegDiff from C∞.

open Complex Function
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-! ### building blocks -/

theorem contDiffOn_Del : ContDiff ℝ ∞ (fun x : Fin 2 -> ℝ => Del p (x 0)) := by
  unfold Del; fun_prop

theorem contDiffOn_rpow_Del (q : ℝ) : ContDiffOn ℝ ∞ (fun x : Fin 2 -> ℝ => Real.rpow (Del p (x 0)) q) (U p) := by
  intro x hx
  have h : ContDiffAt ℝ ∞ (fun x : Fin 2 -> ℝ => Del p (x 0) ^ q) x :=
    ContDiffAt.rpow_const_of_ne (contDiffOn_Del p).contDiffAt (Del_pos p hx.1).ne'
  exact h.contDiffWithinAt

theorem contDiffOn_sqrt_sin : ContDiffOn ℝ ∞ (fun x : Fin 2 -> ℝ => Real.sqrt (Real.sin (x 1))) (U p) := by
  intro x hx
  have hsin : ContDiff ℝ ∞ (fun x : Fin 2 -> ℝ => Real.sin (x 1)) := Real.contDiff_sin.comp (contDiff_pi.mp contDiff_id 1)
  exact (hsin.contDiffAt.sqrt (sin_pos_of_mem p hx).ne').contDiffWithinAt

theorem contDiffOn_prePos : ContDiffOn ℝ ∞ (fun x => (↑(prePos p x) : ℂ)) (U p) :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn ((contDiffOn_rpow_Del p (5/4)).mul (contDiffOn_sqrt_sin p))

theorem contDiffOn_preNeg : ContDiffOn ℝ ∞ (fun x => (↑(preNeg p x) : ℂ)) (U p) :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn ((contDiffOn_rpow_Del p (-3/4)).mul (contDiffOn_sqrt_sin p))

theorem contDiffOn_sqrtDel_c : ContDiffOn ℝ ∞ (fun x => (↑(Real.sqrt (Del p (x 0))) : ℂ)) (U p) := by
  refine Complex.ofRealCLM.contDiff.comp_contDiffOn ?_
  intro x hx
  exact ((contDiffOn_Del p).contDiffAt.sqrt (Del_pos p hx.1).ne').contDiffWithinAt

theorem contDiffOn_inv_sqrtDel_c : ContDiffOn ℝ ∞ (fun x => ((↑(Real.sqrt (Del p (x 0))) : ℂ))⁻¹) (U p) :=
  (contDiffOn_sqrtDel_c p).inv (fun x hx => by exact_mod_cast (Real.sqrt_pos.mpr (Del_pos p hx.1)).ne')

/-! ### C∞ fields -/

structure PosSmooth (F : PosFields) : Prop where
  psi2 : ContDiffOn ℝ ∞ F.psi2 (U p)
  psi1 : ContDiffOn ℝ ∞ F.psi1 (U p)
  k    : ContDiffOn ℝ ∞ F.k (U p)
  s    : ContDiffOn ℝ ∞ F.s (U p)

structure NegSmooth (G : NegFields) : Prop where
  psim2 : ContDiffOn ℝ ∞ G.psim2 (U p)
  psim1 : ContDiffOn ℝ ∞ G.psim1 (U p)
  n     : ContDiffOn ℝ ∞ G.n (U p)
  l     : ContDiffOn ℝ ∞ G.l (U p)

theorem posDiff_of_smooth {F : PosFields} (hF : PosSmooth p F) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : PosDiff F x :=
  ⟨fun k => differentiableAt_slice p hF.psi2 hx k, fun k => differentiableAt_slice p hF.psi1 hx k,
   fun k => differentiableAt_slice p hF.k hx k, fun k => differentiableAt_slice p hF.s hx k⟩

theorem negDiff_of_smooth {G : NegFields} (hG : NegSmooth p G) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : NegDiff G x :=
  ⟨fun k => differentiableAt_slice p hG.psim2 hx k, fun k => differentiableAt_slice p hG.psim1 hx k,
   fun k => differentiableAt_slice p hG.n hx k, fun k => differentiableAt_slice p hG.l hx k⟩

/-! ### the chiral variables are C∞ on U -/

theorem contDiffOn_yPos {F : PosFields} (hF : PosSmooth p F) (e : ℝ) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => yPos p e F x j) (U p) := by
  fin_cases j
  · show ContDiffOn ℝ ∞ (fun x => yPos p e F x 0) (U p)
    simp only [yPos_0, g1]
    refine (contDiffOn_prePos p).mul (hF.psi2.add ?_)
    simp only [div_eq_mul_inv]
    exact (contDiffOn_const.mul hF.psi1).mul (contDiffOn_inv_sqrtDel_c p)
  · show ContDiffOn ℝ ∞ (fun x => yPos p e F x 1) (U p)
    simp only [yPos_1, g2]
    refine (contDiffOn_prePos p).mul (contDiffOn_const.mul (hF.k.add ?_))
    simp only [div_eq_mul_inv]
    exact (contDiffOn_const.mul hF.s).mul (contDiffOn_inv_sqrtDel_c p)

theorem contDiffOn_yNeg {G : NegFields} (hG : NegSmooth p G) (e : ℝ) (j : Fin 2) :
    ContDiffOn ℝ ∞ (fun x => yNeg p e G x j) (U p) := by
  fin_cases j
  · show ContDiffOn ℝ ∞ (fun x => yNeg p e G x 0) (U p)
    simp only [yNeg_0, g1N]
    exact (contDiffOn_preNeg p).mul (hG.psim2.sub ((contDiffOn_const.mul (contDiffOn_sqrtDel_c p)).mul hG.psim1))
  · show ContDiffOn ℝ ∞ (fun x => yNeg p e G x 1) (U p)
    simp only [yNeg_1, g2N]
    exact (contDiffOn_preNeg p).mul (contDiffOn_const.mul (hG.n.sub ((contDiffOn_const.mul (contDiffOn_sqrtDel_c p)).mul hG.l)))

end Hintz2026

end
