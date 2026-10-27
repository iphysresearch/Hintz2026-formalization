import Hintz2026.CSeparation

-- Hintz 2026 - Adjugate identities for C
-- Source: Hintz, arXiv:2609.33661v1, eq. (7): adj(cI - B) = cI + B since tr B = 0,
-- and the adjugate form of C used for Dp(z-) = adj(C) z+.

open Complex Matrix
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

theorem detX_Xinv_eq_adj {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    (X p x).det • (X p x)⁻¹ = adjugate (X p x) := by
  rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv, mul_inv_cancel₀ (det_ne p hx), one_smul]

theorem adjugate_cI_sub_B (c : ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (htr : B.trace = 0) :
    adjugate (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) - B) = c • 1 + B := by
  rw [adjugate_fin_two]
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at htr
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> linear_combination (-1 : ℂ) * htr

theorem adjugate_inv_eq (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det ≠ 0) :
    adjugate M⁻¹ = (M.det)⁻¹ • M := by
  have h1 : M⁻¹.adjugate * M⁻¹ = M⁻¹.det • 1 := adjugate_mul _
  rw [det_nonsing_inv, Ring.inverse_eq_inv] at h1
  have hinv : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  calc adjugate M⁻¹ = adjugate M⁻¹ * (M⁻¹ * M) := by rw [nonsing_inv_mul _ hinv, Matrix.mul_one]
    _ = (adjugate M⁻¹ * M⁻¹) * M := by rw [Matrix.mul_assoc]
    _ = (M.det⁻¹ • 1) * M := by rw [h1]
    _ = M.det⁻¹ • M := by rw [Matrix.smul_mul, Matrix.one_mul]

theorem Xstar_inv_eq {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    ((X p x)ᴴ)⁻¹ = (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ))⁻¹ • (adjugate (X p x))ᴴ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, det_conjTranspose, det_X p hx, Matrix.adjugate_conjTranspose]
  congr 1
  rw [star_def, conj_ofReal]

-- C = k⁻¹ • adj(X) (cI - B) adj(X)^H, k = Q² - M²
theorem Cmat_eq_adj_form (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Cmat p sg om mm x = (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ))⁻¹ •
      (adjugate (X p x) * (cscalar p sg om mm x • 1 - Bmat p sg om mm x) * (adjugate (X p x))ᴴ) := by
  unfold Cmat
  rw [Xstar_inv_eq p hx, Matrix.mul_smul, smul_smul, mul_comm, ← smul_smul,
    ← Matrix.smul_mul, ← Matrix.smul_mul, Matrix.smul_mul, Matrix.smul_mul]
  congr 1
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, detX_Xinv_eq_adj p hx]

-- adj(C) = k⁻¹ • X^H (cI + B) X
theorem adjugate_Cmat_eq (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    adjugate (Cmat p sg om mm x) =
      (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ))⁻¹ •
        ((X p x)ᴴ * (cscalar p sg om mm x • 1 + Bmat p sg om mm x) * X p x) := by
  have hk : ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Q_sq_sub_M_sq_ne_zero p
  rw [Cmat_eq_adj_form p sg om mm hx, adjugate_smul, adjugate_mul_distrib, adjugate_mul_distrib,
    adjugate_cI_sub_B _ _ (Bmat_trace_zero p sg om mm x), ← adjugate_conjTranspose,
    adjugate_adjugate _ (by simp)]
  simp only [Fintype.card_fin, Nat.sub_self, pow_zero, one_smul, pow_one, Nat.add_one_sub_one]
  rw [Matrix.mul_assoc]

end Hintz2026

end
