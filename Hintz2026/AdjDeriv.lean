import Hintz2026.Transform7

-- Hintz 2026 - Derivative of adjugate(X) and X^H
-- Dm(adj X) = -(adj X) * A   (from Dm(X^{-1}) = -(X^{-1} A), det X const)
-- Dp(X^H) = X^H * A          (from Dm X = A X via conjugation, A^H = A)

open Complex Matrix Function
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

theorem adj_X_eq_const_smul_inv {z : Fin 2 -> ℝ} (hz : z ∈ U p) :
    adjugate (X p z) = ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) • (X p z)⁻¹ := by
  rw [← det_X p hz, Matrix.inv_def, smul_smul, Ring.inverse_eq_inv,
    mul_inv_cancel₀ (det_ne p hz), one_smul]

theorem adj_X_entry_eq {z : Fin 2 -> ℝ} (hz : z ∈ U p) (i j : Fin 2) :
    adjugate (X p z) i j = ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) * (X p z)⁻¹ i j := by
  rw [adj_X_eq_const_smul_inv p hz, Matrix.smul_apply, smul_eq_mul]

theorem Dm_adj_entry {x : Fin 2 -> ℝ} (hx : x ∈ U p) (i j : Fin 2) :
    Dm p (fun z => adjugate (X p z) i j) x =
    ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) * Dm p (fun z => (X p z)⁻¹ i j) x := by
  have heq : Set.EqOn (fun z => adjugate (X p z) i j)
      (fun z => ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) * (X p z)⁻¹ i j) (U p) :=
    fun z hz => adj_X_entry_eq p hz i j
  rw [Dm_congr p hx heq]
  unfold Dm cpd
  simp only [deriv_const_mul_field]
  ring

theorem Dm_adj_matrix {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    (of fun a b => Dm p (fun z => adjugate (X p z) a b) x) = -(adjugate (X p x) * A p x) := by
  ext i j
  simp only [of_apply, Dm_adj_entry p hx]
  have h := congr_fun (congr_fun (Dm_Xinv_matrix p hx) i) j
  simp only [of_apply, neg_mul, Matrix.neg_apply] at h
  rw [h, adj_X_eq_const_smul_inv p hx, Matrix.neg_apply, smul_mul_assoc, Matrix.smul_apply, smul_eq_mul]
  ring

theorem Dp_Xstar_matrix {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    (of fun a b => Dp p (fun z => (X p z)ᴴ a b) x) = (X p x)ᴴ * A p x := by
  ext i j
  simp only [of_apply]
  have key : ∀ z, (X p z)ᴴ i j = star (X p z j i) := fun z => conjTranspose_apply _ _ _
  simp_rw [key, Dp_eq_star_Dm_star]
  simp only [star_star]
  have h := congr_fun (congr_fun (Dminus_X_eq_AX p hx) j) i
  simp only [of_apply] at h
  rw [h, ← conjTranspose_apply, conjTranspose_mul, A_conjTranspose p hx]

end Hintz2026

end
