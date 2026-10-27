import Hintz2026.Residual

/-!
# Hintz 2026 — Solution correspondence (iff)

D₋v = 0 ↔ D₋(Xv) − A(Xv) = 0, and D₊v = 0 ↔ D₊(Yv) + A(Yv) = 0,
with regularity-preserving forward/inverse maps.
-/

open Complex Matrix Function
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-! ═══ mulVec invertibility ═══ -/

private theorem mulVec_eq_zero_iff {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : IsUnit M.det)
    {w : Fin 2 → ℂ} : M *ᵥ w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have : M⁻¹ *ᵥ (M *ᵥ w) = M⁻¹ *ᵥ 0 := congr_arg _ h
    rwa [mulVec_mulVec, nonsing_inv_mul _ hM, one_mulVec, mulVec_zero] at this
  · intro h; rw [h, mulVec_zero]

/-! ═══ D₋ solution correspondence ═══ -/

/-- D₋v = 0 ⟺ D₋(Xv) − A·(Xv) = 0 — the D₋ homogeneous equation transfers through X. -/
theorem Dm_v_zero_iff_Xv_residual_zero {x : Fin 2 → ℝ} (hx : x ∈ U p)
    (v : (Fin 2 → ℝ) → Fin 2 → ℂ)
    (hX : ∀ i j k, DifferentiableAt ℝ (fun u => X p (update x k u) i j) (x k))
    (hv : ∀ j k, DifferentiableAt ℝ (fun u => v (update x k u) j) (x k)) :
    (fun j => Dm p (fun z => v z j) x) = 0 ↔
    (fun i => Dm p (fun z => (X p z *ᵥ v z) i) x) - A p x *ᵥ (X p x *ᵥ v x) = 0 := by
  rw [Dm_Xv_sub_AXv p hx v hX hv]
  exact (mulVec_eq_zero_iff (X_det_isUnit p hx)).symm

/-! ═══ D₊ solution correspondence ═══ -/

/-- D₊v = 0 ⟺ D₊(Yv) + A·(Yv) = 0 — the D₊ homogeneous equation transfers through Y = (Xᴴ)⁻¹. -/
theorem Dp_v_zero_iff_Yv_residual_zero {x : Fin 2 → ℝ} (hx : x ∈ U p)
    (v : (Fin 2 → ℝ) → Fin 2 → ℂ)
    (hY : ∀ i j k, DifferentiableAt ℝ (fun u => ((X p (update x k u))ᴴ)⁻¹ i j) (x k))
    (hv : ∀ j k, DifferentiableAt ℝ (fun u => v (update x k u) j) (x k)) :
    (fun j => Dp p (fun z => v z j) x) = 0 ↔
    (fun i => Dp p (fun z => (((X p z)ᴴ)⁻¹ *ᵥ v z) i) x) +
    A p x *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ v x) = 0 := by
  rw [Dp_Yv_add_AYv p hx v hY hv]
  constructor
  · intro h; rw [h, mulVec_zero]
  · intro h
    have : (X p x)ᴴ *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ (fun j => Dp p (fun z => v z j) x)) =
           (X p x)ᴴ *ᵥ 0 := congr_arg ((X p x)ᴴ *ᵥ ·) h
    rwa [mulVec_mulVec, Xstar_mul_inv p hx, one_mulVec, mulVec_zero] at this

/-! ═══ Axiom audit ═══ -/

#print axioms Dm_v_zero_iff_Xv_residual_zero
#print axioms Dp_v_zero_iff_Yv_residual_zero

end Hintz2026

end
