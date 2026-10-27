import Hintz2026.System4Defs
import Hintz2026.FieldInterface

/-!
# Hintz 2026 — Transformation (7): z± and matrix C

Source: Hintz, arXiv:2609.33661v1, equation (7).
-/

open Complex Matrix Function
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-- z+^(ς) = adj(X) · y+ = (det X) · X⁻¹ · y+.
    Using adjugate avoids scalar-mulVec commutativity issues. -/
def zplus (yplus : (Fin 2 → ℝ) → Fin 2 → ℂ)
    (x : Fin 2 → ℝ) : Fin 2 → ℂ :=
  adjugate (X p x) *ᵥ yplus x

/-- z-^(ς) = X* · y- -/
def zminus (yminus : (Fin 2 → ℝ) → Fin 2 → ℂ)
    (x : Fin 2 → ℝ) : Fin 2 → ℂ :=
  (X p x)ᴴ *ᵥ yminus x

/-- C^(ς) = (det X) · X⁻¹ · (c·I - B) · (X*)⁻¹ -/
def Cmat (ς ω m : ℝ) (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (X p x).det • ((X p x)⁻¹ * (cscalar p ς ω m x • 1 - Bmat p ς ω m x) * ((X p x)ᴴ)⁻¹)

theorem det_ne {x : Fin 2 → ℝ} (hx : x ∈ U p) : (X p x).det ≠ 0 := by
  rw [det_X p hx]; exact_mod_cast Q_sq_sub_M_sq_ne_zero p

/-- X · z+ = (det X) • y+ -/
theorem X_mulVec_zplus (yplus : (Fin 2 → ℝ) → Fin 2 → ℂ)
    (x : Fin 2 → ℝ) :
    X p x *ᵥ zplus p yplus x = (X p x).det • yplus x := by
  simp only [zplus, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]

/-- y+ recovered from z+: (det X)⁻¹ • X · z+ = y+ -/
theorem yplus_of_zplus (yplus : (Fin 2 → ℝ) → Fin 2 → ℂ)
    {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (X p x).det⁻¹ • (X p x *ᵥ zplus p yplus x) = yplus x := by
  rw [X_mulVec_zplus, smul_smul, inv_mul_cancel₀ (det_ne p hx), one_smul]

/-- y- recovered from z-: (X*)⁻¹ · z- = y- -/
theorem yminus_of_zminus (yminus : (Fin 2 → ℝ) → Fin 2 → ℂ)
    {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    ((X p x)ᴴ)⁻¹ *ᵥ zminus p yminus x = yminus x := by
  simp only [zminus, mulVec_mulVec, inv_mul_Xstar p hx, one_mulVec]

end Hintz2026

end
