import Hintz2026.Derivatives

/-!
# Hintz 2026 — Integrating factor equations (eq. 6)
-/

open Complex Matrix
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

def cpd (i : Fin 2) (f : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) : ℂ :=
  deriv (fun u => f (Function.update x i u)) (x i)

def Dm (f : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) : ℂ :=
  ↑(Real.sqrt (Del p (x 0))) * cpd 0 f x - I * cpd 1 f x

def Dp (f : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) : ℂ :=
  ↑(Real.sqrt (Del p (x 0))) * cpd 0 f x + I * cpd 1 f x

/-! ### cpd of ρ̄, ρ̄* -/

theorem cpd_rhoBar_r (x : Fin 2 → ℝ) : cpd 0 (rhoBar p) x = 1 :=
  (hasDerivAt_rhoBar_r p x).deriv

theorem cpd_rhoBar_th (x : Fin 2 → ℝ) :
    cpd 1 (rhoBar p) x = ⟨0, -(p.a * Real.sin (x 1))⟩ :=
  (hasDerivAt_rhoBar_th p x).deriv

theorem cpd_rhoBarStar_r (x : Fin 2 → ℝ) : cpd 0 (rhoBarStar p) x = 1 :=
  (hasDerivAt_rhoBarStar_r p x).deriv

theorem cpd_rhoBarStar_th (x : Fin 2 → ℝ) :
    cpd 1 (rhoBarStar p) x = ⟨0, p.a * Real.sin (x 1)⟩ :=
  (hasDerivAt_rhoBarStar_th p x).deriv

/-! ### D₋ ρ̄, D₋ ρ̄*

D₋ ρ̄ = √Δ · 1 - I · ⟨0, -a sinθ⟩ = √Δ - ⟨a sinθ, 0⟩ = ↑(√Δ - a sinθ)
D₋ ρ̄* = √Δ · 1 - I · ⟨0, a sinθ⟩ = √Δ + ⟨a sinθ, 0⟩ = ↑(√Δ + a sinθ)
-/

theorem I_mul_mk_zero_left (y : ℝ) : I * (⟨0, y⟩ : ℂ) = ↑(-y) := by
  apply Complex.ext
  · simp [mul_re, I_re, I_im]
  · simp [mul_im, I_re, I_im]

theorem Dm_rhoBar (x : Fin 2 → ℝ) :
    Dm p (rhoBar p) x = ↑(Real.sqrt (Del p (x 0)) - p.a * Real.sin (x 1)) := by
  unfold Dm; rw [cpd_rhoBar_r, cpd_rhoBar_th, I_mul_mk_zero_left]; push_cast; ring

theorem Dm_rhoBarStar (x : Fin 2 → ℝ) :
    Dm p (rhoBarStar p) x = ↑(Real.sqrt (Del p (x 0)) + p.a * Real.sin (x 1)) := by
  unfold Dm; rw [cpd_rhoBarStar_r, cpd_rhoBarStar_th, I_mul_mk_zero_left]; push_cast; ring

/-! ### cpd of 1/ρ̄, 1/ρ̄* -/

-- Use exact h.deriv (definitional equality handles the beta-reduction)
theorem cpd_inv_rhoBar_r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun x => (rhoBar p x)⁻¹) x =
    -1 / (rhoBar p x) ^ 2 := by
  exact ((hasDerivAt_rhoBar_r p x).inv (rhoBar_ne_zero p hx)).deriv

theorem cpd_inv_rhoBar_th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun x => (rhoBar p x)⁻¹) x =
    -(⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) / (rhoBar p x) ^ 2 := by
  exact ((hasDerivAt_rhoBar_th p x).inv (rhoBar_ne_zero p hx)).deriv

theorem cpd_inv_rhoBarStar_r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun x => (rhoBarStar p x)⁻¹) x =
    -1 / (rhoBarStar p x) ^ 2 := by
  exact ((hasDerivAt_rhoBarStar_r p x).inv (rhoBarStar_ne_zero p hx)).deriv

theorem cpd_inv_rhoBarStar_th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun x => (rhoBarStar p x)⁻¹) x =
    -(⟨0, p.a * Real.sin (x 1)⟩ : ℂ) / (rhoBarStar p x) ^ 2 := by
  exact ((hasDerivAt_rhoBarStar_th p x).inv (rhoBarStar_ne_zero p hx)).deriv


end Hintz2026

end
