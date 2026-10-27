import Hintz2026.IntegratingFactor

/-!
# Hintz 2026 — Slice derivatives of building blocks
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-! ### ∂_r Δ and ∂_r √Δ -/

theorem hasDerivAt_Del_r (r : ℝ) :
    HasDerivAt (Del p) (2 * r - 2 * p.M) r := by
  have : Del p = fun r => r ^ 2 + (-2 * p.M) * r + (p.a ^ 2 + p.Q ^ 2) := by
    ext r; unfold Del; ring
  rw [this]
  exact ((hasDerivAt_pow 2 r).add ((hasDerivAt_id r).const_mul _)).add
    (hasDerivAt_const _ _) |>.congr_deriv (by ring)

theorem hasDerivAt_sqrtDel_r {r : ℝ} (hD : 0 < Del p r) :
    HasDerivAt (fun r => Real.sqrt (Del p r))
      ((r - p.M) / Real.sqrt (Del p r)) r :=
  ((Real.hasDerivAt_sqrt (ne_of_gt hD)).comp r (hasDerivAt_Del_r p r)).congr_deriv
    (by field_simp)

/-! ### Key helper: HasDerivAt for ℂ.mk from real components -/

/-- If `f, g : ℝ → ℝ` have derivatives `f', g'` at `x`, then
`u ↦ ⟨f u, g u⟩ : ℝ → ℂ` has derivative `⟨f', g'⟩` at `x`. -/
theorem hasDerivAt_complex_mk {f g : ℝ → ℝ} {f' g' : ℝ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun u => (⟨f u, g u⟩ : ℂ)) ⟨f', g'⟩ x := by
  -- ↑(f u) has derivative ↑f'
  have hfc : HasDerivAt (fun u => (↑(f u) : ℂ)) (↑f') x :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hf
  -- ↑(g u) has derivative ↑g'
  have hgc : HasDerivAt (fun u => (↑(g u) : ℂ)) (↑g') x :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hg
  -- ↑(g u) * I has derivative ↑g' * I
  have hgI : HasDerivAt (fun u => (↑(g u) : ℂ) * I) (↑g' * I) x := hgc.mul_const I
  -- Sum
  have hsum := hfc.add hgI
  -- ↑(f u) + ↑(g u) * I = ⟨f u, g u⟩
  refine hsum.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u
    apply Complex.ext <;> simp [mul_re, mul_im, I_re, I_im]
  · apply Complex.ext <;> simp [mul_re, mul_im, I_re, I_im]

/-! ### ρ̄ derivatives -/

-- ∂_r ρ̄ = 1
theorem hasDerivAt_rhoBar_r (x : Fin 2 → ℝ) :
    HasDerivAt (fun u => rhoBar p (Function.update x 0 u)) 1 (x 0) := by
  have h := hasDerivAt_complex_mk (hasDerivAt_id (x 0))
    (hasDerivAt_const (x 0) (p.a * Real.cos (x 1)))
  refine h.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u
    unfold rhoBar; congr 1 <;> simp [show (0 : Fin 2) ≠ 1 from by decide]
  · apply Complex.ext <;> simp

-- ∂_r ρ̄* = 1
theorem hasDerivAt_rhoBarStar_r (x : Fin 2 → ℝ) :
    HasDerivAt (fun u => rhoBarStar p (Function.update x 0 u)) 1 (x 0) := by
  have h := hasDerivAt_complex_mk (hasDerivAt_id (x 0))
    (hasDerivAt_const (x 0) (-(p.a * Real.cos (x 1))))
  refine h.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u
    unfold rhoBarStar; congr 1 <;> simp [show (0 : Fin 2) ≠ 1 from by decide]
  · apply Complex.ext <;> simp

-- ∂_θ ρ̄ = ⟨0, -a sinθ⟩
theorem hasDerivAt_rhoBar_th (x : Fin 2 → ℝ) :
    HasDerivAt (fun u => rhoBar p (Function.update x 1 u))
      (⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) (x 1) := by
  have hcos : HasDerivAt (fun u => p.a * Real.cos u) (-(p.a * Real.sin (x 1))) (x 1) :=
    ((Real.hasDerivAt_cos (x 1)).const_mul p.a).congr_deriv (by ring)
  have h := hasDerivAt_complex_mk (hasDerivAt_const (x 1) (x 0)) hcos
  refine h.congr_of_eventuallyEq ?_
  · filter_upwards with u
    unfold rhoBar; congr 1 <;> simp [show (1 : Fin 2) ≠ 0 from by decide]

-- ∂_θ ρ̄* = ⟨0, a sinθ⟩
theorem hasDerivAt_rhoBarStar_th (x : Fin 2 → ℝ) :
    HasDerivAt (fun u => rhoBarStar p (Function.update x 1 u))
      (⟨0, p.a * Real.sin (x 1)⟩ : ℂ) (x 1) := by
  have hcos : HasDerivAt (fun u => -(p.a * Real.cos u)) (p.a * Real.sin (x 1)) (x 1) :=
    (((Real.hasDerivAt_cos (x 1)).const_mul p.a).neg).congr_deriv (by ring)
  have h := hasDerivAt_complex_mk (hasDerivAt_const (x 1) (x 0)) hcos
  refine h.congr_of_eventuallyEq ?_
  · filter_upwards with u
    unfold rhoBarStar; congr 1 <;> simp [show (1 : Fin 2) ≠ 0 from by decide]

end Hintz2026

end
