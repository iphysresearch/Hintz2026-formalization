import Hintz2026.System1Defs

-- Hintz 2026 - slice derivatives of the chiral prefactors Δ^{5/4}√sinθ and Δ^{-3/4}√sinθ (eq. 3)

open Complex
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-- ∂_r Δ^q = q Δ^{q-1} Δ'  for Δ > 0. -/
theorem hasDerivAt_rpow_Del (q : ℝ) {r : ℝ} (hD : 0 < Del p r) :
    HasDerivAt (fun u => Real.rpow (Del p u) q) (q * Real.rpow (Del p r) (q - 1) * Del' p r) r := by
  have h := (Real.hasDerivAt_rpow_const (p := q) (Or.inl hD.ne')).comp r (hasDerivAt_Del_r p r)
  refine h.congr_deriv ?_
  rw [Del'_eq]; simp only [Real.rpow_eq_pow]; try ring

/-- ∂_θ √(sin θ) = cos θ / (2 √(sin θ))  for sin θ > 0. -/
theorem hasDerivAt_sqrt_sin {θ : ℝ} (hs : 0 < Real.sin θ) :
    HasDerivAt (fun u => Real.sqrt (Real.sin u)) (Real.cos θ / (2 * Real.sqrt (Real.sin θ))) θ := by
  have h := (Real.hasDerivAt_sqrt hs.ne').comp θ (Real.hasDerivAt_sin θ)
  exact h.congr_deriv (by ring)

/-- Along r the θ-part of the prefactor is constant: ∂_r prePos = (5/4) Δ^{1/4} Δ' √sinθ. -/
theorem hasDerivAt_prePos_r (x : Fin 2 -> ℝ) (hD : 0 < Del p (x 0)) :
    HasDerivAt (fun u => prePos p (Function.update x 0 u))
      ((5/4) * Real.rpow (Del p (x 0)) (5/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1))) (x 0) := by
  have h := (hasDerivAt_rpow_Del p (5/4) hD).mul_const (Real.sqrt (Real.sin (x 1)))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with u
  simp [prePos, Function.update, show (1 : Fin 2) ≠ 0 from by decide]

theorem hasDerivAt_prePos_th (x : Fin 2 -> ℝ) (hs : 0 < Real.sin (x 1)) :
    HasDerivAt (fun u => prePos p (Function.update x 1 u))
      (Real.rpow (Del p (x 0)) (5/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) (x 1) := by
  have h := (hasDerivAt_sqrt_sin hs).const_mul (Real.rpow (Del p (x 0)) (5/4))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with u
  simp [prePos, Function.update, show (0 : Fin 2) ≠ 1 from by decide]

theorem hasDerivAt_preNeg_r (x : Fin 2 -> ℝ) (hD : 0 < Del p (x 0)) :
    HasDerivAt (fun u => preNeg p (Function.update x 0 u))
      ((-3/4) * Real.rpow (Del p (x 0)) (-3/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1))) (x 0) := by
  have h := (hasDerivAt_rpow_Del p (-3/4) hD).mul_const (Real.sqrt (Real.sin (x 1)))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with u
  simp [preNeg, Function.update, show (1 : Fin 2) ≠ 0 from by decide]

theorem hasDerivAt_preNeg_th (x : Fin 2 -> ℝ) (hs : 0 < Real.sin (x 1)) :
    HasDerivAt (fun u => preNeg p (Function.update x 1 u))
      (Real.rpow (Del p (x 0)) (-3/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) (x 1) := by
  have h := (hasDerivAt_sqrt_sin hs).const_mul (Real.rpow (Del p (x 0)) (-3/4))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with u
  simp [preNeg, Function.update, show (0 : Fin 2) ≠ 1 from by decide]

/-- Algebraic facts: Δ^{5/4} · Δ^{-1/2} relations used later. -/
theorem rpow_Del_mul_rpow {r : ℝ} (hD : 0 < Del p r) (a b : ℝ) :
    Real.rpow (Del p r) a * Real.rpow (Del p r) b = Real.rpow (Del p r) (a + b) :=
  (Real.rpow_add hD a b).symm

theorem sqrt_Del_eq_rpow {r : ℝ} (_hD : 0 < Del p r) :
    Real.sqrt (Del p r) = Real.rpow (Del p r) (1/2) := by
  rw [Real.sqrt_eq_rpow]; rfl

end Hintz2026

end
