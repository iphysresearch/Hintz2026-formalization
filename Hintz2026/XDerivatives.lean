import Hintz2026.Eq6

/-!
# Hintz 2026 — Slice derivatives of X entries and D₋X = AX
-/

open Complex Matrix
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-! ### X entry reductions -/

@[simp] theorem X_01_eq (z : Fin 2 → ℝ) :
    X p z 0 1 = -I * (↑p.M - ↑(p.Q ^ 2) / rhoBar p z) := by simp [X]

@[simp] theorem X_10_eq (z : Fin 2 → ℝ) :
    X p z 1 0 = I * (↑p.M - ↑(p.Q ^ 2) / rhoBarStar p z) := by simp [X]

/-! ### HasDerivAt for X₀₁ slices using congr_of_eventuallyEq -/

theorem hasDerivAt_X01_r (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X p (Function.update x 0 u) 0 1)
      (I * ↑(p.Q ^ 2) * (-1 / (rhoBar p x) ^ 2)) (x 0) := by
  -- Build HasDerivAt for the decomposed form
  have hc : HasDerivAt (fun _ : ℝ => -I * (↑p.M : ℂ)) 0 (x 0) := hasDerivAt_const _ _
  have hinv := (hasDerivAt_rhoBar_r p x).inv (rhoBar_ne_zero p hx)
  have hmul := hinv.const_mul (I * ↑(p.Q ^ 2))
  have hsum := hc.add hmul
  -- hsum is for the decomposed function; congr to match X form
  refine hsum.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u
    simp only [X_01_eq, Pi.add_apply, Pi.inv_apply]; ring
  · simp only [Function.update_eq_self]; ring

theorem hasDerivAt_X01_th (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X p (Function.update x 1 u) 0 1)
      (I * ↑(p.Q ^ 2) * (-(⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) / (rhoBar p x) ^ 2)) (x 1) := by
  have hc : HasDerivAt (fun _ : ℝ => -I * (↑p.M : ℂ)) 0 (x 1) := hasDerivAt_const _ _
  have hinv := (hasDerivAt_rhoBar_th p x).inv (rhoBar_ne_zero p hx)
  have hmul := hinv.const_mul (I * ↑(p.Q ^ 2))
  refine (hc.add hmul).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u
    simp only [X_01_eq, Pi.add_apply, Pi.inv_apply]; ring
  · simp only [Function.update_eq_self]; ring

/-! ### cpd of X₀₁ -/

theorem cpd_X01_r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => X p z 0 1) x =
    I * ↑(p.Q ^ 2) * (-1 / (rhoBar p x) ^ 2) :=
  (hasDerivAt_X01_r p x hx).deriv

theorem cpd_X01_th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => X p z 0 1) x =
    I * ↑(p.Q ^ 2) * (-(⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) / (rhoBar p x) ^ 2) :=
  (hasDerivAt_X01_th p x hx).deriv

/-! ### Dm of X₀₁ -/

-- ⟨0, y⟩ = ↑y * I
theorem mk_zero_eq_mul_I (y : ℝ) : (⟨0, y⟩ : ℂ) = ↑y * I := by
  apply Complex.ext <;> simp [mul_re, mul_im, I_re, I_im]

theorem Dm_X01 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => X p z 0 1) x =
    -I * ↑(p.Q ^ 2) * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) /
      (rhoBar p x) ^ 2 := by
  unfold Dm
  rw [cpd_X01_r p hx, cpd_X01_th p hx, mk_zero_eq_mul_I]
  have : (I : ℂ) ^ 2 = -1 := I_sq
  ring_nf
  simp only [I_pow_three, I_sq, neg_mul, mul_neg, neg_neg]
  push_cast; ring

/-! ### HasDerivAt for X₁₀ slices -/

theorem hasDerivAt_X10_r (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X p (Function.update x 0 u) 1 0)
      (-I * ↑(p.Q ^ 2) * (-1 / (rhoBarStar p x) ^ 2)) (x 0) := by
  have hc : HasDerivAt (fun _ : ℝ => I * (↑p.M : ℂ)) 0 (x 0) := hasDerivAt_const _ _
  have hinv := (hasDerivAt_rhoBarStar_r p x).inv (rhoBarStar_ne_zero p hx)
  refine (hc.add (hinv.const_mul (-I * ↑(p.Q ^ 2)))).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u
    simp only [X_10_eq, Pi.add_apply, Pi.inv_apply]; ring
  · simp only [Function.update_eq_self]; ring

theorem hasDerivAt_X10_th (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X p (Function.update x 1 u) 1 0)
      (-I * ↑(p.Q ^ 2) * (-(⟨0, p.a * Real.sin (x 1)⟩ : ℂ) / (rhoBarStar p x) ^ 2)) (x 1) := by
  have hc : HasDerivAt (fun _ : ℝ => I * (↑p.M : ℂ)) 0 (x 1) := hasDerivAt_const _ _
  have hinv := (hasDerivAt_rhoBarStar_th p x).inv (rhoBarStar_ne_zero p hx)
  refine (hc.add (hinv.const_mul (-I * ↑(p.Q ^ 2)))).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
  · filter_upwards with u
    simp only [X_10_eq, Pi.add_apply, Pi.inv_apply]; ring
  · simp only [Function.update_eq_self]; ring

theorem cpd_X10_r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => X p z 1 0) x =
    -I * ↑(p.Q ^ 2) * (-1 / (rhoBarStar p x) ^ 2) :=
  (hasDerivAt_X10_r p x hx).deriv

theorem cpd_X10_th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => X p z 1 0) x =
    -I * ↑(p.Q ^ 2) * (-(⟨0, p.a * Real.sin (x 1)⟩ : ℂ) / (rhoBarStar p x) ^ 2) :=
  (hasDerivAt_X10_th p x hx).deriv

theorem Dm_X10 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => X p z 1 0) x =
    I * ↑(p.Q ^ 2) * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) /
      (rhoBarStar p x) ^ 2 := by
  unfold Dm
  rw [cpd_X10_r p hx, cpd_X10_th p hx, mk_zero_eq_mul_I]
  ring_nf; simp only [I_pow_three, I_sq, neg_mul, mul_neg, neg_neg]; push_cast; ring

end Hintz2026

end
