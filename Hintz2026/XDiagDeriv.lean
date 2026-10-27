import Hintz2026.XEntries
import Hintz2026.XDerivatives

set_option maxHeartbeats 800000

open Complex Matrix
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

private theorem hasDerivAt_ofReal_comp {f : ℝ → ℝ} {f' x : ℝ} (hf : HasDerivAt f f' x) :
    HasDerivAt (fun u => (↑(f u) : ℂ)) (↑f') x :=
  Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt x hf

/-! ### Numerator derivatives -/

private theorem hasDerivAt_Nplus_r (x : Fin 2 → ℝ) (hD : 0 < Del p (x 0)) :
    HasDerivAt (fun u => (↑p.Q : ℂ) * (↑(Real.sqrt (Del p u)) + ↑p.a * ↑(Real.sin (x 1))))
      (↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) (x 0) :=
  ((hasDerivAt_ofReal_comp (hasDerivAt_sqrtDel_r p hD)).add (hasDerivAt_const _ _)).const_mul _
    |>.congr_deriv (by push_cast; ring)

private theorem hasDerivAt_Nplus_th (x : Fin 2 → ℝ) :
    HasDerivAt (fun u => (↑p.Q : ℂ) * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin u)))
      (↑p.Q * ↑p.a * ↑(Real.cos (x 1))) (x 1) :=
  ((hasDerivAt_const _ _).add ((hasDerivAt_ofReal_comp (Real.hasDerivAt_sin (x 1))).const_mul _)).const_mul _
    |>.congr_deriv (by push_cast; ring)

private theorem hasDerivAt_Nminus_r (x : Fin 2 → ℝ) (hD : 0 < Del p (x 0)) :
    HasDerivAt (fun u => (↑p.Q : ℂ) * (↑(Real.sqrt (Del p u)) - ↑p.a * ↑(Real.sin (x 1))))
      (↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) (x 0) := by
  exact ((hasDerivAt_ofReal_comp (hasDerivAt_sqrtDel_r p hD)).sub (hasDerivAt_const _ _)).const_mul _
    |>.congr_deriv (by push_cast; ring)

private theorem hasDerivAt_Nminus_th (x : Fin 2 → ℝ) :
    HasDerivAt (fun u => (↑p.Q : ℂ) * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin u)))
      (-↑p.Q * ↑p.a * ↑(Real.cos (x 1))) (x 1) := by
  exact ((hasDerivAt_const _ (↑(Real.sqrt (Del p (x 0))) : ℂ)).sub
    ((hasDerivAt_ofReal_comp (Real.hasDerivAt_sin (x 1))).const_mul _)).const_mul _
    |>.congr_deriv (by push_cast; ring)

/-! ### X₀₀ HasDerivAt -/

theorem hasDerivAt_X00_r (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X00 p (Function.update x 0 u))
      ((↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1)))) /
        (rhoBar p x) ^ 2) (x 0) :=
  ((hasDerivAt_Nplus_r p x (Del_pos p hx.1)).div
    (hasDerivAt_rhoBar_r p x) (rhoBar_ne_zero p hx)).congr_of_eventuallyEq
    (by filter_upwards with u; exact (X00_r_eq p x u).symm)
    |>.congr_deriv (by simp [Function.update_eq_self])

theorem hasDerivAt_X00_th (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X00 p (Function.update x 1 u))
      ((↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) *
          (⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ)) /
        (rhoBar p x) ^ 2) (x 1) :=
  ((hasDerivAt_Nplus_th p x).div
    (hasDerivAt_rhoBar_th p x) (rhoBar_ne_zero p hx)).congr_of_eventuallyEq
    (by filter_upwards with u; exact (X00_th_eq p x u).symm)
    |>.congr_deriv (by simp [Function.update_eq_self])

/-! ### X₁₁ HasDerivAt -/

theorem hasDerivAt_X11_r (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X11 p (Function.update x 0 u))
      ((↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBarStar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1)))) /
        (rhoBarStar p x) ^ 2) (x 0) :=
  ((hasDerivAt_Nminus_r p x (Del_pos p hx.1)).div
    (hasDerivAt_rhoBarStar_r p x) (rhoBarStar_ne_zero p hx)).congr_of_eventuallyEq
    (by filter_upwards with u; exact (X11_r_eq p x u).symm)
    |>.congr_deriv (by simp [Function.update_eq_self])

theorem hasDerivAt_X11_th (x : Fin 2 → ℝ) (hx : x ∈ U p) :
    HasDerivAt (fun u => X11 p (Function.update x 1 u))
      ((-↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBarStar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) *
          (⟨0, p.a * Real.sin (x 1)⟩ : ℂ)) /
        (rhoBarStar p x) ^ 2) (x 1) :=
  ((hasDerivAt_Nminus_th p x).div
    (hasDerivAt_rhoBarStar_th p x) (rhoBarStar_ne_zero p hx)).congr_of_eventuallyEq
    (by filter_upwards with u; exact (X11_th_eq p x u).symm)
    |>.congr_deriv (by simp [Function.update_eq_self])

/-! ### cpd -/

theorem cpd_X00_r' {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (X00 p) x = (↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1)))) / (rhoBar p x) ^ 2 :=
  (hasDerivAt_X00_r p x hx).deriv

theorem cpd_X00_th' {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (X00 p) x = (↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) *
        (⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ)) / (rhoBar p x) ^ 2 :=
  (hasDerivAt_X00_th p x hx).deriv

theorem cpd_X11_r' {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (X11 p) x = (↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBarStar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1)))) / (rhoBarStar p x) ^ 2 :=
  (hasDerivAt_X11_r p x hx).deriv

theorem cpd_X11_th' {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (X11 p) x = (-↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBarStar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) *
        (⟨0, p.a * Real.sin (x 1)⟩ : ℂ)) / (rhoBarStar p x) ^ 2 :=
  (hasDerivAt_X11_th p x hx).deriv


private theorem cpd_X00_r_mul {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (X00 p) x * (rhoBar p x) ^ 2 =
    ↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) :=
  by rw [cpd_X00_r' p hx, div_mul_cancel₀ _ (pow_ne_zero 2 (rhoBar_ne_zero p hx))]

private theorem cpd_X00_th_mul {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (X00 p) x * (rhoBar p x) ^ 2 =
    ↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) *
        (⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) :=
  by rw [cpd_X00_th' p hx, div_mul_cancel₀ _ (pow_ne_zero 2 (rhoBar_ne_zero p hx))]


private theorem cpd_X11_r_mul {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (X11 p) x * (rhoBarStar p x) ^ 2 =
    ↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBarStar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) :=
  by rw [cpd_X11_r' p hx, div_mul_cancel₀ _ (pow_ne_zero 2 (rhoBarStar_ne_zero p hx))]

private theorem cpd_X11_th_mul {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (X11 p) x * (rhoBarStar p x) ^ 2 =
    -↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBarStar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) *
        (⟨0, p.a * Real.sin (x 1)⟩ : ℂ) :=
  by rw [cpd_X11_th' p hx, div_mul_cancel₀ _ (pow_ne_zero 2 (rhoBarStar_ne_zero p hx))]

/-! ### Dm -/

theorem Dm_X00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (X00 p) x =
    ↑p.Q * (↑p.M * rhoBarStar p x - ↑(p.Q ^ 2)) / (rhoBar p x) ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 (rhoBar_ne_zero p hx))]
  unfold Dm
  rw [show (↑(Real.sqrt (Del p (x 0))) * cpd 0 (X00 p) x - I * cpd 1 (X00 p) x) *
    (rhoBar p x) ^ 2 =
    ↑(Real.sqrt (Del p (x 0))) * (cpd 0 (X00 p) x * (rhoBar p x) ^ 2) -
    I * (cpd 1 (X00 p) x * (rhoBar p x) ^ 2) from by ring]
  rw [cpd_X00_r_mul p hx, cpd_X00_th_mul p hx]
  have hcancel : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) =
    ↑(x 0 - p.M) := by
    rw [← ofReal_mul, mul_div_cancel₀ _ (Real.sqrt_ne_zero'.mpr (Del_pos p hx.1))]
  have hsqsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑(Real.sqrt (Del p (x 0))) =
    ↑(Del p (x 0)) := by
    rw [← ofReal_mul, Real.mul_self_sqrt (le_of_lt (Del_pos p hx.1))]
  conv_lhs =>
    rw [show ↑(Real.sqrt (Del p (x 0))) *
      (↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBar p x -
       ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1)))) =
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) * rhoBar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) * ↑(Real.sqrt (Del p (x 0))) +
        ↑(Real.sqrt (Del p (x 0))) * (↑p.a * ↑(Real.sin (x 1)))) from by ring]
  rw [hcancel, hsqsq]
  simp only [rhoBar, rhoBarStar]
  have hDel : Del p (x 0) = x 0 ^ 2 - 2 * p.M * x 0 + p.a ^ 2 + p.Q ^ 2 := rfl
  have htrig : Real.sin (x 1) ^ 2 + Real.cos (x 1) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hre1 : (⟨x 0, p.a * Real.cos (x 1)⟩ : ℂ).re = x 0 := rfl
  have him1 : (⟨x 0, p.a * Real.cos (x 1)⟩ : ℂ).im = p.a * Real.cos (x 1) := rfl
  have hre2 : (⟨x 0, -(p.a * Real.cos (x 1))⟩ : ℂ).re = x 0 := rfl
  have him2 : (⟨x 0, -(p.a * Real.cos (x 1))⟩ : ℂ).im = -(p.a * Real.cos (x 1)) := rfl
  have hre3 : (⟨(0 : ℝ), -(p.a * Real.sin (x 1))⟩ : ℂ).re = 0 := rfl
  have him3 : (⟨(0 : ℝ), -(p.a * Real.sin (x 1))⟩ : ℂ).im = -(p.a * Real.sin (x 1)) := rfl
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      hre1, him1, hre2, him2, hre3, him3]
  · linear_combination -p.Q * hDel + p.Q * p.a ^ 2 * htrig
  · linear_combination (0 : ℝ)

theorem Dm_X11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (X11 p) x =
    ↑p.Q * (↑p.M * rhoBar p x - ↑(p.Q ^ 2)) / (rhoBarStar p x) ^ 2 := by
  rw [eq_div_iff (pow_ne_zero 2 (rhoBarStar_ne_zero p hx))]
  unfold Dm
  rw [show (↑(Real.sqrt (Del p (x 0))) * cpd 0 (X11 p) x - I * cpd 1 (X11 p) x) *
    (rhoBarStar p x) ^ 2 =
    ↑(Real.sqrt (Del p (x 0))) * (cpd 0 (X11 p) x * (rhoBarStar p x) ^ 2) -
    I * (cpd 1 (X11 p) x * (rhoBarStar p x) ^ 2) from by ring]
  rw [cpd_X11_r_mul p hx, cpd_X11_th_mul p hx]
  have hcancel : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) =
    ↑(x 0 - p.M) := by
    rw [← ofReal_mul, mul_div_cancel₀ _ (Real.sqrt_ne_zero'.mpr (Del_pos p hx.1))]
  have hsqsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑(Real.sqrt (Del p (x 0))) =
    ↑(Del p (x 0)) := by
    rw [← ofReal_mul, Real.mul_self_sqrt (le_of_lt (Del_pos p hx.1))]
  conv_lhs =>
    rw [show ↑(Real.sqrt (Del p (x 0))) *
      (↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBarStar p x -
       ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1)))) =
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) * rhoBarStar p x -
      ↑p.Q * (↑(Real.sqrt (Del p (x 0))) * ↑(Real.sqrt (Del p (x 0))) -
        ↑(Real.sqrt (Del p (x 0))) * (↑p.a * ↑(Real.sin (x 1)))) from by ring]
  rw [hcancel, hsqsq]
  simp only [rhoBar, rhoBarStar]
  have hDel : Del p (x 0) = x 0 ^ 2 - 2 * p.M * x 0 + p.a ^ 2 + p.Q ^ 2 := rfl
  have htrig : Real.sin (x 1) ^ 2 + Real.cos (x 1) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have hre1 : (⟨x 0, p.a * Real.cos (x 1)⟩ : ℂ).re = x 0 := rfl
  have him1 : (⟨x 0, p.a * Real.cos (x 1)⟩ : ℂ).im = p.a * Real.cos (x 1) := rfl
  have hre2 : (⟨x 0, -(p.a * Real.cos (x 1))⟩ : ℂ).re = x 0 := rfl
  have him2 : (⟨x 0, -(p.a * Real.cos (x 1))⟩ : ℂ).im = -(p.a * Real.cos (x 1)) := rfl
  have hre3 : (⟨(0 : ℝ), p.a * Real.sin (x 1)⟩ : ℂ).re = 0 := rfl
  have him3 : (⟨(0 : ℝ), p.a * Real.sin (x 1)⟩ : ℂ).im = p.a * Real.sin (x 1) := rfl
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      hre1, him1, hre2, him2, hre3, him3]
  · linear_combination -p.Q * hDel + p.Q * p.a ^ 2 * htrig
  · linear_combination (0 : ℝ)

end Hintz2026

end
