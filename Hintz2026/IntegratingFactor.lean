import Hintz2026.Domain

/-!
# Hintz 2026 — Matrix integrating factor X and connection A

Source: Hintz, arXiv:2609.33661v1, equations (4)–(6).
-/

open Complex Matrix Finset
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

def X (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) / rhoBar p x,
     -I * (↑p.M - ↑(p.Q ^ 2) / rhoBar p x);
     I * (↑p.M - ↑(p.Q ^ 2) / rhoBarStar p x),
     ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) / rhoBarStar p x]

def A (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -I * ↑p.Q * rhoBarStar p x / rhoBar p x ^ 2;
     I * ↑p.Q * rhoBar p x / rhoBarStar p x ^ 2, 0]

def XN (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))),
     -I * (↑p.M * rhoBar p x - ↑(p.Q ^ 2));
     I * (↑p.M * rhoBarStar p x - ↑(p.Q ^ 2)),
     ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1)))]

/-! ### Conjugation helpers -/

theorem conj_rhoBar_eq (x : Fin 2 → ℝ) :
    conj (rhoBar p x) = rhoBarStar p x := (rhoBarStar_eq_conj p x).symm

theorem conj_rhoBarStar_eq (x : Fin 2 → ℝ) :
    conj (rhoBarStar p x) = rhoBar p x := by
  rw [rhoBarStar_eq_conj, starRingEnd_self_apply]

/-! ### det X · ρ·ρ* = det XN -/

theorem det_X_mul_eq_det_XN {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (X p x).det * (rhoBar p x * rhoBarStar p x) = (XN p x).det := by
  simp only [X, XN, det_fin_two_of]
  field_simp [rhoBar_ne_zero p hx, rhoBarStar_ne_zero p hx]

/-! ### det XN = (Q²-M²)·ρ·ρ* -/

theorem det_XN (x : Fin 2 → ℝ) (hDel : 0 < Del p (x 0)) :
    (XN p x).det = ↑(p.Q ^ 2 - p.M ^ 2) * (rhoBar p x * rhoBarStar p x) := by
  simp only [XN, det_fin_two_of, rhoBar, rhoBarStar]
  set r := x 0; set c := Real.cos (x 1); set sn := Real.sin (x 1)
  set ac := p.a * c; set sqD := Real.sqrt (Del p r)
  have hsq : sqD ^ 2 = r ^ 2 - 2 * p.M * r + p.a ^ 2 + p.Q ^ 2 :=
    (Real.sq_sqrt (le_of_lt hDel)).trans rfl
  have htrig : sn ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  · linear_combination p.Q ^ 2 * hsq - p.Q ^ 2 * p.a ^ 2 * htrig
  · linear_combination (0 : ℝ)

/-! ### det X = Q² - M² -/

theorem det_X {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (X p x).det = ↑(p.Q ^ 2 - p.M ^ 2) :=
  mul_right_cancel₀ (mul_ne_zero (rhoBar_ne_zero p hx) (rhoBarStar_ne_zero p hx))
    ((det_X_mul_eq_det_XN p hx).trans (det_XN p x (Del_pos p hx.1)))

theorem X_det_isUnit {x : Fin 2 → ℝ} (hx : x ∈ U p) : IsUnit (X p x).det := by
  rw [det_X p hx, isUnit_iff_ne_zero]; exact_mod_cast Q_sq_sub_M_sq_ne_zero p

/-! ### Hermitian A -/

theorem A_conjTranspose {x : Fin 2 → ℝ} (_hx : x ∈ U p) :
    (A p x)ᴴ = A p x := by
  ext i j; simp only [conjTranspose_apply]
  fin_cases i <;> fin_cases j <;>
    simp [A, star_def, conj_rhoBar_eq p, conj_rhoBarStar_eq p]

/-! ### Invertibility -/

theorem X_mul_inv {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    X p x * (X p x)⁻¹ = 1 := mul_nonsing_inv _ (X_det_isUnit p hx)

theorem inv_mul_X {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (X p x)⁻¹ * X p x = 1 := nonsing_inv_mul _ (X_det_isUnit p hx)

theorem Xstar_det_isUnit {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    IsUnit (X p x)ᴴ.det := by
  rw [det_conjTranspose]; exact IsUnit.map (starRingEnd ℂ) (X_det_isUnit p hx)

theorem Xstar_mul_inv {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (X p x)ᴴ * ((X p x)ᴴ)⁻¹ = 1 := mul_nonsing_inv _ (Xstar_det_isUnit p hx)

theorem inv_mul_Xstar {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    ((X p x)ᴴ)⁻¹ * (X p x)ᴴ = 1 := nonsing_inv_mul _ (Xstar_det_isUnit p hx)

end Hintz2026

end
