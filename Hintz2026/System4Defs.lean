import Hintz2026.Eq6

/-!
# Hintz 2026 — System (4) coefficient matrices

Source: Hintz, arXiv:2609.33661v1, equation (4).
-/

open Complex Matrix
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-! ### Frequency parameters -/

/-- K = -(r² + a²)ω + am. -/
def Kfreq (ω m : ℝ) (r : ℝ) : ℝ := -(r ^ 2 + p.a ^ 2) * ω + p.a * m

/-- Δ' = 2(r - M). -/
def Del' (r : ℝ) : ℝ := 2 * (r - p.M)

theorem Del'_eq (r : ℝ) : Del' p r = 2 * r - 2 * p.M := by unfold Del'; ring

/-! ### B matrix (eq. 4) -/

/-- b^(ς)(x) — diagonal entry of B. -/
def bcoeff (ς ω m : ℝ) (x : Fin 2 → ℝ) : ℂ :=
  -↑ς * ↑(-p.a * ω * Real.sin (x 1) + m / Real.sin (x 1))
  - ↑(3 / 2 * Real.cos (x 1) / Real.sin (x 1))
  + 3 * Complex.I * ↑(p.a * Real.sin (x 1)) / rhoBarStar p x

/-- B^(ς) = i · [[b, 3(Mρ̄-Q²)/(Qρ̄)], [3Qρ̄/ρ̄*², -b]]. -/
def Bmat (ς ω m : ℝ) (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.I • !![bcoeff p ς ω m x,
         3 * (↑p.M * rhoBar p x - ↑(p.Q ^ 2)) / (↑p.Q * rhoBar p x);
         3 * ↑p.Q * rhoBar p x / rhoBarStar p x ^ 2,
         -bcoeff p ς ω m x]

/-! ### Scalar c (eq. 4) -/

/-- c^(ς) = (ς·iK/Δ + 3/ρ̄* - 3Δ'/(4Δ)) · √Δ. -/
def cscalar (ς ω m : ℝ) (x : Fin 2 → ℝ) : ℂ :=
  (↑ς * Complex.I * ↑(Kfreq p ω m (x 0)) / ↑(Del p (x 0))
   + 3 / rhoBarStar p x
   - ↑(3 * Del' p (x 0) / (4 * Del p (x 0))))
  * ↑(Real.sqrt (Del p (x 0)))

/-! ### trace B = 0 -/

theorem Bmat_trace_zero (ς ω m : ℝ) (x : Fin 2 → ℝ) :
    (Bmat p ς ω m x).trace = 0 := by
  unfold Bmat
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.smul_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, smul_eq_mul]

end Hintz2026

end
