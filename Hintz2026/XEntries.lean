import Hintz2026.IntegratingFactor

/-!
# Hintz 2026 — Individual X and A matrix entries

Standalone definitions for each entry of X(r,θ) and A(r,θ),
avoiding the !![] elaboration bottleneck.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-! ### X entries (Hintz eq. 5) -/

def X00 (x : Fin 2 → ℝ) : ℂ :=
  ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) / rhoBar p x

def X01 (x : Fin 2 → ℝ) : ℂ :=
  -I * (↑p.M - ↑(p.Q ^ 2) / rhoBar p x)

def X10 (x : Fin 2 → ℝ) : ℂ :=
  I * (↑p.M - ↑(p.Q ^ 2) / rhoBarStar p x)

def X11 (x : Fin 2 → ℝ) : ℂ :=
  ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) / rhoBarStar p x

/-! ### A entries (Hintz eq. 4) -/

def A01 (x : Fin 2 → ℝ) : ℂ :=
  -I * ↑p.Q * rhoBarStar p x / rhoBar p x ^ 2

def A10 (x : Fin 2 → ℝ) : ℂ :=
  I * ↑p.Q * rhoBar p x / rhoBarStar p x ^ 2

/-! ### X and A as matrices, built from entries -/

def X' (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![X00 p x, X01 p x; X10 p x, X11 p x]

def A' (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, A01 p x; A10 p x, 0]

/-! ### X' = X, A' = A -/

theorem X'_eq_X (x : Fin 2 → ℝ) : X' p x = X p x := by
  simp [X', X, X00, X01, X10, X11]

theorem A'_eq_A (x : Fin 2 → ℝ) : A' p x = A p x := by
  simp [A', A, A01, A10]

/-! ### Entry access from X' is definitional -/

@[simp] theorem X'_00 (x : Fin 2 → ℝ) : X' p x 0 0 = X00 p x := by simp [X']
@[simp] theorem X'_01 (x : Fin 2 → ℝ) : X' p x 0 1 = X01 p x := by simp [X']
@[simp] theorem X'_10 (x : Fin 2 → ℝ) : X' p x 1 0 = X10 p x := by simp [X']
@[simp] theorem X'_11 (x : Fin 2 → ℝ) : X' p x 1 1 = X11 p x := by simp [X']

/-! ### Slice functions for X entries are lightweight -/

-- X₀₀ along r: only √Δ and ρ̄ depend on r
theorem X00_r_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X00 p (Function.update x 0 u) =
    ↑p.Q * (↑(Real.sqrt (Del p u)) + ↑p.a * ↑(Real.sin (x 1))) /
      rhoBar p (Function.update x 0 u) := by
  simp [X00]

-- X₀₀ along θ: only sinθ and ρ̄ depend on θ
theorem X00_th_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X00 p (Function.update x 1 u) =
    ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin u)) /
      rhoBar p (Function.update x 1 u) := by
  simp [X00]

-- X₁₁ along r
theorem X11_r_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X11 p (Function.update x 0 u) =
    ↑p.Q * (↑(Real.sqrt (Del p u)) - ↑p.a * ↑(Real.sin (x 1))) /
      rhoBarStar p (Function.update x 0 u) := by
  simp [X11]

-- X₁₁ along θ
theorem X11_th_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X11 p (Function.update x 1 u) =
    ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin u)) /
      rhoBarStar p (Function.update x 1 u) := by
  simp [X11]

-- X₀₁ along r
theorem X01_r_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X01 p (Function.update x 0 u) =
    -I * ↑p.M + I * ↑(p.Q ^ 2) * (rhoBar p (Function.update x 0 u))⁻¹ := by
  simp [X01]; ring

-- X₀₁ along θ
theorem X01_th_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X01 p (Function.update x 1 u) =
    -I * ↑p.M + I * ↑(p.Q ^ 2) * (rhoBar p (Function.update x 1 u))⁻¹ := by
  simp [X01]; ring

-- X₁₀ along r
theorem X10_r_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X10 p (Function.update x 0 u) =
    I * ↑p.M - I * ↑(p.Q ^ 2) * (rhoBarStar p (Function.update x 0 u))⁻¹ := by
  simp [X10]; ring

-- X₁₀ along θ
theorem X10_th_eq (x : Fin 2 → ℝ) (u : ℝ) :
    X10 p (Function.update x 1 u) =
    I * ↑p.M - I * ↑(p.Q ^ 2) * (rhoBarStar p (Function.update x 1 u))⁻¹ := by
  simp [X10]; ring

end Hintz2026

end
