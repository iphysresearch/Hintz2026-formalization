import Hintz2026.Transform7

/-!
# Hintz 2026 — C separates as R(r) + iΘ(θ)

Source: Hintz, arXiv:2609.33661v1, equations following (7).
-/

open Complex Matrix
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

private abbrev ofR : ℝ → ℂ := Complex.ofReal

/-! ### Radial coefficients R₀, R₁ -/

def R0coeff (ς ω m : ℝ) (r : ℝ) : ℂ :=
  ofR (3 * Del' p r / (4 * Real.sqrt (Del p r)))
  - I * ofR ς * ofR (Real.sqrt (Del p r))
    * (ofR (Kfreq p ω m r) / ofR (Del p r)
       - ofR (2 * ω * p.Q ^ 2) / ofR (p.M ^ 2 - p.Q ^ 2))

def R1coeff (ς ω : ℝ) (r : ℝ) : ℂ :=
  -ofR ς * ofR (2 * ω * p.Q * (p.M * r - p.Q ^ 2)) / ofR (p.M ^ 2 - p.Q ^ 2)
  + I * ofR (3 * p.M) / ofR (2 * p.Q)

/-! ### Angular coefficients Θ₀, Θ₁ -/

def Th0coeff (ς ω m : ℝ) (θ : ℝ) : ℝ :=
  3 / 2 * Real.cos θ / Real.sin θ
  + ς * (m / Real.sin θ
    - p.a * ω * (p.M ^ 2 + p.Q ^ 2) * Real.sin θ / (p.M ^ 2 - p.Q ^ 2))

def Th1coeff (ς ω : ℝ) (θ : ℝ) : ℝ :=
  -ς * 2 * p.a * ω * p.M * p.Q * Real.cos θ / (p.M ^ 2 - p.Q ^ 2)
  - 3 * p.M / (2 * p.Q)

/-! ### Assembled R and Θ matrices -/

def Rmat (ς ω m : ℝ) (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![R0coeff p ς ω m r, R1coeff p ς ω r;
     -R1coeff p ς ω r, R0coeff p ς ω m r]

def Thmat (ς ω m : ℝ) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![ofR (Th0coeff p ς ω m θ), ofR (Th1coeff p ς ω θ);
     ofR (Th1coeff p ς ω θ), -ofR (Th0coeff p ς ω m θ)]

/-- The claimed separated form: C^(ς) = R(r) + i·Θ(θ). -/
def Csep (ς ω m : ℝ) (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Rmat p ς ω m (x 0) + I • Thmat p ς ω m (x 1)

end Hintz2026

end
