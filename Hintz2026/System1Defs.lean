import Hintz2026.System4Defs

-- Hintz 2026 - System (1): the first-order positive/negative spin systems, and the chiral
-- variables (3).  Source: Hintz, arXiv:2609.33661v1, eqs (1a)-(1d), the negative-spin replacement
-- rules, and eq. (3).  Transcribed from notes/HINTZ_EQUATIONS_TRANSCRIPT.md.
--
-- Coordinates x : Fin 2 -> ℝ with x 0 = r, x 1 = θ.  Fields are ℂ-valued functions on ℝ².
-- The mode parameters are ω, m ∈ ℝ (the paper: ω ∈ ℝ, m ∈ ℤ).

open Complex
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-! ### Scalar coefficients -/

/-- Q̂ = −aω sinθ + m / sinθ. -/
def Qhat (om mm : ℝ) (θ : ℝ) : ℝ := -p.a * om * Real.sin θ + mm / Real.sin θ

/-- cot θ as a real function. -/
def cotR (θ : ℝ) : ℝ := Real.cos θ / Real.sin θ

/-- F± = 3(M − Q²/ρ̄) ± Q² ρ̄* / ρ̄². -/
def Fplus (x : Fin 2 -> ℝ) : ℂ :=
  3 * (↑p.M - ↑(p.Q ^ 2) / rhoBar p x) + ↑(p.Q ^ 2) * rhoBarStar p x / rhoBar p x ^ 2
def Fminus (x : Fin 2 -> ℝ) : ℂ :=
  3 * (↑p.M - ↑(p.Q ^ 2) / rhoBar p x) - ↑(p.Q ^ 2) * rhoBarStar p x / rhoBar p x ^ 2

/-! ### NP-type first-order operators (applied to a field f at x) -/

/-- 𝒟_j f = ∂_r f + (iK/Δ + jΔ'/Δ) f. -/
def Dop (j : ℝ) (om mm : ℝ) (f : (Fin 2 -> ℝ) -> ℂ) (x : Fin 2 -> ℝ) : ℂ :=
  cpd 0 f x + (I * ↑(Kfreq p om mm (x 0)) / ↑(Del p (x 0)) + ↑j * ↑(Del' p (x 0)) / ↑(Del p (x 0))) * f x

/-- 𝒟_j† f = ∂_r f + (−iK/Δ + jΔ'/Δ) f. -/
def DopDag (j : ℝ) (om mm : ℝ) (f : (Fin 2 -> ℝ) -> ℂ) (x : Fin 2 -> ℝ) : ℂ :=
  cpd 0 f x + (-(I * ↑(Kfreq p om mm (x 0)) / ↑(Del p (x 0))) + ↑j * ↑(Del' p (x 0)) / ↑(Del p (x 0))) * f x

/-- ℒ_j f = ∂_θ f + (Q̂ + j cot θ) f. -/
def Lop (j : ℝ) (om mm : ℝ) (f : (Fin 2 -> ℝ) -> ℂ) (x : Fin 2 -> ℝ) : ℂ :=
  cpd 1 f x + (↑(Qhat p om mm (x 1)) + ↑j * ↑(cotR (x 1))) * f x

/-- ℒ_j† f = ∂_θ f + (−Q̂ + j cot θ) f. -/
def LopDag (j : ℝ) (om mm : ℝ) (f : (Fin 2 -> ℝ) -> ℂ) (x : Fin 2 -> ℝ) : ℂ :=
  cpd 1 f x + (-↑(Qhat p om mm (x 1)) + ↑j * ↑(cotR (x 1))) * f x

/-- 3ia sinθ / ρ̄*. -/
def threeIaSin (x : Fin 2 -> ℝ) : ℂ := 3 * I * ↑(p.a * Real.sin (x 1)) / rhoBarStar p x
/-- 3 / ρ̄*. -/
def threeOverRhoStar (x : Fin 2 -> ℝ) : ℂ := 3 / rhoBarStar p x

/-! ### Positive-spin system (1a)-(1d): residuals (LHS − RHS) -/

/-- Fields of the positive-spin system: ψ₂, ψ₁, k, s. -/
structure PosFields where
  psi2 : (Fin 2 -> ℝ) -> ℂ
  psi1 : (Fin 2 -> ℝ) -> ℂ
  k    : (Fin 2 -> ℝ) -> ℂ
  s    : (Fin 2 -> ℝ) -> ℂ

/-- (1a): (ℒ₂ − 3ia sinθ/ρ̄*) ψ₂ − (𝒟₀ + 3/ρ̄*) ψ₁ + 2k F₊ = 0. -/
def res1a (om mm : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : ℂ :=
  (Lop p 2 om mm F.psi2 x - threeIaSin p x * F.psi2 x)
  - (Dop p 0 om mm F.psi1 x + threeOverRhoStar p x * F.psi1 x)
  + 2 * F.k x * Fplus p x

/-- (1b): Δ(𝒟₂† − 3/ρ̄*) ψ₂ + (ℒ₋₁† + 3ia sinθ/ρ̄*) ψ₁ − 2s F₋ = 0. -/
def res1b (om mm : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : ℂ :=
  ↑(Del p (x 0)) * (DopDag p 2 om mm F.psi2 x - threeOverRhoStar p x * F.psi2 x)
  + (LopDag p (-1) om mm F.psi1 x + threeIaSin p x * F.psi1 x)
  - 2 * F.s x * Fminus p x

/-- (1c): (𝒟₀ + 3/ρ̄*) s − (ℒ₋₁† + 3ia sinθ/ρ̄*) k − (ρ̄/ρ̄*²) ψ₂ = 0. -/
def res1c (om mm : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : ℂ :=
  (Dop p 0 om mm F.s x + threeOverRhoStar p x * F.s x)
  - (LopDag p (-1) om mm F.k x + threeIaSin p x * F.k x)
  - rhoBar p x / rhoBarStar p x ^ 2 * F.psi2 x

/-- (1d): Δ(𝒟₂† − 3/ρ̄*) k + (ℒ₂ − 3ia sinθ/ρ̄*) s − (2ρ̄/ρ̄*²) ψ₁ = 0. -/
def res1d (om mm : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : ℂ :=
  ↑(Del p (x 0)) * (DopDag p 2 om mm F.k x - threeOverRhoStar p x * F.k x)
  + (Lop p 2 om mm F.s x - threeIaSin p x * F.s x)
  - 2 * rhoBar p x / rhoBarStar p x ^ 2 * F.psi1 x

/-! ### Negative-spin system: fields ψ₋₂, ψ₋₁, n, ℓ and the replacement rules -/

structure NegFields where
  psim2 : (Fin 2 -> ℝ) -> ℂ
  psim1 : (Fin 2 -> ℝ) -> ℂ
  n     : (Fin 2 -> ℝ) -> ℂ
  l     : (Fin 2 -> ℝ) -> ℂ

-- Replacements: ψ₁ → −ψ₋₁, ψ₂ → ψ₋₂, k → −n, s → ℓ, ℒ₋₁† → ℒ₋₁, ℒ₂ → ℒ₂†,
-- (𝒟₀ + 3/ρ̄*) → Δ(𝒟₋₁† + 3/ρ̄*),  Δ(𝒟₂† − 3/ρ̄*) → (𝒟₀ − 3/ρ̄*).

/-- (1a)⁻: (ℒ₂† − 3ia sinθ/ρ̄*) ψ₋₂ − Δ(𝒟₋₁† + 3/ρ̄*)(−ψ₋₁) + 2(−n) F₊ = 0. -/
def res1aN (om mm : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : ℂ :=
  (LopDag p 2 om mm G.psim2 x - threeIaSin p x * G.psim2 x)
  - ↑(Del p (x 0)) * (DopDag p (-1) om mm (fun z => -G.psim1 z) x + threeOverRhoStar p x * (-G.psim1 x))
  + 2 * (-G.n x) * Fplus p x

/-- (1b)⁻: (𝒟₀ − 3/ρ̄*) ψ₋₂ + (ℒ₋₁ + 3ia sinθ/ρ̄*)(−ψ₋₁) − 2ℓ F₋ = 0. -/
def res1bN (om mm : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : ℂ :=
  (Dop p 0 om mm G.psim2 x - threeOverRhoStar p x * G.psim2 x)
  + (Lop p (-1) om mm (fun z => -G.psim1 z) x + threeIaSin p x * (-G.psim1 x))
  - 2 * G.l x * Fminus p x

/-- (1c)⁻: Δ(𝒟₋₁† + 3/ρ̄*) ℓ − (ℒ₋₁ + 3ia sinθ/ρ̄*)(−n) − (ρ̄/ρ̄*²) ψ₋₂ = 0. -/
def res1cN (om mm : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : ℂ :=
  ↑(Del p (x 0)) * (DopDag p (-1) om mm G.l x + threeOverRhoStar p x * G.l x)
  - (Lop p (-1) om mm (fun z => -G.n z) x + threeIaSin p x * (-G.n x))
  - rhoBar p x / rhoBarStar p x ^ 2 * G.psim2 x

/-- (1d)⁻: (𝒟₀ − 3/ρ̄*)(−n) + (ℒ₂† − 3ia sinθ/ρ̄*) ℓ − (2ρ̄/ρ̄*²)(−ψ₋₁) = 0. -/
def res1dN (om mm : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : ℂ :=
  (Dop p 0 om mm (fun z => -G.n z) x - threeOverRhoStar p x * (-G.n x))
  + (LopDag p 2 om mm G.l x - threeIaSin p x * G.l x)
  - 2 * rhoBar p x / rhoBarStar p x ^ 2 * (-G.psim1 x)

/-! ### Chiral variables, eq. (3) -/

/-- Δ^{5/4} √(sin θ) as a real prefactor. -/
def prePos (x : Fin 2 -> ℝ) : ℝ := Real.rpow (Del p (x 0)) (5/4) * Real.sqrt (Real.sin (x 1))
/-- Δ^{-3/4} √(sin θ). -/
def preNeg (x : Fin 2 -> ℝ) : ℝ := Real.rpow (Del p (x 0)) (-3/4) * Real.sqrt (Real.sin (x 1))

/-- y±^(+) = Δ^{5/4}√sinθ ( ψ₂ ± iΔ^{-1/2}ψ₁ , −2Q(k ± iΔ^{-1/2}s) ); `e = ±1`. -/
def yPos (e : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : Fin 2 -> ℂ :=
  ![ ↑(prePos p x) * (F.psi2 x + ↑e * I * F.psi1 x / ↑(Real.sqrt (Del p (x 0)))),
     ↑(prePos p x) * (-2 * ↑p.Q * (F.k x + ↑e * I * F.s x / ↑(Real.sqrt (Del p (x 0))))) ]

/-- y±^(−) = Δ^{-3/4}√sinθ ( ψ₋₂ ∓ iΔ^{1/2}ψ₋₁ , 2Q(n ∓ iΔ^{1/2}ℓ) ); `e = ±1`. -/
def yNeg (e : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : Fin 2 -> ℂ :=
  ![ ↑(preNeg p x) * (G.psim2 x - ↑e * I * ↑(Real.sqrt (Del p (x 0))) * G.psim1 x),
     ↑(preNeg p x) * (2 * ↑p.Q * (G.n x - ↑e * I * ↑(Real.sqrt (Del p (x 0))) * G.l x)) ]

end Hintz2026

end
