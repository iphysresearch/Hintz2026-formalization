import Hintz2026.Chiral

-- Hintz 2026 - Chiralisation, Stage B: the residual identity relating system (4) for the chiral
-- variables (3) to the residuals of system (1).  Positive spin, ς = +1:
--   y₊ = prePos · g₊,  y₋ = prePos · g₋,   g± = ( ψ₂ ± i ψ₁/√Δ , −2Q (k ± i s/√Δ) ).
-- Claim (component form):
--   Dm(y₊) − A y₊ − (c I − B) y₋  = prePos · W₊ · (res1a, res1b, res1c, res1d)
--   Dp(y₋) + A y₋ − (c I + B) y₊  = prePos · W₋ · (res1a, res1b, res1c, res1d)
-- with W₊ = [[−i, 1/√Δ, 0, 0], [0, 0, −2Q·i, −2Q/√Δ]], W₋ = [[i, 1/√Δ, 0, 0], [0, 0, 2Q·i, −2Q/√Δ]].
-- (W is obtained by matching the first-order terms; the zeroth-order match is the content proved here.)

set_option maxHeartbeats 40000000
set_option maxRecDepth 100000

open Complex Function Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-- normalised chiral components, positive spin; `e = ±1`. -/
def g1 (e : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : ℂ :=
  F.psi2 x + ↑e * I * F.psi1 x / ↑(Real.sqrt (Del p (x 0)))
def g2 (e : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : ℂ :=
  -2 * ↑p.Q * (F.k x + ↑e * I * F.s x / ↑(Real.sqrt (Del p (x 0))))

theorem yPos_0 (e : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : yPos p e F x 0 = ↑(prePos p x) * g1 p e F x := by
  simp [yPos, g1]
theorem yPos_1 (e : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : yPos p e F x 1 = ↑(prePos p x) * g2 p e F x := by
  simp [yPos, g2]

/-! ### D± of 1/√Δ and of f/√Δ -/

theorem cpd0_inv_sqrtDel {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (↑(Real.sqrt (Del p (z 0))) : ℂ)⁻¹) x
      = -(↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) : ℂ) / (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 2 := by
  unfold cpd
  have hD := Del_pos p hx.1
  have h1 : HasDerivAt (fun u => (↑(Real.sqrt (Del p u)) : ℂ)) (↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) (x 0) :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_sqrtDel_r p hD)
  have hne : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have h2 := h1.inv hne
  refine (h2.congr_of_eventuallyEq ?_).deriv
  filter_upwards with u; simp [Function.update, show (1 : Fin 2) ≠ 0 from by decide]

theorem cpd1_inv_sqrtDel (x : Fin 2 -> ℝ) :
    cpd 1 (fun z => (↑(Real.sqrt (Del p (z 0))) : ℂ)⁻¹) x = 0 := by
  unfold cpd
  have : (fun u => (↑(Real.sqrt (Del p ((update x 1 u) 0))) : ℂ)⁻¹) = fun _ => (↑(Real.sqrt (Del p (x 0))) : ℂ)⁻¹ := by
    funext u; simp [Function.update, show (0 : Fin 2) ≠ 1 from by decide]
  rw [this, deriv_const]

theorem diff_inv_sqrtDel_slice {x : Fin 2 -> ℝ} (hx : x ∈ U p) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => (↑(Real.sqrt (Del p ((update x k u) 0))) : ℂ)⁻¹) (x k) := by
  fin_cases k
  · have hD := Del_pos p hx.1
    have h1 : HasDerivAt (fun u => (↑(Real.sqrt (Del p u)) : ℂ)) (↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) (x 0) :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_sqrtDel_r p hD)
    have hne : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
    refine ((h1.inv hne).congr_of_eventuallyEq ?_).differentiableAt
    filter_upwards with u; simp [Function.update]
  · show DifferentiableAt ℝ (fun u => (↑(Real.sqrt (Del p ((update x 1 u) 0))) : ℂ)⁻¹) (x 1)
    have : (fun u => (↑(Real.sqrt (Del p ((update x 1 u) 0))) : ℂ)⁻¹) = fun _ => (↑(Real.sqrt (Del p (x 0))) : ℂ)⁻¹ := by
      funext u; simp [Function.update]
    rw [this]; exact differentiableAt_const _

/-- Dm(f/√Δ) = Dm f /√Δ − f · Δ'/(2Δ). -/
theorem Dm_div_sqrtDel {x : Fin 2 -> ℝ} (hx : x ∈ U p) (f : (Fin 2 -> ℝ) -> ℂ)
    (hf : ∀ k, DifferentiableAt ℝ (fun u => f (update x k u)) (x k)) :
    Dm p (fun z => f z / ↑(Real.sqrt (Del p (z 0)))) x
      = Dm p f x / ↑(Real.sqrt (Del p (x 0))) - f x * ↑(Del' p (x 0)) / (2 * ↑(Del p (x 0))) := by
  have hD := Del_pos p hx.1
  have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have hDc : (↑(Del p (x 0)) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 2 = ↑(Del p (x 0)) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hD.le]
  have e : (fun z => f z / ↑(Real.sqrt (Del p (z 0)))) = fun z => f z * (↑(Real.sqrt (Del p (z 0))) : ℂ)⁻¹ := by
    funext z; rw [div_eq_mul_inv]
  rw [e, Dm_mul p f _ x (hf 0) (diff_inv_sqrtDel_slice p hx 0) (hf 1) (diff_inv_sqrtDel_slice p hx 1)]
  unfold Dm
  rw [cpd0_inv_sqrtDel p hx, cpd1_inv_sqrtDel]
  rw [Del'_eq]
  field_simp
  push_cast
  ring_nf
  rw [← hsq]
  field_simp
  ring

theorem Dp_div_sqrtDel {x : Fin 2 -> ℝ} (hx : x ∈ U p) (f : (Fin 2 -> ℝ) -> ℂ)
    (hf : ∀ k, DifferentiableAt ℝ (fun u => f (update x k u)) (x k)) :
    Dp p (fun z => f z / ↑(Real.sqrt (Del p (z 0)))) x
      = Dp p f x / ↑(Real.sqrt (Del p (x 0))) - f x * ↑(Del' p (x 0)) / (2 * ↑(Del p (x 0))) := by
  have hD := Del_pos p hx.1
  have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have hDc : (↑(Del p (x 0)) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 2 = ↑(Del p (x 0)) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hD.le]
  have e : (fun z => f z / ↑(Real.sqrt (Del p (z 0)))) = fun z => f z * (↑(Real.sqrt (Del p (z 0))) : ℂ)⁻¹ := by
    funext z; rw [div_eq_mul_inv]
  rw [e, Dp_mul p f _ x (hf 0) (diff_inv_sqrtDel_slice p hx 0) (hf 1) (diff_inv_sqrtDel_slice p hx 1)]
  unfold Dp
  rw [cpd0_inv_sqrtDel p hx, cpd1_inv_sqrtDel]
  rw [Del'_eq]
  field_simp
  push_cast
  ring_nf
  rw [← hsq]
  field_simp
  ring

/-! ### constant multiples and sums -/

theorem Dm_const_mul (c : ℂ) (f : (Fin 2 -> ℝ) -> ℂ) (x : Fin 2 -> ℝ) :
    Dm p (fun z => c * f z) x = c * Dm p f x := by
  unfold Dm cpd; simp only [deriv_const_mul_field]; ring

theorem Dp_const_mul (c : ℂ) (f : (Fin 2 -> ℝ) -> ℂ) (x : Fin 2 -> ℝ) :
    Dp p (fun z => c * f z) x = c * Dp p f x := by
  unfold Dp cpd; simp only [deriv_const_mul_field]; ring

theorem diff_div_sqrtDel_slice {x : Fin 2 -> ℝ} (hx : x ∈ U p) (f : (Fin 2 -> ℝ) -> ℂ)
    (hf : ∀ k, DifferentiableAt ℝ (fun u => f (update x k u)) (x k)) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => f (update x k u) / ↑(Real.sqrt (Del p ((update x k u) 0)))) (x k) := by
  simp only [div_eq_mul_inv]
  exact (hf k).mul (diff_inv_sqrtDel_slice p hx k)

theorem diff_const_mul_slice (c : ℂ) {x : Fin 2 -> ℝ} (f : (Fin 2 -> ℝ) -> ℂ)
    (hf : ∀ k, DifferentiableAt ℝ (fun u => f (update x k u)) (x k)) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => c * f (update x k u)) (x k) := (hf k).const_mul c

/-! ### D± of the normalised chiral components -/

/-- Differentiability data for the four positive-spin fields at x. -/
structure PosDiff (F : PosFields) (x : Fin 2 -> ℝ) : Prop where
  psi2 : ∀ k, DifferentiableAt ℝ (fun u => F.psi2 (update x k u)) (x k)
  psi1 : ∀ k, DifferentiableAt ℝ (fun u => F.psi1 (update x k u)) (x k)
  k    : ∀ k, DifferentiableAt ℝ (fun u => F.k (update x k u)) (x k)
  s    : ∀ k, DifferentiableAt ℝ (fun u => F.s (update x k u)) (x k)

theorem g1_eq (e : ℝ) (F : PosFields) :
    g1 p e F = fun z => F.psi2 z + (↑e * I) * (F.psi1 z / ↑(Real.sqrt (Del p (z 0)))) := by
  funext z; unfold g1; ring

theorem g2_eq (e : ℝ) (F : PosFields) :
    g2 p e F = fun z => (-2 * ↑p.Q) * (F.k z + (↑e * I) * (F.s z / ↑(Real.sqrt (Del p (z 0))))) := by
  funext z; unfold g2; ring

theorem diff_g1_slice (e : ℝ) {F : PosFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hF : PosDiff F x) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => g1 p e F (update x k u)) (x k) := by
  rw [g1_eq]
  exact (hF.psi2 k).add (((diff_div_sqrtDel_slice p hx F.psi1 hF.psi1 k)).const_mul _)

theorem diff_g2_slice (e : ℝ) {F : PosFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hF : PosDiff F x) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => g2 p e F (update x k u)) (x k) := by
  rw [g2_eq]
  exact ((hF.k k).add (((diff_div_sqrtDel_slice p hx F.s hF.s k)).const_mul _)).const_mul _

theorem Dm_g1 (e : ℝ) {F : PosFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hF : PosDiff F x) :
    Dm p (g1 p e F) x = Dm p F.psi2 x
      + (↑e * I) * (Dm p F.psi1 x / ↑(Real.sqrt (Del p (x 0))) - F.psi1 x * ↑(Del' p (x 0)) / (2 * ↑(Del p (x 0)))) := by
  rw [g1_eq, Dm_add p _ _ x (hF.psi2 0) (diff_const_mul_slice _ (fun z => F.psi1 z / ↑(Real.sqrt (Del p (z 0)))) (diff_div_sqrtDel_slice p hx F.psi1 hF.psi1) 0)
        (hF.psi2 1) (diff_const_mul_slice _ (fun z => F.psi1 z / ↑(Real.sqrt (Del p (z 0)))) (diff_div_sqrtDel_slice p hx F.psi1 hF.psi1) 1),
      Dm_const_mul, Dm_div_sqrtDel p hx F.psi1 hF.psi1]

theorem Dm_g2 (e : ℝ) {F : PosFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hF : PosDiff F x) :
    Dm p (g2 p e F) x = (-2 * ↑p.Q) * (Dm p F.k x
      + (↑e * I) * (Dm p F.s x / ↑(Real.sqrt (Del p (x 0))) - F.s x * ↑(Del' p (x 0)) / (2 * ↑(Del p (x 0))))) := by
  rw [g2_eq, Dm_const_mul, Dm_add p _ _ x (hF.k 0) (diff_const_mul_slice _ (fun z => F.s z / ↑(Real.sqrt (Del p (z 0)))) (diff_div_sqrtDel_slice p hx F.s hF.s) 0)
        (hF.k 1) (diff_const_mul_slice _ (fun z => F.s z / ↑(Real.sqrt (Del p (z 0)))) (diff_div_sqrtDel_slice p hx F.s hF.s) 1),
      Dm_const_mul, Dm_div_sqrtDel p hx F.s hF.s]

theorem Dp_g1 (e : ℝ) {F : PosFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hF : PosDiff F x) :
    Dp p (g1 p e F) x = Dp p F.psi2 x
      + (↑e * I) * (Dp p F.psi1 x / ↑(Real.sqrt (Del p (x 0))) - F.psi1 x * ↑(Del' p (x 0)) / (2 * ↑(Del p (x 0)))) := by
  rw [g1_eq, Dp_add p _ _ x (hF.psi2 0) (diff_const_mul_slice _ (fun z => F.psi1 z / ↑(Real.sqrt (Del p (z 0)))) (diff_div_sqrtDel_slice p hx F.psi1 hF.psi1) 0)
        (hF.psi2 1) (diff_const_mul_slice _ (fun z => F.psi1 z / ↑(Real.sqrt (Del p (z 0)))) (diff_div_sqrtDel_slice p hx F.psi1 hF.psi1) 1),
      Dp_const_mul, Dp_div_sqrtDel p hx F.psi1 hF.psi1]

theorem Dp_g2 (e : ℝ) {F : PosFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hF : PosDiff F x) :
    Dp p (g2 p e F) x = (-2 * ↑p.Q) * (Dp p F.k x
      + (↑e * I) * (Dp p F.s x / ↑(Real.sqrt (Del p (x 0))) - F.s x * ↑(Del' p (x 0)) / (2 * ↑(Del p (x 0))))) := by
  rw [g2_eq, Dp_const_mul, Dp_add p _ _ x (hF.k 0) (diff_const_mul_slice _ (fun z => F.s z / ↑(Real.sqrt (Del p (z 0)))) (diff_div_sqrtDel_slice p hx F.s hF.s) 0)
        (hF.k 1) (diff_const_mul_slice _ (fun z => F.s z / ↑(Real.sqrt (Del p (z 0)))) (diff_div_sqrtDel_slice p hx F.s hF.s) 1),
      Dp_const_mul, Dp_div_sqrtDel p hx F.s hF.s]

end Hintz2026

end
