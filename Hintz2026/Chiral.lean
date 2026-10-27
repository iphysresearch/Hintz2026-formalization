import Hintz2026.Prefactors
import Hintz2026.FieldInterface

-- Hintz 2026 - Chiralisation, Stage A: D± of the prefactors Δ^{5/4}√sinθ and Δ^{-3/4}√sinθ.
--   Dm(prePos) = prePos · λ,  λ = (5/4) Δ'/√Δ − (i/2) cot θ   (and the three analogues)

open Complex Function
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

theorem prePos_pos {x : Fin 2 -> ℝ} (hx : x ∈ U p) : 0 < prePos p x := by
  unfold prePos
  exact mul_pos (Real.rpow_pos_of_pos (Del_pos p hx.1) _) (Real.sqrt_pos.mpr (sin_pos_of_mem p hx))

theorem preNeg_pos {x : Fin 2 -> ℝ} (hx : x ∈ U p) : 0 < preNeg p x := by
  unfold preNeg
  exact mul_pos (Real.rpow_pos_of_pos (Del_pos p hx.1) _) (Real.sqrt_pos.mpr (sin_pos_of_mem p hx))

/-! ### cpd of the prefactors -/

theorem cpd0_prePos {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (↑(prePos p z) : ℂ)) x =
      ↑((5/4) * Real.rpow (Del p (x 0)) (5/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1))) := by
  unfold cpd
  exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_prePos_r p x (Del_pos p hx.1))).deriv

theorem cpd1_prePos {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => (↑(prePos p z) : ℂ)) x =
      ↑(Real.rpow (Del p (x 0)) (5/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) := by
  unfold cpd
  exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 1) (hasDerivAt_prePos_th p x (sin_pos_of_mem p hx))).deriv

theorem cpd0_preNeg {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (↑(preNeg p z) : ℂ)) x =
      ↑((-3/4) * Real.rpow (Del p (x 0)) (-3/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1))) := by
  unfold cpd
  exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_preNeg_r p x (Del_pos p hx.1))).deriv

theorem cpd1_preNeg {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => (↑(preNeg p z) : ℂ)) x =
      ↑(Real.rpow (Del p (x 0)) (-3/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) := by
  unfold cpd
  exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 1) (hasDerivAt_preNeg_th p x (sin_pos_of_mem p hx))).deriv

/-! ### The logarithmic D±-derivatives of the prefactors -/

def lamPosM (x : Fin 2 -> ℝ) : ℂ := ↑(5/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) - I / 2 * ↑(cotR (x 1))
def lamPosP (x : Fin 2 -> ℝ) : ℂ := ↑(5/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) + I / 2 * ↑(cotR (x 1))
def lamNegM (x : Fin 2 -> ℝ) : ℂ := ↑(-3/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) - I / 2 * ↑(cotR (x 1))
def lamNegP (x : Fin 2 -> ℝ) : ℂ := ↑(-3/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) + I / 2 * ↑(cotR (x 1))

-- Real algebra isolated from rpow: the r-part identity.
--   √Δ · (c · Δ^{q-1} · Δ' · t) = (Δ^q · t) · (c · Δ' / √Δ)   with Δ = (√Δ)², Δ^{q-1} = Δ^q / Δ
theorem pre_r_key (q c : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Real.sqrt (Del p (x 0)) * (c * Real.rpow (Del p (x 0)) (q - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1)))
      = (Real.rpow (Del p (x 0)) q * Real.sqrt (Real.sin (x 1))) * (c * Del' p (x 0) / Real.sqrt (Del p (x 0))) := by
  have hD := Del_pos p hx.1
  have hsD : Real.sqrt (Del p (x 0)) ≠ 0 := (Real.sqrt_pos.mpr hD).ne'
  have hs2 : Real.sqrt (Del p (x 0)) ^ 2 = Del p (x 0) := Real.sq_sqrt hD.le
  have hP1 : Del p (x 0) ^ (q - 1) = Del p (x 0) ^ q / Del p (x 0) := Real.rpow_sub_one hD.ne' _
  simp only [Real.rpow_eq_pow]
  rw [hP1]
  generalize Del p (x 0) ^ q = P
  generalize hsd : Real.sqrt (Del p (x 0)) = s at hs2 hsD ⊢
  generalize Del p (x 0) = D at hs2 ⊢
  subst hs2
  field_simp
  try ring

-- the θ-part identity:  Δ^q · (cos/(2√sin)) = (Δ^q · √sin) · (cot/2)   with sin = (√sin)²
theorem pre_th_key (q : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Real.rpow (Del p (x 0)) q * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))
      = (Real.rpow (Del p (x 0)) q * Real.sqrt (Real.sin (x 1))) * (cotR (x 1) / 2) := by
  have hs := sin_pos_of_mem p hx
  have ht : Real.sqrt (Real.sin (x 1)) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have ht2 : Real.sqrt (Real.sin (x 1)) ^ 2 = Real.sin (x 1) := Real.sq_sqrt hs.le
  unfold cotR
  generalize Real.rpow (Del p (x 0)) q = P
  generalize htd : Real.sqrt (Real.sin (x 1)) = t at ht2 ht ⊢
  generalize Real.sin (x 1) = S at ht2 ⊢
  subst ht2
  field_simp
  try ring

theorem Dm_prePos {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (↑(prePos p z) : ℂ)) x = ↑(prePos p x) * lamPosM p x := by
  unfold Dm lamPosM
  rw [cpd0_prePos p hx, cpd1_prePos p hx]
  have e1 : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑(5/4 * Real.rpow (Del p (x 0)) (5/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1)))
      = ↑(prePos p x) * ↑(5/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) := by
    rw [← Complex.ofReal_mul, pre_r_key p (5/4) (5/4) hx, Complex.ofReal_mul]; rfl
  have e2 : (↑(Real.rpow (Del p (x 0)) (5/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) : ℂ)
      = ↑(prePos p x) * ↑(cotR (x 1) / 2) := by
    rw [pre_th_key p (5/4) hx, Complex.ofReal_mul]; rfl
  rw [e1, e2]; push_cast; ring

theorem Dp_prePos {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Dp p (fun z => (↑(prePos p z) : ℂ)) x = ↑(prePos p x) * lamPosP p x := by
  unfold Dp lamPosP
  rw [cpd0_prePos p hx, cpd1_prePos p hx]
  have e1 : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑(5/4 * Real.rpow (Del p (x 0)) (5/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1)))
      = ↑(prePos p x) * ↑(5/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) := by
    rw [← Complex.ofReal_mul, pre_r_key p (5/4) (5/4) hx, Complex.ofReal_mul]; rfl
  have e2 : (↑(Real.rpow (Del p (x 0)) (5/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) : ℂ)
      = ↑(prePos p x) * ↑(cotR (x 1) / 2) := by
    rw [pre_th_key p (5/4) hx, Complex.ofReal_mul]; rfl
  rw [e1, e2]; push_cast; ring

theorem Dm_preNeg {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (↑(preNeg p z) : ℂ)) x = ↑(preNeg p x) * lamNegM p x := by
  unfold Dm lamNegM
  rw [cpd0_preNeg p hx, cpd1_preNeg p hx]
  have e1 : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑(-3/4 * Real.rpow (Del p (x 0)) (-3/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1)))
      = ↑(preNeg p x) * ↑(-3/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) := by
    rw [← Complex.ofReal_mul, pre_r_key p (-3/4) (-3/4) hx, Complex.ofReal_mul]; rfl
  have e2 : (↑(Real.rpow (Del p (x 0)) (-3/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) : ℂ)
      = ↑(preNeg p x) * ↑(cotR (x 1) / 2) := by
    rw [pre_th_key p (-3/4) hx, Complex.ofReal_mul]; rfl
  rw [e1, e2]; push_cast; ring

theorem Dp_preNeg {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Dp p (fun z => (↑(preNeg p z) : ℂ)) x = ↑(preNeg p x) * lamNegP p x := by
  unfold Dp lamNegP
  rw [cpd0_preNeg p hx, cpd1_preNeg p hx]
  have e1 : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑(-3/4 * Real.rpow (Del p (x 0)) (-3/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1)))
      = ↑(preNeg p x) * ↑(-3/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) := by
    rw [← Complex.ofReal_mul, pre_r_key p (-3/4) (-3/4) hx, Complex.ofReal_mul]; rfl
  have e2 : (↑(Real.rpow (Del p (x 0)) (-3/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) : ℂ)
      = ↑(preNeg p x) * ↑(cotR (x 1) / 2) := by
    rw [pre_th_key p (-3/4) hx, Complex.ofReal_mul]; rfl
  rw [e1, e2]; push_cast; ring

/-! ### Slice differentiability of the coerced prefactors -/

theorem diff_prePos_slice {x : Fin 2 -> ℝ} (hx : x ∈ U p) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => (↑(prePos p (update x k u)) : ℂ)) (x k) := by
  fin_cases k
  · exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_prePos_r p x (Del_pos p hx.1))).differentiableAt
  · exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 1) (hasDerivAt_prePos_th p x (sin_pos_of_mem p hx))).differentiableAt

theorem diff_preNeg_slice {x : Fin 2 -> ℝ} (hx : x ∈ U p) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => (↑(preNeg p (update x k u)) : ℂ)) (x k) := by
  fin_cases k
  · exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_preNeg_r p x (Del_pos p hx.1))).differentiableAt
  · exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 1) (hasDerivAt_preNeg_th p x (sin_pos_of_mem p hx))).differentiableAt

/-! ### D± of prefactor × field -/

theorem Dm_prePos_mul {x : Fin 2 -> ℝ} (hx : x ∈ U p) (g : (Fin 2 -> ℝ) -> ℂ)
    (hg : ∀ k, DifferentiableAt ℝ (fun u => g (update x k u)) (x k)) :
    Dm p (fun z => ↑(prePos p z) * g z) x = ↑(prePos p x) * (lamPosM p x * g x + Dm p g x) := by
  rw [Dm_mul p _ g x (diff_prePos_slice p hx 0) (hg 0) (diff_prePos_slice p hx 1) (hg 1), Dm_prePos p hx]; ring

theorem Dp_prePos_mul {x : Fin 2 -> ℝ} (hx : x ∈ U p) (g : (Fin 2 -> ℝ) -> ℂ)
    (hg : ∀ k, DifferentiableAt ℝ (fun u => g (update x k u)) (x k)) :
    Dp p (fun z => ↑(prePos p z) * g z) x = ↑(prePos p x) * (lamPosP p x * g x + Dp p g x) := by
  rw [Dp_mul p _ g x (diff_prePos_slice p hx 0) (hg 0) (diff_prePos_slice p hx 1) (hg 1), Dp_prePos p hx]; ring

theorem Dm_preNeg_mul {x : Fin 2 -> ℝ} (hx : x ∈ U p) (g : (Fin 2 -> ℝ) -> ℂ)
    (hg : ∀ k, DifferentiableAt ℝ (fun u => g (update x k u)) (x k)) :
    Dm p (fun z => ↑(preNeg p z) * g z) x = ↑(preNeg p x) * (lamNegM p x * g x + Dm p g x) := by
  rw [Dm_mul p _ g x (diff_preNeg_slice p hx 0) (hg 0) (diff_preNeg_slice p hx 1) (hg 1), Dm_preNeg p hx]; ring

theorem Dp_preNeg_mul {x : Fin 2 -> ℝ} (hx : x ∈ U p) (g : (Fin 2 -> ℝ) -> ℂ)
    (hg : ∀ k, DifferentiableAt ℝ (fun u => g (update x k u)) (x k)) :
    Dp p (fun z => ↑(preNeg p z) * g z) x = ↑(preNeg p x) * (lamNegP p x * g x + Dp p g x) := by
  rw [Dp_mul p _ g x (diff_preNeg_slice p hx 0) (hg 0) (diff_preNeg_slice p hx 1) (hg 1), Dp_preNeg p hx]; ring

end Hintz2026

end
