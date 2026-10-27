import Hintz2026.XDiagDeriv

/-!
# Hintz 2026 — Assembly: D₋X = AX (eq. 6)

Assembles the entry-wise Dm_Xij identities into the matrix equation
  (of fun a b => D₋ (fun z => X z a b) x) = A x * X x.
-/

open Complex Matrix
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-! ### Bridge: X p z i j = Xij p z -/

theorem X_entry_00 (z : Fin 2 → ℝ) : X p z 0 0 = X00 p z := by
  rw [← X'_eq_X]; exact X'_00 p z
theorem X_entry_01 (z : Fin 2 → ℝ) : X p z 0 1 = X01 p z := by
  rw [← X'_eq_X]; exact X'_01 p z
theorem X_entry_10 (z : Fin 2 → ℝ) : X p z 1 0 = X10 p z := by
  rw [← X'_eq_X]; exact X'_10 p z
theorem X_entry_11 (z : Fin 2 → ℝ) : X p z 1 1 = X11 p z := by
  rw [← X'_eq_X]; exact X'_11 p z

/-! ### A' entry access -/

@[simp] theorem A'_00 (x : Fin 2 → ℝ) : A' p x 0 0 = 0 := by simp [A']
@[simp] theorem A'_01 (x : Fin 2 → ℝ) : A' p x 0 1 = A01 p x := by simp [A']
@[simp] theorem A'_10 (x : Fin 2 → ℝ) : A' p x 1 0 = A10 p x := by simp [A']
@[simp] theorem A'_11 (x : Fin 2 → ℝ) : A' p x 1 1 = 0 := by simp [A']

/-! ### Dm of X-entry functions (fun form) -/

theorem Dm_X_entry_00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => X p z 0 0) x =
    ↑p.Q * (↑p.M * rhoBarStar p x - ↑(p.Q ^ 2)) / (rhoBar p x) ^ 2 := by
  have hX : X00 p = (fun z => X p z 0 0) := by funext z; exact (X_entry_00 p z).symm
  rw [← hX]; exact Dm_X00 p hx

theorem Dm_X_entry_11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => X p z 1 1) x =
    ↑p.Q * (↑p.M * rhoBar p x - ↑(p.Q ^ 2)) / (rhoBarStar p x) ^ 2 := by
  have hX : X11 p = (fun z => X p z 1 1) := by funext z; exact (X_entry_11 p z).symm
  rw [← hX]; exact Dm_X11 p hx

/-! ### AX entry computations: (A x * X x) i j -/

theorem AX_00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (A p x * X p x) 0 0 =
    ↑p.Q * (↑p.M * rhoBarStar p x - ↑(p.Q ^ 2)) / (rhoBar p x) ^ 2 := by
  rw [← A'_eq_A, ← X'_eq_X]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, A'_00, A'_01, A'_10, A'_11,
    X'_00, X'_01, X'_10, X'_11, A01, X10]
  field_simp [rhoBar_ne_zero p hx, rhoBarStar_ne_zero p hx]
  try simp only [I_sq]
  ring

theorem AX_01 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (A p x * X p x) 0 1 =
    -I * ↑(p.Q ^ 2) * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) /
      (rhoBar p x) ^ 2 := by
  rw [← A'_eq_A, ← X'_eq_X]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, A'_00, A'_01, A'_10, A'_11,
    X'_00, X'_01, X'_10, X'_11, A01, X11]
  field_simp [rhoBar_ne_zero p hx, rhoBarStar_ne_zero p hx]
  push_cast
  ring

theorem AX_10 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (A p x * X p x) 1 0 =
    I * ↑(p.Q ^ 2) * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) /
      (rhoBarStar p x) ^ 2 := by
  rw [← A'_eq_A, ← X'_eq_X]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, A'_00, A'_01, A'_10, A'_11,
    X'_00, X'_01, X'_10, X'_11, A10, X00]
  field_simp [rhoBar_ne_zero p hx, rhoBarStar_ne_zero p hx]
  push_cast
  ring

theorem AX_11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (A p x * X p x) 1 1 =
    ↑p.Q * (↑p.M * rhoBar p x - ↑(p.Q ^ 2)) / (rhoBarStar p x) ^ 2 := by
  rw [← A'_eq_A, ← X'_eq_X]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, A'_00, A'_01, A'_10, A'_11,
    X'_00, X'_01, X'_10, X'_11, A10, X01]
  field_simp [rhoBar_ne_zero p hx, rhoBarStar_ne_zero p hx]
  try simp only [I_sq]
  ring


/-! ### Main equation: D₋X = AX -/

theorem Dminus_X_eq_AX {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (of fun a b => Dm p (fun z => X p z a b) x) = A p x * X p x := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [of_apply]
  · -- i=0,j=0: goal has ⟨0,⋯⟩,⟨0,⋯⟩, show converts to numeral form
    show Dm p (fun z => X p z 0 0) x = (A p x * X p x) 0 0
    rw [Dm_X_entry_00 p hx, AX_00 p hx]
  · -- i=0,j=1
    show Dm p (fun z => X p z 0 1) x = (A p x * X p x) 0 1
    rw [Dm_X01 p hx, AX_01 p hx]
  · -- i=1,j=0
    show Dm p (fun z => X p z 1 0) x = (A p x * X p x) 1 0
    rw [Dm_X10 p hx, AX_10 p hx]
  · -- i=1,j=1
    show Dm p (fun z => X p z 1 1) x = (A p x * X p x) 1 1
    rw [Dm_X_entry_11 p hx, AX_11 p hx]

/-! ### Companion equation: D₊(Xᴴ)⁻¹ = −A·(Xᴴ)⁻¹ (eq. 6, conjugate) -/


set_option maxHeartbeats 8000000
theorem adj_X_00 (x : Fin 2 → ℝ) : adjugate (X p x) 0 0 = X p x 1 1 := by
  unfold X; rw [adjugate_fin_two_of]; simp
theorem adj_X_01 (x : Fin 2 → ℝ) : adjugate (X p x) 0 1 = -(X p x 0 1) := by
  unfold X; rw [adjugate_fin_two_of]; simp
theorem adj_X_10 (x : Fin 2 → ℝ) : adjugate (X p x) 1 0 = -(X p x 1 0) := by
  unfold X; rw [adjugate_fin_two_of]; simp
theorem adj_X_11 (x : Fin 2 → ℝ) : adjugate (X p x) 1 1 = X p x 0 0 := by
  unfold X; rw [adjugate_fin_two_of]; simp
theorem Xinv_eq_smul (x : Fin 2 → ℝ) :
    (X p x)⁻¹ = (X p x).det⁻¹ • adjugate (X p x) := by
  simp [Matrix.inv_def, Ring.inverse_eq_inv]
theorem Xinv_00 (x : Fin 2 → ℝ) :
    (X p x)⁻¹ 0 0 = (X p x).det⁻¹ * X p x 1 1 := by
  simp [Xinv_eq_smul p, adj_X_00 p]
theorem Xinv_01 (x : Fin 2 → ℝ) :
    (X p x)⁻¹ 0 1 = (X p x).det⁻¹ * -(X p x 0 1) := by
  simp [Xinv_eq_smul p, adj_X_01 p]
theorem Xinv_10 (x : Fin 2 → ℝ) :
    (X p x)⁻¹ 1 0 = (X p x).det⁻¹ * -(X p x 1 0) := by
  simp [Xinv_eq_smul p, adj_X_10 p]
theorem Xinv_11 (x : Fin 2 → ℝ) :
    (X p x)⁻¹ 1 1 = (X p x).det⁻¹ * X p x 0 0 := by
  simp [Xinv_eq_smul p, adj_X_11 p]

-- ═══ Reuse: U membership / det / slice / HasDerivAt / cpd (all from blk_all_cpd) ═══
theorem mem_U_r {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ) (hu : rPlus p < u) :
    Function.update x 0 u ∈ U p :=
  ⟨by simp [Function.update]; exact hu, hx.2⟩
theorem mem_U_th {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ)
    (h0 : 0 < u) (h1 : u < Real.pi) : Function.update x 1 u ∈ U p := by
  constructor
  · simp [Function.update, show (0 : Fin 2) ≠ 1 from by decide]; exact hx.1
  · simp [Function.update]; exact ⟨h0, h1⟩
theorem det_r_const {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ) (hu : rPlus p < u) :
    (X p (Function.update x 0 u)).det = (X p x).det := by
  rw [det_X p (mem_U_r p hx u hu), det_X p hx]
theorem det_th_const {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ)
    (h0 : 0 < u) (h1 : u < Real.pi) :
    (X p (Function.update x 1 u)).det = (X p x).det := by
  rw [det_X p (mem_U_th p hx u h0 h1), det_X p hx]

-- Slice helpers
theorem sl00r {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ) (hu : rPlus p < u) :
    (X p (Function.update x 0 u))⁻¹ 0 0 =
      (X p x).det⁻¹ * X11 p (Function.update x 0 u) := by
  rw [Xinv_00, det_r_const p hx u hu, ← X_entry_11]
theorem sl00th {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ)
    (h0 : 0 < u) (h1 : u < Real.pi) :
    (X p (Function.update x 1 u))⁻¹ 0 0 =
      (X p x).det⁻¹ * X11 p (Function.update x 1 u) := by
  rw [Xinv_00, det_th_const p hx u h0 h1, ← X_entry_11]
theorem sl01r {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ) (hu : rPlus p < u) :
    (X p (Function.update x 0 u))⁻¹ 0 1 =
      (X p x).det⁻¹ * -(X p (Function.update x 0 u) 0 1) := by
  rw [Xinv_01, det_r_const p hx u hu]
theorem sl01th {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ)
    (h0 : 0 < u) (h1 : u < Real.pi) :
    (X p (Function.update x 1 u))⁻¹ 0 1 =
      (X p x).det⁻¹ * -(X p (Function.update x 1 u) 0 1) := by
  rw [Xinv_01, det_th_const p hx u h0 h1]
theorem sl10r {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ) (hu : rPlus p < u) :
    (X p (Function.update x 0 u))⁻¹ 1 0 =
      (X p x).det⁻¹ * -(X p (Function.update x 0 u) 1 0) := by
  rw [Xinv_10, det_r_const p hx u hu]
theorem sl10th {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ)
    (h0 : 0 < u) (h1 : u < Real.pi) :
    (X p (Function.update x 1 u))⁻¹ 1 0 =
      (X p x).det⁻¹ * -(X p (Function.update x 1 u) 1 0) := by
  rw [Xinv_10, det_th_const p hx u h0 h1]
theorem sl11r {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ) (hu : rPlus p < u) :
    (X p (Function.update x 0 u))⁻¹ 1 1 =
      (X p x).det⁻¹ * X00 p (Function.update x 0 u) := by
  rw [Xinv_11, det_r_const p hx u hu, ← X_entry_00]
theorem sl11th {x : Fin 2 → ℝ} (hx : x ∈ U p) (u : ℝ)
    (h0 : 0 < u) (h1 : u < Real.pi) :
    (X p (Function.update x 1 u))⁻¹ 1 1 =
      (X p x).det⁻¹ * X00 p (Function.update x 1 u) := by
  rw [Xinv_11, det_th_const p hx u h0 h1, ← X_entry_00]

-- HasDerivAt (same as blk_all_cpd)
theorem hd00r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 0 u))⁻¹ 0 0)
      ((X p x).det⁻¹ * ((↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBarStar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1)))) /
        (rhoBarStar p x) ^ 2)) (x 0) := by
  apply ((hasDerivAt_X11_r p x hx).const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioi_mem_nhds hx.1)
  intro u hu; dsimp only; exact sl00r p hx u (Set.mem_Ioi.mp hu)
theorem hd00th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 1 u))⁻¹ 0 0)
      ((X p x).det⁻¹ * ((-↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBarStar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) *
          (⟨0, p.a * Real.sin (x 1)⟩ : ℂ)) / (rhoBarStar p x) ^ 2)) (x 1) := by
  apply ((hasDerivAt_X11_th p x hx).const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioo_mem_nhds hx.2.1 hx.2.2)
  intro u hu; dsimp only; obtain ⟨h0, h1⟩ := Set.mem_Ioo.mp hu; exact sl00th p hx u h0 h1
theorem hd01r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 0 u))⁻¹ 0 1)
      ((X p x).det⁻¹ * -(I * ↑(p.Q ^ 2) * (-1 / (rhoBar p x) ^ 2))) (x 0) := by
  have hneg : HasDerivAt (fun u => -(X p (Function.update x 0 u) 0 1))
      (-(I * ↑(p.Q ^ 2) * (-1 / (rhoBar p x) ^ 2))) (x 0) := (hasDerivAt_X01_r p x hx).neg
  apply (hneg.const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioi_mem_nhds hx.1)
  intro u hu; dsimp only; exact sl01r p hx u (Set.mem_Ioi.mp hu)
theorem hd01th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 1 u))⁻¹ 0 1)
      ((X p x).det⁻¹ * -(I * ↑(p.Q ^ 2) * (-(⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) /
        (rhoBar p x) ^ 2))) (x 1) := by
  have hneg : HasDerivAt (fun u => -(X p (Function.update x 1 u) 0 1))
      (-(I * ↑(p.Q ^ 2) * (-(⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) / (rhoBar p x) ^ 2))) (x 1) :=
    (hasDerivAt_X01_th p x hx).neg
  apply (hneg.const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioo_mem_nhds hx.2.1 hx.2.2)
  intro u hu; dsimp only; obtain ⟨h0, h1⟩ := Set.mem_Ioo.mp hu; exact sl01th p hx u h0 h1
theorem hd10r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 0 u))⁻¹ 1 0)
      ((X p x).det⁻¹ * -(-I * ↑(p.Q ^ 2) * (-1 / (rhoBarStar p x) ^ 2))) (x 0) := by
  have hneg : HasDerivAt (fun u => -(X p (Function.update x 0 u) 1 0))
      (-(-I * ↑(p.Q ^ 2) * (-1 / (rhoBarStar p x) ^ 2))) (x 0) := (hasDerivAt_X10_r p x hx).neg
  apply (hneg.const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioi_mem_nhds hx.1)
  intro u hu; dsimp only; exact sl10r p hx u (Set.mem_Ioi.mp hu)
theorem hd10th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 1 u))⁻¹ 1 0)
      ((X p x).det⁻¹ * -(-I * ↑(p.Q ^ 2) * (-(⟨0, p.a * Real.sin (x 1)⟩ : ℂ) /
        (rhoBarStar p x) ^ 2))) (x 1) := by
  have hneg : HasDerivAt (fun u => -(X p (Function.update x 1 u) 1 0))
      (-(-I * ↑(p.Q ^ 2) * (-(⟨0, p.a * Real.sin (x 1)⟩ : ℂ) / (rhoBarStar p x) ^ 2))) (x 1) :=
    (hasDerivAt_X10_th p x hx).neg
  apply (hneg.const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioo_mem_nhds hx.2.1 hx.2.2)
  intro u hu; dsimp only; obtain ⟨h0, h1⟩ := Set.mem_Ioo.mp hu; exact sl10th p hx u h0 h1
theorem hd11r {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 0 u))⁻¹ 1 1)
      ((X p x).det⁻¹ * ((↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1)))) /
        (rhoBar p x) ^ 2)) (x 0) := by
  apply ((hasDerivAt_X00_r p x hx).const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioi_mem_nhds hx.1)
  intro u hu; dsimp only; exact sl11r p hx u (Set.mem_Ioi.mp hu)
theorem hd11th {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    HasDerivAt (fun u => (X p (Function.update x 1 u))⁻¹ 1 1)
      ((X p x).det⁻¹ * ((↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBar p x -
        ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) *
          (⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ)) / (rhoBar p x) ^ 2)) (x 1) := by
  apply ((hasDerivAt_X00_th p x hx).const_mul ((X p x).det⁻¹)).congr_of_eventuallyEq
  apply Filter.eventually_of_mem (Ioo_mem_nhds hx.2.1 hx.2.2)
  intro u hu; dsimp only; obtain ⟨h0, h1⟩ := Set.mem_Ioo.mp hu; exact sl11th p hx u h0 h1

-- cpd extraction
theorem cpd0_00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (X p z)⁻¹ 0 0) x = (X p x).det⁻¹ * ((↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBarStar p x - ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1)))) / (rhoBarStar p x) ^ 2) := (hd00r p hx).deriv
theorem cpd1_00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => (X p z)⁻¹ 0 0) x = (X p x).det⁻¹ * ((-↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBarStar p x - ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) * (⟨0, p.a * Real.sin (x 1)⟩ : ℂ)) / (rhoBarStar p x) ^ 2) := (hd00th p hx).deriv
theorem cpd0_01 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (X p z)⁻¹ 0 1) x = (X p x).det⁻¹ * -(I * ↑(p.Q ^ 2) * (-1 / (rhoBar p x) ^ 2)) := (hd01r p hx).deriv
theorem cpd1_01 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => (X p z)⁻¹ 0 1) x = (X p x).det⁻¹ * -(I * ↑(p.Q ^ 2) * (-(⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ) / (rhoBar p x) ^ 2)) := (hd01th p hx).deriv
theorem cpd0_10 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (X p z)⁻¹ 1 0) x = (X p x).det⁻¹ * -(-I * ↑(p.Q ^ 2) * (-1 / (rhoBarStar p x) ^ 2)) := (hd10r p hx).deriv
theorem cpd1_10 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => (X p z)⁻¹ 1 0) x = (X p x).det⁻¹ * -(-I * ↑(p.Q ^ 2) * (-(⟨0, p.a * Real.sin (x 1)⟩ : ℂ) / (rhoBarStar p x) ^ 2)) := (hd10th p hx).deriv
theorem cpd0_11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (X p z)⁻¹ 1 1) x = (X p x).det⁻¹ * ((↑p.Q * ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) * rhoBar p x - ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1)))) / (rhoBar p x) ^ 2) := (hd11r p hx).deriv
theorem cpd1_11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => (X p z)⁻¹ 1 1) x = (X p x).det⁻¹ * ((↑p.Q * ↑p.a * ↑(Real.cos (x 1)) * rhoBar p x - ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) * (⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ)) / (rhoBar p x) ^ 2) := (hd11th p hx).deriv

/-! ═══ Dm factoring: Dm(X⁻¹_{ij}) = ±det⁻¹ * Dm(X_{kl}) ═══ -/

-- Dm(X⁻¹)₀₀ = det⁻¹ * Dm(X11)
theorem Dm_fac_00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 0 0) x = (X p x).det⁻¹ * Dm p (X11 p) x := by
  simp only [Dm, cpd0_00 p hx, cpd1_00 p hx, cpd_X11_r' p hx, cpd_X11_th' p hx]; ring

-- Dm(X⁻¹)₀₁ = -det⁻¹ * Dm(fun z => X p z 0 1)
theorem Dm_fac_01 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 0 1) x = -(X p x).det⁻¹ * Dm p (fun z => X p z 0 1) x := by
  simp only [Dm, cpd0_01 p hx, cpd1_01 p hx, cpd_X01_r p hx, cpd_X01_th p hx]; ring

-- Dm(X⁻¹)₁₀ = -det⁻¹ * Dm(fun z => X p z 1 0)
theorem Dm_fac_10 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 1 0) x = -(X p x).det⁻¹ * Dm p (fun z => X p z 1 0) x := by
  simp only [Dm, cpd0_10 p hx, cpd1_10 p hx, cpd_X10_r p hx, cpd_X10_th p hx]; ring

-- Dm(X⁻¹)₁₁ = det⁻¹ * Dm(X00)
theorem Dm_fac_11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 1 1) x = (X p x).det⁻¹ * Dm p (X00 p) x := by
  simp only [Dm, cpd0_11 p hx, cpd1_11 p hx, cpd_X00_r' p hx, cpd_X00_th' p hx]; ring

/-! ═══ Dm(X entries) = (AX) entries ═══ -/

theorem dm_X11_AX {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (X11 p) x = (A p x * X p x) 1 1 := by
  have := congr_fun (congr_fun (Dminus_X_eq_AX p hx) 1) 1
  simp only [of_apply, ← X_entry_11] at this; exact this

theorem dm_X01_AX {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => X p z 0 1) x = (A p x * X p x) 0 1 := by
  have := congr_fun (congr_fun (Dminus_X_eq_AX p hx) 0) 1
  simp only [of_apply] at this; exact this

theorem dm_X10_AX {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => X p z 1 0) x = (A p x * X p x) 1 0 := by
  have := congr_fun (congr_fun (Dminus_X_eq_AX p hx) 1) 0
  simp only [of_apply] at this; exact this

theorem dm_X00_AX {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (X00 p) x = (A p x * X p x) 0 0 := by
  have := congr_fun (congr_fun (Dminus_X_eq_AX p hx) 0) 0
  simp only [of_apply, ← X_entry_00] at this; exact this

/-! ═══ Algebraic: -(X⁻¹*A)_{ij} = det⁻¹ * (±(AX)_{kl}) ═══ -/

theorem neg_XinvA_00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    -((X p x)⁻¹ * A p x) 0 0 = (X p x).det⁻¹ * (A p x * X p x) 1 1 := by
  have hL : ((X p x)⁻¹ * A p x) 0 0 =
      (X p x).det⁻¹ * X p x 1 1 * A p x 0 0 + (X p x).det⁻¹ * -(X p x 0 1) * A p x 1 0 := by
    rw [mul_apply, Fin.sum_univ_two, Xinv_00, Xinv_01]
  have hR : (A p x * X p x) 1 1 = A p x 1 0 * X p x 0 1 + A p x 1 1 * X p x 1 1 := by
    rw [mul_apply, Fin.sum_univ_two]
  have hA00 : A p x 0 0 = 0 := by rw [← A'_eq_A p, A'_00]
  have hA11 : A p x 1 1 = 0 := by rw [← A'_eq_A p, A'_11]
  rw [hL, hA00, hR, hA11]; ring

theorem neg_XinvA_01 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    -((X p x)⁻¹ * A p x) 0 1 = -(X p x).det⁻¹ * (A p x * X p x) 0 1 := by
  have hL : ((X p x)⁻¹ * A p x) 0 1 =
      (X p x).det⁻¹ * X p x 1 1 * A p x 0 1 + (X p x).det⁻¹ * -(X p x 0 1) * A p x 1 1 := by
    rw [mul_apply, Fin.sum_univ_two, Xinv_00, Xinv_01]
  have hR : (A p x * X p x) 0 1 = A p x 0 0 * X p x 0 1 + A p x 0 1 * X p x 1 1 := by
    rw [mul_apply, Fin.sum_univ_two]
  have hA00 : A p x 0 0 = 0 := by rw [← A'_eq_A p, A'_00]
  have hA11 : A p x 1 1 = 0 := by rw [← A'_eq_A p, A'_11]
  rw [hL, hA11, hR, hA00]; ring

theorem neg_XinvA_10 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    -((X p x)⁻¹ * A p x) 1 0 = -(X p x).det⁻¹ * (A p x * X p x) 1 0 := by
  have hL : ((X p x)⁻¹ * A p x) 1 0 =
      (X p x).det⁻¹ * -(X p x 1 0) * A p x 0 0 + (X p x).det⁻¹ * X p x 0 0 * A p x 1 0 := by
    rw [mul_apply, Fin.sum_univ_two, Xinv_10, Xinv_11]
  have hR : (A p x * X p x) 1 0 = A p x 1 0 * X p x 0 0 + A p x 1 1 * X p x 1 0 := by
    rw [mul_apply, Fin.sum_univ_two]
  have hA00 : A p x 0 0 = 0 := by rw [← A'_eq_A p, A'_00]
  have hA11 : A p x 1 1 = 0 := by rw [← A'_eq_A p, A'_11]
  rw [hL, hA00, hR, hA11]; ring

theorem neg_XinvA_11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    -((X p x)⁻¹ * A p x) 1 1 = (X p x).det⁻¹ * (A p x * X p x) 0 0 := by
  have hL : ((X p x)⁻¹ * A p x) 1 1 =
      (X p x).det⁻¹ * -(X p x 1 0) * A p x 0 1 + (X p x).det⁻¹ * X p x 0 0 * A p x 1 1 := by
    rw [mul_apply, Fin.sum_univ_two, Xinv_10, Xinv_11]
  have hR : (A p x * X p x) 0 0 = A p x 0 0 * X p x 0 0 + A p x 0 1 * X p x 1 0 := by
    rw [mul_apply, Fin.sum_univ_two]
  have hA00 : A p x 0 0 = 0 := by rw [← A'_eq_A p, A'_00]
  have hA11 : A p x 1 1 = 0 := by rw [← A'_eq_A p, A'_11]
  rw [hL, hA11, hR, hA00]; ring

/-! ═══ Chain: Dm(X⁻¹)_{ij} = -(X⁻¹*A)_{ij} ═══ -/

theorem Dm_Xinv_neg_00 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 0 0) x = -((X p x)⁻¹ * A p x) 0 0 := by
  rw [Dm_fac_00 p hx, dm_X11_AX p hx, neg_XinvA_00 p hx]

theorem Dm_Xinv_neg_01 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 0 1) x = -((X p x)⁻¹ * A p x) 0 1 := by
  rw [Dm_fac_01 p hx, dm_X01_AX p hx, neg_XinvA_01 p hx]

theorem Dm_Xinv_neg_10 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 1 0) x = -((X p x)⁻¹ * A p x) 1 0 := by
  rw [Dm_fac_10 p hx, dm_X10_AX p hx, neg_XinvA_10 p hx]

theorem Dm_Xinv_neg_11 {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (X p z)⁻¹ 1 1) x = -((X p x)⁻¹ * A p x) 1 1 := by
  rw [Dm_fac_11 p hx, dm_X00_AX p hx, neg_XinvA_11 p hx]

/-! ═══ Matrix assembly: Dm(X⁻¹) = -(X⁻¹*A) ═══ -/

theorem Dm_Xinv_matrix {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (of fun a b => Dm p (fun z => (X p z)⁻¹ a b) x) = -(X p x)⁻¹ * A p x := by
  ext i j; simp only [of_apply, neg_mul, Matrix.neg_apply]
  fin_cases i <;> fin_cases j
  · exact Dm_Xinv_neg_00 p hx
  · exact Dm_Xinv_neg_01 p hx
  · exact Dm_Xinv_neg_10 p hx
  · exact Dm_Xinv_neg_11 p hx

/-! ═══ D₊ / star helpers ═══ -/

theorem cpd_star_eq (i : Fin 2) (f : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) :
    cpd i (fun z => star (f z)) x = star (cpd i f x) := deriv.star

theorem Dp_eq_star_Dm_star (f : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) :
    Dp p f x = star (Dm p (fun z => star (f z)) x) := by
  unfold Dp Dm
  rw [cpd_star_eq, cpd_star_eq]
  have hI : star (I : ℂ) = -I := by rw [star_def]; exact conj_I
  have hR : star (↑(Real.sqrt (Del p (x 0))) : ℂ) = ↑(Real.sqrt (Del p (x 0))) := by
    rw [star_def]; exact conj_ofReal _
  rw [star_sub, star_mul, star_mul, star_star, star_star, hI, hR]; ring

theorem Dp_Xstarinv_entry {x : Fin 2 → ℝ} (hx : x ∈ U p) (i j : Fin 2) :
    Dp p (fun z => ((X p z)ᴴ)⁻¹ i j) x = star (Dm p (fun z => (X p z)⁻¹ j i) x) := by
  have key : ∀ z, ((X p z)ᴴ)⁻¹ i j = star ((X p z)⁻¹ j i) := fun z => by
    rw [← conjTranspose_nonsing_inv, conjTranspose_apply]
  simp_rw [key, Dp_eq_star_Dm_star]; simp [star_star]

/-! ═══ Main theorem ═══ -/

theorem Dplus_XstarInv_eq' {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (of fun a b => Dp p (fun z => ((X p z)ᴴ)⁻¹ a b) x) = -A p x * ((X p x)ᴴ)⁻¹ := by
  ext i j
  simp only [of_apply, Dp_Xstarinv_entry p hx]
  have hDm : Dm p (fun z => (X p z)⁻¹ j i) x = -((X p x)⁻¹ * A p x) j i := by
    have h := congr_fun (congr_fun (Dm_Xinv_matrix p hx) j) i
    simp only [of_apply, neg_mul, Matrix.neg_apply] at h; exact h
  rw [hDm, star_neg]
  simp only [neg_mul, Matrix.neg_apply]
  congr 1
  have hmat : A p x * (X p x)ᴴ⁻¹ = ((X p x)⁻¹ * A p x)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, A_conjTranspose p hx]
  rw [hmat, conjTranspose_apply]

theorem Dplus_XstarInv_eq {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (of fun a b => Dp p (fun z => ((X p z)ᴴ)⁻¹ a b) x) =
    -A p x * ((X p x)ᴴ)⁻¹ := by
  ext i j
  simp only [of_apply, Dp_Xstarinv_entry p hx]
  have hDm : Dm p (fun z => (X p z)⁻¹ j i) x = -((X p x)⁻¹ * A p x) j i := by
    have h := congr_fun (congr_fun (Dm_Xinv_matrix p hx) j) i
    simp only [of_apply, neg_mul, Matrix.neg_apply] at h; exact h
  rw [hDm, star_neg]
  simp only [neg_mul, Matrix.neg_apply]
  congr 1
  have hmat : A p x * (X p x)ᴴ⁻¹ = ((X p x)⁻¹ * A p x)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_nonsing_inv, A_conjTranspose p hx]
  rw [hmat, conjTranspose_apply]

end Hintz2026

end
