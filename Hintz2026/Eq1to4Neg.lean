import Hintz2026.Eq1to4Pos

-- Hintz 2026 - (1) -> (4), negative spin (ς = −1): the four scalar residual identities for the
-- replacement system (1)⁻ and the chiral variables y±^(−) = Δ^{-3/4}√sinθ (ψ₋₂ ∓ i√Δ ψ₋₁, 2Q(n ∓ i√Δ ℓ)).

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

open Complex Function Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-- normalised negative-spin chiral components; `e = ±1`. -/
def g1N (e : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : ℂ :=
  G.psim2 x - ↑e * I * ↑(Real.sqrt (Del p (x 0))) * G.psim1 x
def g2N (e : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : ℂ :=
  2 * ↑p.Q * (G.n x - ↑e * I * ↑(Real.sqrt (Del p (x 0))) * G.l x)

theorem yNeg_0 (e : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : yNeg p e G x 0 = ↑(preNeg p x) * g1N p e G x := by simp [yNeg, g1N]
theorem yNeg_1 (e : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : yNeg p e G x 1 = ↑(preNeg p x) * g2N p e G x := by simp [yNeg, g2N]

/-! ### D± of f·√Δ -/

theorem cpd0_sqrtDel {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (↑(Real.sqrt (Del p (z 0))) : ℂ)) x = ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) := by
  unfold cpd
  have h1 : HasDerivAt (fun u => (↑(Real.sqrt (Del p u)) : ℂ)) (↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) (x 0) :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_sqrtDel_r p (Del_pos p hx.1))
  refine (h1.congr_of_eventuallyEq ?_).deriv
  filter_upwards with u; simp [Function.update]

theorem cpd1_sqrtDel (x : Fin 2 -> ℝ) :
    cpd 1 (fun z => (↑(Real.sqrt (Del p (z 0))) : ℂ)) x = 0 := by
  unfold cpd
  have : (fun u => (↑(Real.sqrt (Del p ((update x 1 u) 0))) : ℂ)) = fun _ => (↑(Real.sqrt (Del p (x 0))) : ℂ) := by
    funext u; simp [Function.update]
  rw [this, deriv_const]

theorem diff_sqrtDel_slice {x : Fin 2 -> ℝ} (hx : x ∈ U p) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => (↑(Real.sqrt (Del p ((update x k u) 0))) : ℂ)) (x k) := by
  fin_cases k
  · have h1 : HasDerivAt (fun u => (↑(Real.sqrt (Del p u)) : ℂ)) (↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) (x 0) :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_sqrtDel_r p (Del_pos p hx.1))
    refine (h1.congr_of_eventuallyEq ?_).differentiableAt
    filter_upwards with u; simp [Function.update]
  · show DifferentiableAt ℝ (fun u => (↑(Real.sqrt (Del p ((update x 1 u) 0))) : ℂ)) (x 1)
    have : (fun u => (↑(Real.sqrt (Del p ((update x 1 u) 0))) : ℂ)) = fun _ => (↑(Real.sqrt (Del p (x 0))) : ℂ) := by
      funext u; simp [Function.update]
    rw [this]; exact differentiableAt_const _

theorem Dm_sqrtDel_mul {x : Fin 2 -> ℝ} (hx : x ∈ U p) (f : (Fin 2 -> ℝ) -> ℂ)
    (hf : ∀ k, DifferentiableAt ℝ (fun u => f (update x k u)) (x k)) :
    Dm p (fun z => ↑(Real.sqrt (Del p (z 0))) * f z) x
      = ↑(Real.sqrt (Del p (x 0))) * Dm p f x + ↑(Del' p (x 0)) / 2 * f x := by
  rw [Dm_mul p _ f x (diff_sqrtDel_slice p hx 0) (hf 0) (diff_sqrtDel_slice p hx 1) (hf 1)]
  unfold Dm; rw [cpd0_sqrtDel p hx, cpd1_sqrtDel, Del'_eq]
  have hD := Del_pos p hx.1
  have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  push_cast; field_simp; ring

theorem Dp_sqrtDel_mul {x : Fin 2 -> ℝ} (hx : x ∈ U p) (f : (Fin 2 -> ℝ) -> ℂ)
    (hf : ∀ k, DifferentiableAt ℝ (fun u => f (update x k u)) (x k)) :
    Dp p (fun z => ↑(Real.sqrt (Del p (z 0))) * f z) x
      = ↑(Real.sqrt (Del p (x 0))) * Dp p f x + ↑(Del' p (x 0)) / 2 * f x := by
  rw [Dp_mul p _ f x (diff_sqrtDel_slice p hx 0) (hf 0) (diff_sqrtDel_slice p hx 1) (hf 1)]
  unfold Dp; rw [cpd0_sqrtDel p hx, cpd1_sqrtDel, Del'_eq]
  have hD := Del_pos p hx.1
  have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  push_cast; field_simp; ring

structure NegDiff (G : NegFields) (x : Fin 2 -> ℝ) : Prop where
  psim2 : ∀ k, DifferentiableAt ℝ (fun u => G.psim2 (update x k u)) (x k)
  psim1 : ∀ k, DifferentiableAt ℝ (fun u => G.psim1 (update x k u)) (x k)
  n     : ∀ k, DifferentiableAt ℝ (fun u => G.n (update x k u)) (x k)
  l     : ∀ k, DifferentiableAt ℝ (fun u => G.l (update x k u)) (x k)

theorem g1N_eq (e : ℝ) (G : NegFields) :
    g1N p e G = fun z => G.psim2 z + (-(↑e * I)) * (↑(Real.sqrt (Del p (z 0))) * G.psim1 z) := by
  funext z; unfold g1N; ring
theorem g2N_eq (e : ℝ) (G : NegFields) :
    g2N p e G = fun z => (2 * ↑p.Q) * (G.n z + (-(↑e * I)) * (↑(Real.sqrt (Del p (z 0))) * G.l z)) := by
  funext z; unfold g2N; ring

theorem diff_sqrtDel_mul_slice {x : Fin 2 -> ℝ} (hx : x ∈ U p) (f : (Fin 2 -> ℝ) -> ℂ)
    (hf : ∀ k, DifferentiableAt ℝ (fun u => f (update x k u)) (x k)) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => ↑(Real.sqrt (Del p ((update x k u) 0))) * f (update x k u)) (x k) :=
  (diff_sqrtDel_slice p hx k).mul (hf k)

theorem diff_g1N_slice (e : ℝ) {G : NegFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hG : NegDiff G x) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => g1N p e G (update x k u)) (x k) := by
  rw [g1N_eq]; exact (hG.psim2 k).add ((diff_sqrtDel_mul_slice p hx G.psim1 hG.psim1 k).const_mul _)
theorem diff_g2N_slice (e : ℝ) {G : NegFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hG : NegDiff G x) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => g2N p e G (update x k u)) (x k) := by
  rw [g2N_eq]; exact ((hG.n k).add ((diff_sqrtDel_mul_slice p hx G.l hG.l k).const_mul _)).const_mul _

theorem Dm_g1N (e : ℝ) {G : NegFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hG : NegDiff G x) :
    Dm p (g1N p e G) x = Dm p G.psim2 x
      + (-(↑e * I)) * (↑(Real.sqrt (Del p (x 0))) * Dm p G.psim1 x + ↑(Del' p (x 0)) / 2 * G.psim1 x) := by
  rw [g1N_eq, Dm_add p _ _ x (hG.psim2 0) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.psim1 z) (diff_sqrtDel_mul_slice p hx G.psim1 hG.psim1) 0)
        (hG.psim2 1) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.psim1 z) (diff_sqrtDel_mul_slice p hx G.psim1 hG.psim1) 1),
      Dm_const_mul, Dm_sqrtDel_mul p hx G.psim1 hG.psim1]
theorem Dm_g2N (e : ℝ) {G : NegFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hG : NegDiff G x) :
    Dm p (g2N p e G) x = (2 * ↑p.Q) * (Dm p G.n x
      + (-(↑e * I)) * (↑(Real.sqrt (Del p (x 0))) * Dm p G.l x + ↑(Del' p (x 0)) / 2 * G.l x)) := by
  rw [g2N_eq, Dm_const_mul, Dm_add p _ _ x (hG.n 0) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.l z) (diff_sqrtDel_mul_slice p hx G.l hG.l) 0)
        (hG.n 1) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.l z) (diff_sqrtDel_mul_slice p hx G.l hG.l) 1),
      Dm_const_mul, Dm_sqrtDel_mul p hx G.l hG.l]
theorem Dp_g1N (e : ℝ) {G : NegFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hG : NegDiff G x) :
    Dp p (g1N p e G) x = Dp p G.psim2 x
      + (-(↑e * I)) * (↑(Real.sqrt (Del p (x 0))) * Dp p G.psim1 x + ↑(Del' p (x 0)) / 2 * G.psim1 x) := by
  rw [g1N_eq, Dp_add p _ _ x (hG.psim2 0) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.psim1 z) (diff_sqrtDel_mul_slice p hx G.psim1 hG.psim1) 0)
        (hG.psim2 1) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.psim1 z) (diff_sqrtDel_mul_slice p hx G.psim1 hG.psim1) 1),
      Dp_const_mul, Dp_sqrtDel_mul p hx G.psim1 hG.psim1]
theorem Dp_g2N (e : ℝ) {G : NegFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hG : NegDiff G x) :
    Dp p (g2N p e G) x = (2 * ↑p.Q) * (Dp p G.n x
      + (-(↑e * I)) * (↑(Real.sqrt (Del p (x 0))) * Dp p G.l x + ↑(Del' p (x 0)) / 2 * G.l x)) := by
  rw [g2N_eq, Dp_const_mul, Dp_add p _ _ x (hG.n 0) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.l z) (diff_sqrtDel_mul_slice p hx G.l hG.l) 0)
        (hG.n 1) (diff_const_mul_slice _ (fun z => ↑(Real.sqrt (Del p (z 0))) * G.l z) (diff_sqrtDel_mul_slice p hx G.l hG.l) 1),
      Dp_const_mul, Dp_sqrtDel_mul p hx G.l hG.l]

theorem cpd_neg (k : Fin 2) (f : (Fin 2 -> ℝ) -> ℂ) (x : Fin 2 -> ℝ) :
    cpd k (fun z => -f z) x = -cpd k f x := by
  unfold cpd; exact deriv.neg

/-! ### The four negative-spin identities (ς = −1) -/

theorem identN_m0 (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (G : NegFields) (hG : NegDiff G x) :
    Dm p (fun z => yNeg p 1 G z 0) x - (A p x *ᵥ yNeg p 1 G x) 0
      - ((cscalar p (-1) om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p (-1) om mm x) *ᵥ yNeg p (-1) G x) 0
    = ↑(preNeg p x) * (-I * res1aN p om mm G x + ↑(Real.sqrt (Del p (x 0))) * res1bN p om mm G x) := by
  have hy : (fun z => yNeg p 1 G z 0) = fun z => ↑(preNeg p z) * g1N p 1 G z := by funext z; exact yNeg_0 p 1 G z
  rw [hy, Dm_preNeg_mul p hx _ (diff_g1N_slice p 1 hx hG), Dm_g1N p 1 hx hG,
    mulVec_entry0, mulVec_entry0, cIsubB_00, cIsubB_01, A_00, A_01, B_00, B_01, yNeg_0, yNeg_1, yNeg_0, yNeg_1]
  unfold res1aN res1bN Dop DopDag Lop LopDag threeIaSin threeOverRhoStar Fplus Fminus lamNegM cscalar bcoeff Qhat cotR Kfreq Del' g1N g2N
  simp only [cpd_neg]
  unfold Dm
  have hD : 0 < Del p (x 0) := Del_pos p hx.1
  have hDne : (↑(Del p (x 0)) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have hsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 2 = ↑(Del p (x 0)) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hD.le]
  have hs : (↑(Real.sin (x 1)) : ℂ) ≠ 0 := by exact_mod_cast (sin_pos_of_mem p hx).ne'
  have hr := rhoBar_ne_zero p hx; have hrs := rhoBarStar_ne_zero p hx
  have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
  have hpre : (↑(preNeg p x) : ℂ) ≠ 0 := by exact_mod_cast (preNeg_pos p hx).ne'
  have hrr : rhoBar p x = ↑(x 0) + ↑p.a * ↑(Real.cos (x 1)) * I := by rw [rhoBar_eq_ofReal]; push_cast; ring
  have hrrs : rhoBarStar p x = ↑(x 0) - ↑p.a * ↑(Real.cos (x 1)) * I := by rw [rhoBarStar_eq_ofReal]; push_cast; ring
  have htrig : (↑(Real.sin (x 1)) : ℂ) ^ 2 + (↑(Real.cos (x 1)) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, Real.sin_sq_add_cos_sq]; rfl
  have hcos2 : (↑(Real.cos (x 1)) : ℂ) ^ 2 = 1 - (↑(Real.sin (x 1)) : ℂ) ^ 2 := by linear_combination htrig
  have hs3 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 3 = ↑(Real.sqrt (Del p (x 0))) * ↑(Del p (x 0)) := by rw [pow_succ, hsq, mul_comm]
  have hs4 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 4 = ↑(Del p (x 0)) ^ 2 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, hsq]
  have hs5 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 5 = ↑(Real.sqrt (Del p (x 0))) * ↑(Del p (x 0)) ^ 2 := by rw [pow_succ, hs4, mul_comm]
  have hs6 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 6 = ↑(Del p (x 0)) ^ 3 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, hsq]
  have hc3 : (↑(Real.cos (x 1)) : ℂ) ^ 3 = ↑(Real.cos (x 1)) * (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) := by rw [pow_succ, hcos2, mul_comm]
  have hc4 : (↑(Real.cos (x 1)) : ℂ) ^ 4 = (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 2 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, hcos2]
  have hc5 : (↑(Real.cos (x 1)) : ℂ) ^ 5 = ↑(Real.cos (x 1)) * (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 2 := by rw [pow_succ, hc4, mul_comm]
  have hc6 : (↑(Real.cos (x 1)) : ℂ) ^ 6 = (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 3 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, hcos2]
  have hI5 : (I : ℂ) ^ 5 = I := by rw [pow_succ, I_pow_four, one_mul]
  have hI6 : (I : ℂ) ^ 6 = -1 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, I_sq]; norm_num
  have hI7 : (I : ℂ) ^ 7 = -I := by rw [pow_succ, hI6]; ring
  have hI8 : (I : ℂ) ^ 8 = 1 := by rw [show (8:ℕ) = 4*2 from rfl, pow_mul, I_pow_four, one_pow]
  push_cast at *
  field_simp [hr, hrs, hDne, hsD, hs, hQ, hpre]
  rw [hrr, hrrs]
  ring_nf
  simp only [hsq, hs3, hs4, hs5, hs6, hcos2, hc3, hc4, hc5, hc6, I_sq, I_pow_three, I_pow_four, hI5, hI6, hI7, hI8]
  simp only [Del]
  push_cast
  ring_nf


theorem identN_m1 (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (G : NegFields) (hG : NegDiff G x) :
    Dm p (fun z => yNeg p 1 G z 1) x - (A p x *ᵥ yNeg p 1 G x) 1
      - ((cscalar p (-1) om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p (-1) om mm x) *ᵥ yNeg p (-1) G x) 1
    = ↑(preNeg p x) * ((2 * ↑p.Q) * (-I * res1cN p om mm G x - ↑(Real.sqrt (Del p (x 0))) * res1dN p om mm G x)) := by
  have hy : (fun z => yNeg p 1 G z 1) = fun z => ↑(preNeg p z) * g2N p 1 G z := by funext z; exact yNeg_1 p 1 G z
  rw [hy, Dm_preNeg_mul p hx _ (diff_g2N_slice p 1 hx hG), Dm_g2N p 1 hx hG,
    mulVec_entry1, mulVec_entry1, cIsubB_10, cIsubB_11, A_10, A_11, B_10, B_11, yNeg_0, yNeg_1, yNeg_0, yNeg_1]
  unfold res1cN res1dN Dop DopDag Lop LopDag threeIaSin threeOverRhoStar lamNegM cscalar bcoeff Qhat cotR Kfreq Del' g1N g2N
  simp only [cpd_neg]
  unfold Dm
  have hD : 0 < Del p (x 0) := Del_pos p hx.1
  have hDne : (↑(Del p (x 0)) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have hsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 2 = ↑(Del p (x 0)) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hD.le]
  have hs : (↑(Real.sin (x 1)) : ℂ) ≠ 0 := by exact_mod_cast (sin_pos_of_mem p hx).ne'
  have hr := rhoBar_ne_zero p hx; have hrs := rhoBarStar_ne_zero p hx
  have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
  have hpre : (↑(preNeg p x) : ℂ) ≠ 0 := by exact_mod_cast (preNeg_pos p hx).ne'
  have hrr : rhoBar p x = ↑(x 0) + ↑p.a * ↑(Real.cos (x 1)) * I := by rw [rhoBar_eq_ofReal]; push_cast; ring
  have hrrs : rhoBarStar p x = ↑(x 0) - ↑p.a * ↑(Real.cos (x 1)) * I := by rw [rhoBarStar_eq_ofReal]; push_cast; ring
  have htrig : (↑(Real.sin (x 1)) : ℂ) ^ 2 + (↑(Real.cos (x 1)) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, Real.sin_sq_add_cos_sq]; rfl
  have hcos2 : (↑(Real.cos (x 1)) : ℂ) ^ 2 = 1 - (↑(Real.sin (x 1)) : ℂ) ^ 2 := by linear_combination htrig
  have hs3 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 3 = ↑(Real.sqrt (Del p (x 0))) * ↑(Del p (x 0)) := by rw [pow_succ, hsq, mul_comm]
  have hs4 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 4 = ↑(Del p (x 0)) ^ 2 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, hsq]
  have hs5 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 5 = ↑(Real.sqrt (Del p (x 0))) * ↑(Del p (x 0)) ^ 2 := by rw [pow_succ, hs4, mul_comm]
  have hs6 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 6 = ↑(Del p (x 0)) ^ 3 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, hsq]
  have hc3 : (↑(Real.cos (x 1)) : ℂ) ^ 3 = ↑(Real.cos (x 1)) * (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) := by rw [pow_succ, hcos2, mul_comm]
  have hc4 : (↑(Real.cos (x 1)) : ℂ) ^ 4 = (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 2 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, hcos2]
  have hc5 : (↑(Real.cos (x 1)) : ℂ) ^ 5 = ↑(Real.cos (x 1)) * (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 2 := by rw [pow_succ, hc4, mul_comm]
  have hc6 : (↑(Real.cos (x 1)) : ℂ) ^ 6 = (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 3 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, hcos2]
  have hI5 : (I : ℂ) ^ 5 = I := by rw [pow_succ, I_pow_four, one_mul]
  have hI6 : (I : ℂ) ^ 6 = -1 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, I_sq]; norm_num
  have hI7 : (I : ℂ) ^ 7 = -I := by rw [pow_succ, hI6]; ring
  have hI8 : (I : ℂ) ^ 8 = 1 := by rw [show (8:ℕ) = 4*2 from rfl, pow_mul, I_pow_four, one_pow]
  push_cast at *
  field_simp [hr, hrs, hDne, hsD, hs, hQ, hpre]
  rw [hrr, hrrs]
  ring_nf
  simp only [hsq, hs3, hs4, hs5, hs6, hcos2, hc3, hc4, hc5, hc6, I_sq, I_pow_three, I_pow_four, hI5, hI6, hI7, hI8]
  simp only [Del]
  push_cast
  ring_nf


theorem identN_p0 (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (G : NegFields) (hG : NegDiff G x) :
    Dp p (fun z => yNeg p (-1) G z 0) x + (A p x *ᵥ yNeg p (-1) G x) 0
      - ((cscalar p (-1) om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p (-1) om mm x) *ᵥ yNeg p 1 G x) 0
    = ↑(preNeg p x) * (I * res1aN p om mm G x + ↑(Real.sqrt (Del p (x 0))) * res1bN p om mm G x) := by
  have hy : (fun z => yNeg p (-1) G z 0) = fun z => ↑(preNeg p z) * g1N p (-1) G z := by funext z; exact yNeg_0 p (-1) G z
  rw [hy, Dp_preNeg_mul p hx _ (diff_g1N_slice p (-1) hx hG), Dp_g1N p (-1) hx hG,
    mulVec_entry0, mulVec_entry0, cIaddB_00, cIaddB_01, A_00, A_01, B_00, B_01, yNeg_0, yNeg_1, yNeg_0, yNeg_1]
  unfold res1aN res1bN Dop DopDag Lop LopDag threeIaSin threeOverRhoStar Fplus Fminus lamNegP cscalar bcoeff Qhat cotR Kfreq Del' g1N g2N
  simp only [cpd_neg]
  unfold Dp
  have hD : 0 < Del p (x 0) := Del_pos p hx.1
  have hDne : (↑(Del p (x 0)) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have hsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 2 = ↑(Del p (x 0)) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hD.le]
  have hs : (↑(Real.sin (x 1)) : ℂ) ≠ 0 := by exact_mod_cast (sin_pos_of_mem p hx).ne'
  have hr := rhoBar_ne_zero p hx; have hrs := rhoBarStar_ne_zero p hx
  have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
  have hpre : (↑(preNeg p x) : ℂ) ≠ 0 := by exact_mod_cast (preNeg_pos p hx).ne'
  have hrr : rhoBar p x = ↑(x 0) + ↑p.a * ↑(Real.cos (x 1)) * I := by rw [rhoBar_eq_ofReal]; push_cast; ring
  have hrrs : rhoBarStar p x = ↑(x 0) - ↑p.a * ↑(Real.cos (x 1)) * I := by rw [rhoBarStar_eq_ofReal]; push_cast; ring
  have htrig : (↑(Real.sin (x 1)) : ℂ) ^ 2 + (↑(Real.cos (x 1)) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, Real.sin_sq_add_cos_sq]; rfl
  have hcos2 : (↑(Real.cos (x 1)) : ℂ) ^ 2 = 1 - (↑(Real.sin (x 1)) : ℂ) ^ 2 := by linear_combination htrig
  have hs3 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 3 = ↑(Real.sqrt (Del p (x 0))) * ↑(Del p (x 0)) := by rw [pow_succ, hsq, mul_comm]
  have hs4 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 4 = ↑(Del p (x 0)) ^ 2 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, hsq]
  have hs5 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 5 = ↑(Real.sqrt (Del p (x 0))) * ↑(Del p (x 0)) ^ 2 := by rw [pow_succ, hs4, mul_comm]
  have hs6 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 6 = ↑(Del p (x 0)) ^ 3 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, hsq]
  have hc3 : (↑(Real.cos (x 1)) : ℂ) ^ 3 = ↑(Real.cos (x 1)) * (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) := by rw [pow_succ, hcos2, mul_comm]
  have hc4 : (↑(Real.cos (x 1)) : ℂ) ^ 4 = (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 2 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, hcos2]
  have hc5 : (↑(Real.cos (x 1)) : ℂ) ^ 5 = ↑(Real.cos (x 1)) * (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 2 := by rw [pow_succ, hc4, mul_comm]
  have hc6 : (↑(Real.cos (x 1)) : ℂ) ^ 6 = (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 3 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, hcos2]
  have hI5 : (I : ℂ) ^ 5 = I := by rw [pow_succ, I_pow_four, one_mul]
  have hI6 : (I : ℂ) ^ 6 = -1 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, I_sq]; norm_num
  have hI7 : (I : ℂ) ^ 7 = -I := by rw [pow_succ, hI6]; ring
  have hI8 : (I : ℂ) ^ 8 = 1 := by rw [show (8:ℕ) = 4*2 from rfl, pow_mul, I_pow_four, one_pow]
  push_cast at *
  field_simp [hr, hrs, hDne, hsD, hs, hQ, hpre]
  rw [hrr, hrrs]
  ring_nf
  simp only [hsq, hs3, hs4, hs5, hs6, hcos2, hc3, hc4, hc5, hc6, I_sq, I_pow_three, I_pow_four, hI5, hI6, hI7, hI8]
  simp only [Del]
  push_cast
  ring_nf


theorem identN_p1 (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (G : NegFields) (hG : NegDiff G x) :
    Dp p (fun z => yNeg p (-1) G z 1) x + (A p x *ᵥ yNeg p (-1) G x) 1
      - ((cscalar p (-1) om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p (-1) om mm x) *ᵥ yNeg p 1 G x) 1
    = ↑(preNeg p x) * ((2 * ↑p.Q) * (I * res1cN p om mm G x - ↑(Real.sqrt (Del p (x 0))) * res1dN p om mm G x)) := by
  have hy : (fun z => yNeg p (-1) G z 1) = fun z => ↑(preNeg p z) * g2N p (-1) G z := by funext z; exact yNeg_1 p (-1) G z
  rw [hy, Dp_preNeg_mul p hx _ (diff_g2N_slice p (-1) hx hG), Dp_g2N p (-1) hx hG,
    mulVec_entry1, mulVec_entry1, cIaddB_10, cIaddB_11, A_10, A_11, B_10, B_11, yNeg_0, yNeg_1, yNeg_0, yNeg_1]
  unfold res1cN res1dN Dop DopDag Lop LopDag threeIaSin threeOverRhoStar lamNegP cscalar bcoeff Qhat cotR Kfreq Del' g1N g2N
  simp only [cpd_neg]
  unfold Dp
  have hD : 0 < Del p (x 0) := Del_pos p hx.1
  have hDne : (↑(Del p (x 0)) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have hsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 2 = ↑(Del p (x 0)) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hD.le]
  have hs : (↑(Real.sin (x 1)) : ℂ) ≠ 0 := by exact_mod_cast (sin_pos_of_mem p hx).ne'
  have hr := rhoBar_ne_zero p hx; have hrs := rhoBarStar_ne_zero p hx
  have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
  have hpre : (↑(preNeg p x) : ℂ) ≠ 0 := by exact_mod_cast (preNeg_pos p hx).ne'
  have hrr : rhoBar p x = ↑(x 0) + ↑p.a * ↑(Real.cos (x 1)) * I := by rw [rhoBar_eq_ofReal]; push_cast; ring
  have hrrs : rhoBarStar p x = ↑(x 0) - ↑p.a * ↑(Real.cos (x 1)) * I := by rw [rhoBarStar_eq_ofReal]; push_cast; ring
  have htrig : (↑(Real.sin (x 1)) : ℂ) ^ 2 + (↑(Real.cos (x 1)) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add, Real.sin_sq_add_cos_sq]; rfl
  have hcos2 : (↑(Real.cos (x 1)) : ℂ) ^ 2 = 1 - (↑(Real.sin (x 1)) : ℂ) ^ 2 := by linear_combination htrig
  have hs3 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 3 = ↑(Real.sqrt (Del p (x 0))) * ↑(Del p (x 0)) := by rw [pow_succ, hsq, mul_comm]
  have hs4 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 4 = ↑(Del p (x 0)) ^ 2 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, hsq]
  have hs5 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 5 = ↑(Real.sqrt (Del p (x 0))) * ↑(Del p (x 0)) ^ 2 := by rw [pow_succ, hs4, mul_comm]
  have hs6 : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 6 = ↑(Del p (x 0)) ^ 3 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, hsq]
  have hc3 : (↑(Real.cos (x 1)) : ℂ) ^ 3 = ↑(Real.cos (x 1)) * (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) := by rw [pow_succ, hcos2, mul_comm]
  have hc4 : (↑(Real.cos (x 1)) : ℂ) ^ 4 = (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 2 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, hcos2]
  have hc5 : (↑(Real.cos (x 1)) : ℂ) ^ 5 = ↑(Real.cos (x 1)) * (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 2 := by rw [pow_succ, hc4, mul_comm]
  have hc6 : (↑(Real.cos (x 1)) : ℂ) ^ 6 = (1 - (↑(Real.sin (x 1)) : ℂ) ^ 2) ^ 3 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, hcos2]
  have hI5 : (I : ℂ) ^ 5 = I := by rw [pow_succ, I_pow_four, one_mul]
  have hI6 : (I : ℂ) ^ 6 = -1 := by rw [show (6:ℕ) = 2*3 from rfl, pow_mul, I_sq]; norm_num
  have hI7 : (I : ℂ) ^ 7 = -I := by rw [pow_succ, hI6]; ring
  have hI8 : (I : ℂ) ^ 8 = 1 := by rw [show (8:ℕ) = 4*2 from rfl, pow_mul, I_pow_four, one_pow]
  push_cast at *
  field_simp [hr, hrs, hDne, hsD, hs, hQ, hpre]
  rw [hrr, hrrs]
  ring_nf
  simp only [hsq, hs3, hs4, hs5, hs6, hcos2, hc3, hc4, hc5, hc6, I_sq, I_pow_three, I_pow_four, hI5, hI6, hI7, hI8]
  simp only [Del]
  push_cast
  ring_nf


end Hintz2026

end
