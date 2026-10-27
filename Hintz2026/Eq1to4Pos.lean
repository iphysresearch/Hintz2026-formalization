import Hintz2026.Eq1to4Identity

-- Hintz 2026 - (1) -> (4), positive spin, the four scalar residual identities.
-- Dm(y₊) − A y₊ − (cI − B) y₋ = prePos · W₊ · res,  Dp(y₋) + A y₋ − (cI + B) y₊ = prePos · W₋ · res

set_option maxHeartbeats 100000000
set_option maxRecDepth 100000

open Complex Function Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

-- entry lemmas for the (4) coefficient matrices
theorem A_00 (x : Fin 2 -> ℝ) : A p x 0 0 = 0 := by simp [A]
theorem A_01 (x : Fin 2 -> ℝ) : A p x 0 1 = -I * ↑p.Q * rhoBarStar p x / rhoBar p x ^ 2 := by simp [A]
theorem A_10 (x : Fin 2 -> ℝ) : A p x 1 0 = I * ↑p.Q * rhoBar p x / rhoBarStar p x ^ 2 := by simp [A]
theorem A_11 (x : Fin 2 -> ℝ) : A p x 1 1 = 0 := by simp [A]
theorem B_00 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : Bmat p sg om mm x 0 0 = I * bcoeff p sg om mm x := by simp [Bmat]
theorem B_01 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : Bmat p sg om mm x 0 1 = I * (3 * (↑p.M * rhoBar p x - ↑(p.Q ^ 2)) / (↑p.Q * rhoBar p x)) := by simp [Bmat]
theorem B_10 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : Bmat p sg om mm x 1 0 = I * (3 * ↑p.Q * rhoBar p x / rhoBarStar p x ^ 2) := by simp [Bmat]
theorem B_11 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : Bmat p sg om mm x 1 1 = I * -bcoeff p sg om mm x := by simp [Bmat]

theorem mulVec_entry0 (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 -> ℂ) : (M *ᵥ v) 0 = M 0 0 * v 0 + M 0 1 * v 1 := by
  simp [mulVec, dotProduct, Fin.sum_univ_two]
theorem mulVec_entry1 (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 -> ℂ) : (M *ᵥ v) 1 = M 1 0 * v 0 + M 1 1 * v 1 := by
  simp [mulVec, dotProduct, Fin.sum_univ_two]
theorem cIsubB_00 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) 0 0 = cscalar p sg om mm x - Bmat p sg om mm x 0 0 := by simp
theorem cIsubB_01 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) 0 1 = - Bmat p sg om mm x 0 1 := by simp
theorem cIsubB_10 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) 1 0 = - Bmat p sg om mm x 1 0 := by simp
theorem cIsubB_11 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) 1 1 = cscalar p sg om mm x - Bmat p sg om mm x 1 1 := by simp

/-- Component 0 of the Dm-equation of (4), ς = +1. -/
theorem ident_m0 (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (F : PosFields) (hF : PosDiff F x) :
    Dm p (fun z => yPos p 1 F z 0) x - (A p x *ᵥ yPos p 1 F x) 0
      - ((cscalar p 1 om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p 1 om mm x) *ᵥ yPos p (-1) F x) 0
    = ↑(prePos p x) * (-I * res1a p om mm F x + res1b p om mm F x / ↑(Real.sqrt (Del p (x 0)))) := by
  have hy : (fun z => yPos p 1 F z 0) = fun z => ↑(prePos p z) * g1 p 1 F z := by funext z; exact yPos_0 p 1 F z
  rw [hy, Dm_prePos_mul p hx _ (diff_g1_slice p 1 hx hF), Dm_g1 p 1 hx hF,
    mulVec_entry0, mulVec_entry0, cIsubB_00, cIsubB_01, A_00, A_01, B_00, B_01, yPos_0, yPos_1, yPos_0, yPos_1]
  unfold res1a res1b Dop DopDag Lop LopDag threeIaSin threeOverRhoStar Fplus Fminus lamPosM cscalar bcoeff Qhat cotR Kfreq Del' g1 g2
  unfold Dm
  have hD : 0 < Del p (x 0) := Del_pos p hx.1
  have hDne : (↑(Del p (x 0)) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have hsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 2 = ↑(Del p (x 0)) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hD.le]
  have hs : (↑(Real.sin (x 1)) : ℂ) ≠ 0 := by exact_mod_cast (sin_pos_of_mem p hx).ne'
  have hr := rhoBar_ne_zero p hx; have hrs := rhoBarStar_ne_zero p hx
  have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
  have hpre : (↑(prePos p x) : ℂ) ≠ 0 := by exact_mod_cast (prePos_pos p hx).ne'
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

theorem cIaddB_00 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) 0 0 = cscalar p sg om mm x + Bmat p sg om mm x 0 0 := by simp
theorem cIaddB_01 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) 0 1 = Bmat p sg om mm x 0 1 := by simp
theorem cIaddB_10 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) 1 0 = Bmat p sg om mm x 1 0 := by simp
theorem cIaddB_11 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) 1 1 = cscalar p sg om mm x + Bmat p sg om mm x 1 1 := by simp

/-- Component 1 of the Dm-equation of (4), ς = +1. -/
theorem ident_m1 (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (F : PosFields) (hF : PosDiff F x) :
    Dm p (fun z => yPos p 1 F z 1) x - (A p x *ᵥ yPos p 1 F x) 1
      - ((cscalar p 1 om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p 1 om mm x) *ᵥ yPos p (-1) F x) 1
    = ↑(prePos p x) * ((-2 * ↑p.Q) * (I * res1c p om mm F x + res1d p om mm F x / ↑(Real.sqrt (Del p (x 0))))) := by
  have hy : (fun z => yPos p 1 F z 1) = fun z => ↑(prePos p z) * g2 p 1 F z := by funext z; exact yPos_1 p 1 F z
  rw [hy, Dm_prePos_mul p hx _ (diff_g2_slice p 1 hx hF), Dm_g2 p 1 hx hF,
    mulVec_entry1, mulVec_entry1, cIsubB_10, cIsubB_11, A_10, A_11, B_10, B_11, yPos_0, yPos_1, yPos_0, yPos_1]
  unfold res1c res1d Dop DopDag Lop LopDag threeIaSin threeOverRhoStar lamPosM cscalar bcoeff Qhat cotR Kfreq Del' g1 g2
  unfold Dm
  have hD : 0 < Del p (x 0) := Del_pos p hx.1
  have hDne : (↑(Del p (x 0)) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have hsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 2 = ↑(Del p (x 0)) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hD.le]
  have hs : (↑(Real.sin (x 1)) : ℂ) ≠ 0 := by exact_mod_cast (sin_pos_of_mem p hx).ne'
  have hr := rhoBar_ne_zero p hx; have hrs := rhoBarStar_ne_zero p hx
  have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
  have hpre : (↑(prePos p x) : ℂ) ≠ 0 := by exact_mod_cast (prePos_pos p hx).ne'
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

/-- Component 0 of the Dp-equation of (4), ς = +1. -/
theorem ident_p0 (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (F : PosFields) (hF : PosDiff F x) :
    Dp p (fun z => yPos p (-1) F z 0) x + (A p x *ᵥ yPos p (-1) F x) 0
      - ((cscalar p 1 om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p 1 om mm x) *ᵥ yPos p 1 F x) 0
    = ↑(prePos p x) * (I * res1a p om mm F x + res1b p om mm F x / ↑(Real.sqrt (Del p (x 0)))) := by
  have hy : (fun z => yPos p (-1) F z 0) = fun z => ↑(prePos p z) * g1 p (-1) F z := by funext z; exact yPos_0 p (-1) F z
  rw [hy, Dp_prePos_mul p hx _ (diff_g1_slice p (-1) hx hF), Dp_g1 p (-1) hx hF,
    mulVec_entry0, mulVec_entry0, cIaddB_00, cIaddB_01, A_00, A_01, B_00, B_01, yPos_0, yPos_1, yPos_0, yPos_1]
  unfold res1a res1b Dop DopDag Lop LopDag threeIaSin threeOverRhoStar Fplus Fminus lamPosP cscalar bcoeff Qhat cotR Kfreq Del' g1 g2
  unfold Dp
  have hD : 0 < Del p (x 0) := Del_pos p hx.1
  have hDne : (↑(Del p (x 0)) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have hsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 2 = ↑(Del p (x 0)) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hD.le]
  have hs : (↑(Real.sin (x 1)) : ℂ) ≠ 0 := by exact_mod_cast (sin_pos_of_mem p hx).ne'
  have hr := rhoBar_ne_zero p hx; have hrs := rhoBarStar_ne_zero p hx
  have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
  have hpre : (↑(prePos p x) : ℂ) ≠ 0 := by exact_mod_cast (prePos_pos p hx).ne'
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

/-- Component 1 of the Dp-equation of (4), ς = +1. -/
theorem ident_p1 (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (F : PosFields) (hF : PosDiff F x) :
    Dp p (fun z => yPos p (-1) F z 1) x + (A p x *ᵥ yPos p (-1) F x) 1
      - ((cscalar p 1 om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p 1 om mm x) *ᵥ yPos p 1 F x) 1
    = ↑(prePos p x) * ((-2 * ↑p.Q) * (-I * res1c p om mm F x + res1d p om mm F x / ↑(Real.sqrt (Del p (x 0))))) := by
  have hy : (fun z => yPos p (-1) F z 1) = fun z => ↑(prePos p z) * g2 p (-1) F z := by funext z; exact yPos_1 p (-1) F z
  rw [hy, Dp_prePos_mul p hx _ (diff_g2_slice p (-1) hx hF), Dp_g2 p (-1) hx hF,
    mulVec_entry1, mulVec_entry1, cIaddB_10, cIaddB_11, A_10, A_11, B_10, B_11, yPos_0, yPos_1, yPos_0, yPos_1]
  unfold res1c res1d Dop DopDag Lop LopDag threeIaSin threeOverRhoStar lamPosP cscalar bcoeff Qhat cotR Kfreq Del' g1 g2
  unfold Dp
  have hD : 0 < Del p (x 0) := Del_pos p hx.1
  have hDne : (↑(Del p (x 0)) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have hsq : (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 2 = ↑(Del p (x 0)) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hD.le]
  have hs : (↑(Real.sin (x 1)) : ℂ) ≠ 0 := by exact_mod_cast (sin_pos_of_mem p hx).ne'
  have hr := rhoBar_ne_zero p hx; have hrs := rhoBarStar_ne_zero p hx
  have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
  have hpre : (↑(prePos p x) : ℂ) ≠ 0 := by exact_mod_cast (prePos_pos p hx).ne'
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
