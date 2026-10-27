import Hintz2026.Eq1to4Neg

-- Hintz 2026 - Local equivalence (1) <-> (4) at a point of U, both spins.
-- From the eight residual identities  LHS₄ = pre · W · res  with W block-invertible
-- (rows (−i, 1/√Δ) / (i, 1/√Δ) etc.) and pre ≠ 0 on U.

open Complex Function Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-- System (4), ς, at x, for a pair of fields (vector form, as in `system4_iff_system7`). -/
def Sys4At (sg om mm : ℝ) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (x : Fin 2 -> ℝ) : Prop :=
  (fun j => Dm p (fun z => yplus z j) x) - A p x *ᵥ yplus x =
      (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) *ᵥ yminus x ∧
  (fun j => Dp p (fun z => yminus z j) x) + A p x *ᵥ yminus x =
      (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) *ᵥ yplus x

/-- System (1), positive spin, at x: the four residuals vanish. -/
def Sys1PosAt (om mm : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : Prop :=
  res1a p om mm F x = 0 ∧ res1b p om mm F x = 0 ∧ res1c p om mm F x = 0 ∧ res1d p om mm F x = 0

/-- System (1), negative spin (replacement rules), at x. -/
def Sys1NegAt (om mm : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : Prop :=
  res1aN p om mm G x = 0 ∧ res1bN p om mm G x = 0 ∧ res1cN p om mm G x = 0 ∧ res1dN p om mm G x = 0

/-! ### vector-equation ↔ componentwise -/

theorem vec2_eq_iff (u v : Fin 2 -> ℂ) : u = v ↔ u 0 = v 0 ∧ u 1 = v 1 := by
  constructor
  · intro h; exact ⟨congr_fun h 0, congr_fun h 1⟩
  · rintro ⟨h0, h1⟩; funext i; fin_cases i <;> assumption

theorem sub_eq_iff_sub_sub (a b c : ℂ) : a - b = c ↔ a - b - c = 0 := by constructor <;> intro h <;> linear_combination h
theorem add_eq_iff_add_sub (a b c : ℂ) : a + b = c ↔ a + b - c = 0 := by constructor <;> intro h <;> linear_combination h

/-! ### 2×2 eliminations -/

theorem elim_pm {s : ℂ} (hs : s ≠ 0) {a b : ℂ} (h1 : -I * a + b / s = 0) (h2 : I * a + b / s = 0) : a = 0 ∧ b = 0 := by
  have hb : b / s = 0 := by linear_combination (1/2 : ℂ) * h1 + (1/2 : ℂ) * h2
  have hb' : b = 0 := by rcases div_eq_zero_iff.mp hb with h | h; exact h; exact absurd h hs
  have ha : I * a = 0 := by linear_combination (-(1/2) : ℂ) * h1 + (1/2 : ℂ) * h2
  exact ⟨by rcases mul_eq_zero.mp ha with h | h; exact absurd h I_ne_zero; exact h, hb'⟩

theorem elim_pm' {s : ℂ} (hs : s ≠ 0) {a b : ℂ} (h1 : -I * a + s * b = 0) (h2 : I * a + s * b = 0) : a = 0 ∧ b = 0 := by
  have hb : s * b = 0 := by linear_combination (1/2 : ℂ) * h1 + (1/2 : ℂ) * h2
  have hb' : b = 0 := by rcases mul_eq_zero.mp hb with h | h; exact absurd h hs; exact h
  have ha : I * a = 0 := by linear_combination (-(1/2) : ℂ) * h1 + (1/2 : ℂ) * h2
  exact ⟨by rcases mul_eq_zero.mp ha with h | h; exact absurd h I_ne_zero; exact h, hb'⟩

theorem elim_pm_neg {s : ℂ} (hs : s ≠ 0) {a b : ℂ} (h1 : -I * a - s * b = 0) (h2 : I * a - s * b = 0) : a = 0 ∧ b = 0 := by
  have hb : s * b = 0 := by linear_combination (-(1/2) : ℂ) * h1 - (1/2 : ℂ) * h2
  have hb' : b = 0 := by rcases mul_eq_zero.mp hb with h | h; exact absurd h hs; exact h
  have ha : I * a = 0 := by linear_combination (-(1/2) : ℂ) * h1 + (1/2 : ℂ) * h2
  exact ⟨by rcases mul_eq_zero.mp ha with h | h; exact absurd h I_ne_zero; exact h, hb'⟩

/-! ### Positive spin: (1) ↔ (4) with ς = +1 -/

theorem sys1_iff_sys4_pos (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (F : PosFields) (hF : PosDiff F x) :
    Sys1PosAt p om mm F x ↔ Sys4At p 1 om mm (yPos p 1 F) (yPos p (-1) F) x := by
  have hpre : (↑(prePos p x) : ℂ) ≠ 0 := by exact_mod_cast (prePos_pos p hx).ne'
  have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (Del_pos p hx.1)).ne'
  have hQ : (-2 * (↑p.Q : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast p.hQ)
  have m0 := ident_m0 p om mm hx F hF; have m1 := ident_m1 p om mm hx F hF
  have p0 := ident_p0 p om mm hx F hF; have p1 := ident_p1 p om mm hx F hF
  unfold Sys1PosAt Sys4At
  rw [vec2_eq_iff, vec2_eq_iff]
  simp only [Pi.sub_apply, Pi.add_apply]
  constructor
  · rintro ⟨ha, hb, hc, hd⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [sub_eq_iff_sub_sub, m0, ha, hb]; simp
    · rw [sub_eq_iff_sub_sub, m1, hc, hd]; simp
    · rw [add_eq_iff_add_sub, p0, ha, hb]; simp
    · rw [add_eq_iff_add_sub, p1, hc, hd]; simp
  · rintro ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩
    rw [sub_eq_iff_sub_sub, m0] at h0
    rw [sub_eq_iff_sub_sub, m1] at h1
    rw [add_eq_iff_add_sub, p0] at h2
    rw [add_eq_iff_add_sub, p1] at h3
    have e0 : -I * res1a p om mm F x + res1b p om mm F x / ↑(Real.sqrt (Del p (x 0))) = 0 :=
      (mul_eq_zero.mp h0).resolve_left hpre
    have e2 : I * res1a p om mm F x + res1b p om mm F x / ↑(Real.sqrt (Del p (x 0))) = 0 :=
      (mul_eq_zero.mp h2).resolve_left hpre
    have e1 : I * res1c p om mm F x + res1d p om mm F x / ↑(Real.sqrt (Del p (x 0))) = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hpre)).resolve_left hQ
    have e3 : -I * res1c p om mm F x + res1d p om mm F x / ↑(Real.sqrt (Del p (x 0))) = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hpre)).resolve_left hQ
    obtain ⟨ha, hb⟩ := elim_pm hsD e0 e2
    obtain ⟨hc, hd⟩ := elim_pm hsD e3 e1
    exact ⟨ha, hb, hc, hd⟩

/-! ### Negative spin: (1)⁻ ↔ (4) with ς = −1 -/

theorem sys1_iff_sys4_neg (om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) (G : NegFields) (hG : NegDiff G x) :
    Sys1NegAt p om mm G x ↔ Sys4At p (-1) om mm (yNeg p 1 G) (yNeg p (-1) G) x := by
  have hpre : (↑(preNeg p x) : ℂ) ≠ 0 := by exact_mod_cast (preNeg_pos p hx).ne'
  have hsD : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (Del_pos p hx.1)).ne'
  have hQ : (2 * (↑p.Q : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (by exact_mod_cast p.hQ)
  have m0 := identN_m0 p om mm hx G hG; have m1 := identN_m1 p om mm hx G hG
  have p0 := identN_p0 p om mm hx G hG; have p1 := identN_p1 p om mm hx G hG
  unfold Sys1NegAt Sys4At
  rw [vec2_eq_iff, vec2_eq_iff]
  simp only [Pi.sub_apply, Pi.add_apply]
  constructor
  · rintro ⟨ha, hb, hc, hd⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [sub_eq_iff_sub_sub, m0, ha, hb]; simp
    · rw [sub_eq_iff_sub_sub, m1, hc, hd]; simp
    · rw [add_eq_iff_add_sub, p0, ha, hb]; simp
    · rw [add_eq_iff_add_sub, p1, hc, hd]; simp
  · rintro ⟨⟨h0, h1⟩, ⟨h2, h3⟩⟩
    rw [sub_eq_iff_sub_sub, m0] at h0
    rw [sub_eq_iff_sub_sub, m1] at h1
    rw [add_eq_iff_add_sub, p0] at h2
    rw [add_eq_iff_add_sub, p1] at h3
    have e0 : -I * res1aN p om mm G x + ↑(Real.sqrt (Del p (x 0))) * res1bN p om mm G x = 0 :=
      (mul_eq_zero.mp h0).resolve_left hpre
    have e2 : I * res1aN p om mm G x + ↑(Real.sqrt (Del p (x 0))) * res1bN p om mm G x = 0 :=
      (mul_eq_zero.mp h2).resolve_left hpre
    have e1 : -I * res1cN p om mm G x - ↑(Real.sqrt (Del p (x 0))) * res1dN p om mm G x = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hpre)).resolve_left hQ
    have e3 : I * res1cN p om mm G x - ↑(Real.sqrt (Del p (x 0))) * res1dN p om mm G x = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hpre)).resolve_left hQ
    obtain ⟨ha, hb⟩ := elim_pm' hsD e0 e2
    obtain ⟨hc, hd⟩ := elim_pm_neg hsD e1 e3
    exact ⟨ha, hb, hc, hd⟩

end Hintz2026

end
