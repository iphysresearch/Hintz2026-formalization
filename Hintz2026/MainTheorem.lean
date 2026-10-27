import Hintz2026.ChiralSmooth
import Hintz2026.Equivalence4to7

-- Hintz 2026 - MAIN THEOREM: local equivalence (1) <-> (4) <-> (7) on U for C∞ fields, both spins,
-- with explicit forward map T : (ψ₂,ψ₁,k,s) ↦ (y₊,y₋) ↦ (z₊,z₋) and its inverse.

open Complex Function Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-- System (7) at x for the transformed variables z₊ = adj(X) y₊, z₋ = X^H y₋ of (y₊, y₋):
    Dm z₊ = C z₋,  Dp z₋ = adj(C) z₊. -/
def Sys7At (sg om mm : ℝ) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (x : Fin 2 -> ℝ) : Prop :=
  (fun i => Dm p (fun z => (adjugate (X p z) *ᵥ yplus z) i) x) = Cmat p sg om mm x *ᵥ ((X p x)ᴴ *ᵥ yminus x) ∧
  (fun i => Dp p (fun z => ((X p z)ᴴ *ᵥ yminus z) i) x) = adjugate (Cmat p sg om mm x) *ᵥ (adjugate (X p x) *ᵥ yplus x)

theorem sys4_iff_sys7 (sg om mm : ℝ) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ)
    (hyp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yplus x j) (U p))
    (hym : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yminus x j) (U p))
    {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Sys4At p sg om mm yplus yminus x ↔ Sys7At p sg om mm yplus yminus x :=
  system4_iff_system7 p yplus yminus sg om mm hyp hym hx

/-! ### Main theorem, positive spin (ς = +1) -/

/-- (1) ⟺ (4) ⟺ (7) at every x ∈ U, for C∞ fields (ψ₂, ψ₁, k, s). -/
theorem main_pos (om mm : ℝ) (F : PosFields) (hF : PosSmooth p F) {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Sys1PosAt p om mm F x ↔ Sys7At p 1 om mm (yPos p 1 F) (yPos p (-1) F) x :=
  (sys1_iff_sys4_pos p om mm hx F (posDiff_of_smooth p hF hx)).trans
    (sys4_iff_sys7 p 1 om mm _ _ (contDiffOn_yPos p hF 1) (contDiffOn_yPos p hF (-1)) hx)

theorem main_pos_on_U (om mm : ℝ) (F : PosFields) (hF : PosSmooth p F) :
    (∀ x ∈ U p, Sys1PosAt p om mm F x) ↔ (∀ x ∈ U p, Sys7At p 1 om mm (yPos p 1 F) (yPos p (-1) F) x) :=
  forall₂_congr (fun x hx => main_pos p om mm F hF hx)

/-! ### Main theorem, negative spin (ς = −1) -/

theorem main_neg (om mm : ℝ) (G : NegFields) (hG : NegSmooth p G) {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Sys1NegAt p om mm G x ↔ Sys7At p (-1) om mm (yNeg p 1 G) (yNeg p (-1) G) x :=
  (sys1_iff_sys4_neg p om mm hx G (negDiff_of_smooth p hG hx)).trans
    (sys4_iff_sys7 p (-1) om mm _ _ (contDiffOn_yNeg p hG 1) (contDiffOn_yNeg p hG (-1)) hx)

theorem main_neg_on_U (om mm : ℝ) (G : NegFields) (hG : NegSmooth p G) :
    (∀ x ∈ U p, Sys1NegAt p om mm G x) ↔ (∀ x ∈ U p, Sys7At p (-1) om mm (yNeg p 1 G) (yNeg p (-1) G) x) :=
  forall₂_congr (fun x hx => main_neg p om mm G hG hx)

/-! ### The inverse chiral map T⁻¹ (positive spin) and round trips on U -/

/-- From a pair (y₊, y₋) recover (ψ₂, ψ₁, k, s):
    ψ₂ = (y₊⁰ + y₋⁰)/(2 pre),  ψ₁ = √Δ (y₊⁰ − y₋⁰)/(2i pre),
    k  = −(y₊¹ + y₋¹)/(4Q pre),  s = −√Δ (y₊¹ − y₋¹)/(4iQ pre). -/
def invPos (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) : PosFields where
  psi2 := fun z => (yplus z 0 + yminus z 0) / (2 * ↑(prePos p z))
  psi1 := fun z => ↑(Real.sqrt (Del p (z 0))) * (yplus z 0 - yminus z 0) / (2 * I * ↑(prePos p z))
  k    := fun z => -(yplus z 1 + yminus z 1) / (4 * ↑p.Q * ↑(prePos p z))
  s    := fun z => -(↑(Real.sqrt (Del p (z 0))) * (yplus z 1 - yminus z 1)) / (4 * I * ↑p.Q * ↑(prePos p z))

theorem yPos_invPos (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) {z : Fin 2 -> ℝ} (hz : z ∈ U p) :
    yPos p 1 (invPos p yplus yminus) z = yplus z ∧ yPos p (-1) (invPos p yplus yminus) z = yminus z := by
  have hpre : (↑(prePos p z) : ℂ) ≠ 0 := by exact_mod_cast (prePos_pos p hz).ne'
  have hsD : (↑(Real.sqrt (Del p (z 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (Del_pos p hz.1)).ne'
  have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
  constructor <;> (funext i; fin_cases i) <;> simp only [yPos, invPos] <;>
    field_simp <;> push_cast <;> ring

theorem invPos_yPos (F : PosFields) {z : Fin 2 -> ℝ} (hz : z ∈ U p) :
    (invPos p (yPos p 1 F) (yPos p (-1) F)).psi2 z = F.psi2 z ∧
    (invPos p (yPos p 1 F) (yPos p (-1) F)).psi1 z = F.psi1 z ∧
    (invPos p (yPos p 1 F) (yPos p (-1) F)).k z = F.k z ∧
    (invPos p (yPos p 1 F) (yPos p (-1) F)).s z = F.s z := by
  have hpre : (↑(prePos p z) : ℂ) ≠ 0 := by exact_mod_cast (prePos_pos p hz).ne'
  have hsD : (↑(Real.sqrt (Del p (z 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (Del_pos p hz.1)).ne'
  have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
  simp only [invPos, yPos, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> push_cast <;> ring

/-! ### The inverse chiral map (negative spin) -/

def invNeg (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) : NegFields where
  psim2 := fun z => (yplus z 0 + yminus z 0) / (2 * ↑(preNeg p z))
  psim1 := fun z => -(yplus z 0 - yminus z 0) / (2 * I * ↑(Real.sqrt (Del p (z 0))) * ↑(preNeg p z))
  n     := fun z => (yplus z 1 + yminus z 1) / (4 * ↑p.Q * ↑(preNeg p z))
  l     := fun z => -(yplus z 1 - yminus z 1) / (4 * I * ↑p.Q * ↑(Real.sqrt (Del p (z 0))) * ↑(preNeg p z))

theorem yNeg_invNeg (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) {z : Fin 2 -> ℝ} (hz : z ∈ U p) :
    yNeg p 1 (invNeg p yplus yminus) z = yplus z ∧ yNeg p (-1) (invNeg p yplus yminus) z = yminus z := by
  have hpre : (↑(preNeg p z) : ℂ) ≠ 0 := by exact_mod_cast (preNeg_pos p hz).ne'
  have hsD : (↑(Real.sqrt (Del p (z 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (Del_pos p hz.1)).ne'
  have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
  constructor <;> (funext i; fin_cases i) <;> simp only [yNeg, invNeg] <;>
    field_simp <;> push_cast <;> ring

theorem invNeg_yNeg (G : NegFields) {z : Fin 2 -> ℝ} (hz : z ∈ U p) :
    (invNeg p (yNeg p 1 G) (yNeg p (-1) G)).psim2 z = G.psim2 z ∧
    (invNeg p (yNeg p 1 G) (yNeg p (-1) G)).psim1 z = G.psim1 z ∧
    (invNeg p (yNeg p 1 G) (yNeg p (-1) G)).n z = G.n z ∧
    (invNeg p (yNeg p 1 G) (yNeg p (-1) G)).l z = G.l z := by
  have hpre : (↑(preNeg p z) : ℂ) ≠ 0 := by exact_mod_cast (preNeg_pos p hz).ne'
  have hsD : (↑(Real.sqrt (Del p (z 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (Del_pos p hz.1)).ne'
  have hQ : (↑p.Q : ℂ) ≠ 0 := by exact_mod_cast p.hQ
  simp only [invNeg, yNeg, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> field_simp <;> push_cast <;> ring

/-! ### Single goal: both spins, all C∞ fields, all points of U -/

/-- **Main theorem.** For every frequency ω and azimuthal number m, every C∞ positive-spin field
    (ψ₂,ψ₁,k,s) and every C∞ negative-spin field (ψ₋₂,ψ₋₁,n,ℓ) on U:
    system (1) holds at x ∈ U  ⟺  system (7) holds at x for the transformed variables
    z₊ = adj(X) y₊, z₋ = X^H y₋, with y± the chiral variables (3) of the respective spin. -/
theorem main (om mm : ℝ) :
    (∀ F : PosFields, PosSmooth p F → ∀ x ∈ U p,
        (Sys1PosAt p om mm F x ↔ Sys7At p 1 om mm (yPos p 1 F) (yPos p (-1) F) x)) ∧
    (∀ G : NegFields, NegSmooth p G → ∀ x ∈ U p,
        (Sys1NegAt p om mm G x ↔ Sys7At p (-1) om mm (yNeg p 1 G) (yNeg p (-1) G) x)) :=
  ⟨fun F hF x hx => main_pos p om mm F hF hx, fun G hG x hx => main_neg p om mm G hG hx⟩

end Hintz2026

end
