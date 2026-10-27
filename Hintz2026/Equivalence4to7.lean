import Hintz2026.AdjDeriv
import Hintz2026.CAdjugate

-- Hintz 2026 - Equivalence (4) to (7)
-- System (4): (Dm - A) y+ = (c*1 - B) y-,  (Dp + A) y- = (c*1 + B) y+
-- System (7): Dm(z+) = C z-, Dp(z-) = adj(C) z+
--   where z+ = adj(X) y+, z- = X^H y-, C = adj(X) (c*1-B) (X^H)^{-1}

open Complex Matrix Function
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

theorem hadj_of_smooth {x : Fin 2 -> ℝ} (hx : x ∈ U p) (i j k : Fin 2) :
    DifferentiableAt ℝ (fun u => adjugate (X p (update x k u)) i j) (x k) := by
  have heq : Set.EqOn (fun z => adjugate (X p z) i j)
      (fun z => ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) * (X p z)⁻¹ i j) (U p) :=
    fun z hz => adj_X_entry_eq p hz i j
  have hsm : ContDiffOn ℝ ∞ (fun z => ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) * (X p z)⁻¹ i j) (U p) :=
    contDiffOn_const.mul ((contDiffOn_Xinv_entry p i j).of_le le_top)
  have hsm' : ContDiffOn ℝ ∞ (fun z => adjugate (X p z) i j) (U p) :=
    hsm.congr (fun z hz => heq hz)
  exact differentiableAt_slice p hsm' hx k

theorem hXstar_of_smooth {x : Fin 2 -> ℝ} (hx : x ∈ U p) (i j k : Fin 2) :
    DifferentiableAt ℝ (fun u => (X p (update x k u))ᴴ i j) (x k) :=
  differentiableAt_slice p ((contDiffOn_Xstar_entry p i j).of_le le_top) hx k

-- Dm(adj X · y+) = -(adj X) A y+ + adj X · Dm y+
theorem Dm_adj_mulVec {x : Fin 2 -> ℝ} (hx : x ∈ U p)
    (y : (Fin 2 -> ℝ) -> Fin 2 -> ℂ)
    (hy : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => y x j) (U p)) :
    (fun i => Dm p (fun z => (adjugate (X p z) *ᵥ y z) i) x) =
    -(adjugate (X p x) * A p x) *ᵥ y x + adjugate (X p x) *ᵥ (fun j => Dm p (fun z => y z j) x) := by
  ext i
  rw [Dm_mulVec_entry p (fun z => adjugate (X p z)) y x i
    (fun j k => hadj_of_smooth p hx i j k) (fun j k => hv_of_smooth p hy hx j k)]
  rw [Dm_adj_matrix p hx]
  rfl

-- Dp(X^H · y-) = X^H A y- + X^H · Dp y-
theorem Dp_Xstar_mulVec {x : Fin 2 -> ℝ} (hx : x ∈ U p)
    (y : (Fin 2 -> ℝ) -> Fin 2 -> ℂ)
    (hy : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => y x j) (U p)) :
    (fun i => Dp p (fun z => ((X p z)ᴴ *ᵥ y z) i) x) =
    ((X p x)ᴴ * A p x) *ᵥ y x + (X p x)ᴴ *ᵥ (fun j => Dp p (fun z => y z j) x) := by
  ext i
  rw [Dp_mulVec_entry p (fun z => (X p z)ᴴ) y x i
    (fun j k => hXstar_of_smooth p hx i j k) (fun j k => hv_of_smooth p hy hx j k)]
  rw [Dp_Xstar_matrix p hx]
  rfl

-- C * X^H = adj(X) * (c*1 - B)
theorem Cmat_mul_Xstar (sg om mm : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Cmat p sg om mm x * (X p x)ᴴ = adjugate (X p x) * (cscalar p sg om mm x • 1 - Bmat p sg om mm x) := by
  unfold Cmat
  rw [Matrix.smul_mul, Matrix.mul_assoc, inv_mul_Xstar p hx, Matrix.mul_one,
    ← Matrix.smul_mul, detX_Xinv_eq_adj p hx]

/-- System (7) z+ from system (4). -/
theorem system7_zplus_of_system4
    (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ)
    (sg om mm : ℝ)
    (hyp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yplus x j) (U p))
    (hym : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yminus x j) (U p))
    {x : Fin 2 -> ℝ} (hx : x ∈ U p)
    (h4 : (fun j => Dm p (fun z => yplus z j) x) - A p x *ᵥ yplus x =
      (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) *ᵥ yminus x) :
    (fun i => Dm p (fun z => (adjugate (X p z) *ᵥ yplus z) i) x) =
      Cmat p sg om mm x *ᵥ zminus p yminus x := by
  rw [Dm_adj_mulVec p hx yplus hyp]
  -- Dm y+ = A y+ + (cI-B) y-
  have hDm : (fun j => Dm p (fun z => yplus z j) x) =
      A p x *ᵥ yplus x + (cscalar p sg om mm x • 1 - Bmat p sg om mm x) *ᵥ yminus x := by
    rw [← h4]; abel
  rw [hDm, mulVec_add, mulVec_mulVec, mulVec_mulVec, neg_mulVec]
  simp only [neg_add_cancel_left]
  unfold zminus
  rw [mulVec_mulVec, Cmat_mul_Xstar p sg om mm hx]

/-- System (7) z- from system (4). -/
theorem system7_zminus_of_system4
    (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ)
    (sg om mm : ℝ)
    (hyp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yplus x j) (U p))
    (hym : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yminus x j) (U p))
    {x : Fin 2 -> ℝ} (hx : x ∈ U p)
    (h4 : (fun j => Dp p (fun z => yminus z j) x) + A p x *ᵥ yminus x =
      (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) *ᵥ yplus x) :
    (fun i => Dp p (fun z => ((X p z)ᴴ *ᵥ yminus z) i) x) =
      adjugate (Cmat p sg om mm x) *ᵥ zplus p yplus x := by
  rw [Dp_Xstar_mulVec p hx yminus hym]
  have hDp : (fun j => Dp p (fun z => yminus z j) x) =
      -(A p x *ᵥ yminus x) + (cscalar p sg om mm x • 1 + Bmat p sg om mm x) *ᵥ yplus x := by
    rw [← h4]; abel
  rw [hDp, mulVec_add, mulVec_neg, mulVec_mulVec, mulVec_mulVec]
  simp only [add_neg_cancel_left]
  unfold zplus
  rw [mulVec_mulVec]
  congr 1
  -- X^H (c*1 + B) = adj(C) adj(X) via adj(C) = k⁻¹ • X^H (cI+B) X and X adj(X) = k • 1
  rw [adjugate_Cmat_eq p sg om mm hx, Matrix.smul_mul, Matrix.mul_assoc, mul_adjugate, det_X p hx,
    Matrix.mul_smul, Matrix.mul_one, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Q_sq_sub_M_sq_ne_zero p), one_smul]

end Hintz2026

end

namespace Hintz2026

variable (p : SubextremalKN)

open scoped ContDiff

-- ===== Reverse direction (7) -> (4) =====
-- Given arbitrary smooth fields zp, zm with Dm zp = C zm (resp. Dp zm = adj(C) zp) at x,
-- the fields y+ := k⁻¹ X zp, y- := (X^H)⁻¹ zm satisfy system (4) at x.

theorem kinv_X_mulVec_eq (x : Fin 2 -> ℝ) (w : Fin 2 -> ℂ) :
    ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p x *ᵥ w) = (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • X p x) *ᵥ w := by
  rw [smul_mulVec]

theorem system4_yplus_of_system7
    (zp zm : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (sg om mm : ℝ)
    (hzp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => zp x j) (U p))
    {x : Fin 2 -> ℝ} (hx : x ∈ U p)
    (h7 : (fun i => Dm p (fun z => zp z i) x) = Cmat p sg om mm x *ᵥ zm x) :
    (fun j => Dm p (fun z => (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p z *ᵥ zp z)) j) x)
        - A p x *ᵥ (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p x *ᵥ zp x)) =
      (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ zm x) := by
  -- scalar k⁻¹ pulls out of Dm and of A·(·)
  have hk : ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Q_sq_sub_M_sq_ne_zero p
  have hDmk : ∀ j, Dm p (fun z => ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ * (X p z *ᵥ zp z) j) x
      = ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ * Dm p (fun z => (X p z *ᵥ zp z) j) x := by
    intro j; unfold Dm cpd
    simp only [deriv_const_mul_field]; ring
  have hres := Dm_Xv_sub_AXv p hx zp (fun i j k => hX_of_smooth p hx i j k) (fun j k => hv_of_smooth p hzp hx j k)
  -- LHS = k⁻¹ • (Dm(X zp) - A (X zp)) = k⁻¹ • X Dm zp = k⁻¹ • X C zm
  have hL : (fun j => Dm p (fun z => (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p z *ᵥ zp z)) j) x)
        - A p x *ᵥ (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p x *ᵥ zp x))
      = ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • ((fun i => Dm p (fun z => (X p z *ᵥ zp z) i) x) - A p x *ᵥ (X p x *ᵥ zp x)) := by
    ext j; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mulVec_smul]; rw [hDmk]; ring
  rw [hL, hres, h7, mulVec_mulVec]
  -- X C = X k⁻¹ adj(X)(cI-B)(X^H)⁻¹... use Cmat def directly: X * (det • X⁻¹ * M * Yinv) = det • M * Yinv
  unfold Cmat
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, X_mul_inv p hx, Matrix.one_mul,
    det_X p hx, smul_mulVec, smul_smul, inv_mul_cancel₀ hk, one_smul, ← mulVec_mulVec]

theorem system4_yminus_of_system7
    (zp zm : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (sg om mm : ℝ)
    (hzm : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => zm x j) (U p))
    {x : Fin 2 -> ℝ} (hx : x ∈ U p)
    (h7 : (fun i => Dp p (fun z => zm z i) x) = adjugate (Cmat p sg om mm x) *ᵥ zp x) :
    (fun j => Dp p (fun z => (((X p z)ᴴ)⁻¹ *ᵥ zm z) j) x) + A p x *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ zm x) =
      (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) *ᵥ
        (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p x *ᵥ zp x)) := by
  have hres := Dp_Yv_add_AYv p hx zm (fun i j k => hY_of_smooth p hx i j k) (fun j k => hv_of_smooth p hzm hx j k)
  rw [hres, h7, adjugate_Cmat_eq p sg om mm hx, smul_mulVec, mulVec_smul, mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, inv_mul_Xstar p hx, Matrix.one_mul]
  rw [mulVec_smul, mulVec_mulVec]

-- ===== Two-sided local equivalence at a point of U =====
-- For smooth y+, y-: system (4) at x  <->  system (7) at x for z+ = adj(X) y+, z- = X^H y-.
theorem system4_iff_system7
    (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (sg om mm : ℝ)
    (hyp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yplus x j) (U p))
    (hym : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => yminus x j) (U p))
    {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    ((fun j => Dm p (fun z => yplus z j) x) - A p x *ᵥ yplus x =
        (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) *ᵥ yminus x ∧
     (fun j => Dp p (fun z => yminus z j) x) + A p x *ᵥ yminus x =
        (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) *ᵥ yplus x)
    ↔
    ((fun i => Dm p (fun z => (adjugate (X p z) *ᵥ yplus z) i) x) = Cmat p sg om mm x *ᵥ ((X p x)ᴴ *ᵥ yminus x) ∧
     (fun i => Dp p (fun z => ((X p z)ᴴ *ᵥ yminus z) i) x) = adjugate (Cmat p sg om mm x) *ᵥ (adjugate (X p x) *ᵥ yplus x)) := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨system7_zplus_of_system4 p yplus yminus sg om mm hyp hym hx h1,
           system7_zminus_of_system4 p yplus yminus sg om mm hyp hym hx h2⟩
  · rintro ⟨h1, h2⟩
    -- apply the reverse direction to zp := adj(X) y+, zm := X^H y-, then undo the round trips
    have hzp : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => (adjugate (X p x) *ᵥ yplus x) j) (U p) := by
      intro j; simp only [mulVec, dotProduct, Fin.sum_univ_two]
      have ha : ∀ a b, ContDiffOn ℝ ∞ (fun x => adjugate (X p x) a b) (U p) := by
        intro a b
        have heq : Set.EqOn (fun z => adjugate (X p z) a b)
            (fun z => ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) * (X p z)⁻¹ a b) (U p) := fun z hz => adj_X_entry_eq p hz a b
        exact (contDiffOn_const.mul ((contDiffOn_Xinv_entry p a b).of_le le_top)).congr (fun z hz => heq hz)
      exact ((ha j 0).mul (hyp 0)).add ((ha j 1).mul (hyp 1))
    have hzm : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => ((X p x)ᴴ *ᵥ yminus x) j) (U p) :=
      fun j => contDiffOn_Xstar_mulVec p hym j
    have r1 := system4_yplus_of_system7 p (fun z => adjugate (X p z) *ᵥ yplus z) (fun z => (X p z)ᴴ *ᵥ yminus z) sg om mm hzp hx h1
    have r2 := system4_yminus_of_system7 p (fun z => adjugate (X p z) *ᵥ yplus z) (fun z => (X p z)ᴴ *ᵥ yminus z) sg om mm hzm hx h2
    -- round trips: k⁻¹ X adj(X) y+ = y+ on U ; (X^H)⁻¹ X^H y- = y- on U
    have hrt1 : Set.EqOn (fun z => ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p z *ᵥ (adjugate (X p z) *ᵥ yplus z))) yplus (U p) := by
      intro z hz; simp only
      rw [mulVec_mulVec, mul_adjugate, det_X p hz, smul_mulVec, one_mulVec, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast Q_sq_sub_M_sq_ne_zero p), one_smul]
    have hrt2 : Set.EqOn (fun z => ((X p z)ᴴ)⁻¹ *ᵥ ((X p z)ᴴ *ᵥ yminus z)) yminus (U p) := by
      intro z hz; simp only; rw [mulVec_mulVec, inv_mul_Xstar p hz, one_mulVec]
    have e1 : ∀ j, Dm p (fun z => (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ)⁻¹ • (X p z *ᵥ (adjugate (X p z) *ᵥ yplus z))) j) x
        = Dm p (fun z => yplus z j) x := fun j => Dm_congr p hx (fun z hz => congr_fun (hrt1 hz) j)
    have e2 : ∀ j, Dp p (fun z => (((X p z)ᴴ)⁻¹ *ᵥ ((X p z)ᴴ *ᵥ yminus z)) j) x
        = Dp p (fun z => yminus z j) x := fun j => Dp_congr p hx (fun z hz => congr_fun (hrt2 hz) j)
    simp only [e1, e2, hrt1 hx, hrt2 hx] at r1 r2
    exact ⟨r1, r2⟩

end Hintz2026
