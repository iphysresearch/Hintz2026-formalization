import Hintz2026.Assembly

/-!
# Hintz 2026 — Residual identities, solution correspondence, negative control

**C.** D₋(Xv) − A·(Xv) = X·(D₋v)  and  D₊(Yv) + A·(Yv) = Y·(D₊v)
**D.** Round-trip: X⁻¹(X·w)=w, X(X⁻¹·w)=w, Xᴴ(Y·w)=w, Y(Xᴴ·w)=w
**E.** Negative control: Dbad = √Δ·∂r fails the integrating-factor equation
-/

open Complex Matrix Function
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

/-! ═══ cpd / Dm / Dp calculus ═══ -/

theorem cpd_mul (k : Fin 2) (f g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ)
    (hf : DifferentiableAt ℝ (fun u => f (update x k u)) (x k))
    (hg : DifferentiableAt ℝ (fun u => g (update x k u)) (x k)) :
    cpd k (fun z => f z * g z) x = cpd k f x * g x + f x * cpd k g x := by
  unfold cpd
  rw [show (fun u => f (update x k u) * g (update x k u)) =
      (fun u => f (update x k u)) * (fun u => g (update x k u)) from rfl,
      deriv_mul hf hg]; simp only [update_eq_self]

theorem cpd_add (k : Fin 2) (f g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ)
    (hf : DifferentiableAt ℝ (fun u => f (update x k u)) (x k))
    (hg : DifferentiableAt ℝ (fun u => g (update x k u)) (x k)) :
    cpd k (fun z => f z + g z) x = cpd k f x + cpd k g x := by
  unfold cpd
  rw [show (fun u => f (update x k u) + g (update x k u)) =
      (fun u => f (update x k u)) + (fun u => g (update x k u)) from rfl]
  exact deriv_add hf hg

theorem Dm_add (f g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ)
    (hf0 : DifferentiableAt ℝ (fun u => f (update x 0 u)) (x 0))
    (hg0 : DifferentiableAt ℝ (fun u => g (update x 0 u)) (x 0))
    (hf1 : DifferentiableAt ℝ (fun u => f (update x 1 u)) (x 1))
    (hg1 : DifferentiableAt ℝ (fun u => g (update x 1 u)) (x 1)) :
    Dm p (fun z => f z + g z) x = Dm p f x + Dm p g x := by
  unfold Dm; rw [cpd_add 0 f g x hf0 hg0, cpd_add 1 f g x hf1 hg1]; ring

theorem Dm_mul (f g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ)
    (hf0 : DifferentiableAt ℝ (fun u => f (update x 0 u)) (x 0))
    (hg0 : DifferentiableAt ℝ (fun u => g (update x 0 u)) (x 0))
    (hf1 : DifferentiableAt ℝ (fun u => f (update x 1 u)) (x 1))
    (hg1 : DifferentiableAt ℝ (fun u => g (update x 1 u)) (x 1)) :
    Dm p (fun z => f z * g z) x = Dm p f x * g x + f x * Dm p g x := by
  unfold Dm; rw [cpd_mul 0 f g x hf0 hg0, cpd_mul 1 f g x hf1 hg1]; ring

theorem Dp_add (f g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ)
    (hf0 : DifferentiableAt ℝ (fun u => f (update x 0 u)) (x 0))
    (hg0 : DifferentiableAt ℝ (fun u => g (update x 0 u)) (x 0))
    (hf1 : DifferentiableAt ℝ (fun u => f (update x 1 u)) (x 1))
    (hg1 : DifferentiableAt ℝ (fun u => g (update x 1 u)) (x 1)) :
    Dp p (fun z => f z + g z) x = Dp p f x + Dp p g x := by
  unfold Dp; rw [cpd_add 0 f g x hf0 hg0, cpd_add 1 f g x hf1 hg1]; ring

theorem Dp_mul (f g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ)
    (hf0 : DifferentiableAt ℝ (fun u => f (update x 0 u)) (x 0))
    (hg0 : DifferentiableAt ℝ (fun u => g (update x 0 u)) (x 0))
    (hf1 : DifferentiableAt ℝ (fun u => f (update x 1 u)) (x 1))
    (hg1 : DifferentiableAt ℝ (fun u => g (update x 1 u)) (x 1)) :
    Dp p (fun z => f z * g z) x = Dp p f x * g x + f x * Dp p g x := by
  unfold Dp; rw [cpd_mul 0 f g x hf0 hg0, cpd_mul 1 f g x hf1 hg1]; ring

/-! ═══ mulVec Leibniz ═══ -/

theorem Dm_mulVec_entry
    (M : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ)
    (w : (Fin 2 → ℝ) → Fin 2 → ℂ) (x : Fin 2 → ℝ) (i : Fin 2)
    (hM : ∀ j k, DifferentiableAt ℝ (fun u => M (update x k u) i j) (x k))
    (hw : ∀ j k, DifferentiableAt ℝ (fun u => w (update x k u) j) (x k)) :
    Dm p (fun z => (M z *ᵥ w z) i) x =
    (of fun a b => Dm p (fun z => M z a b) x).mulVec (w x) i +
    (M x).mulVec (fun j => Dm p (fun z => w z j) x) i := by
  simp only [mulVec, dotProduct, Fin.sum_univ_two, of_apply]
  rw [Dm_add p _ _ x ((hM 0 0).mul (hw 0 0)) ((hM 1 0).mul (hw 1 0))
                      ((hM 0 1).mul (hw 0 1)) ((hM 1 1).mul (hw 1 1)),
      Dm_mul p _ _ x (hM 0 0) (hw 0 0) (hM 0 1) (hw 0 1),
      Dm_mul p _ _ x (hM 1 0) (hw 1 0) (hM 1 1) (hw 1 1)]; ring

theorem Dp_mulVec_entry
    (M : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ)
    (w : (Fin 2 → ℝ) → Fin 2 → ℂ) (x : Fin 2 → ℝ) (i : Fin 2)
    (hM : ∀ j k, DifferentiableAt ℝ (fun u => M (update x k u) i j) (x k))
    (hw : ∀ j k, DifferentiableAt ℝ (fun u => w (update x k u) j) (x k)) :
    Dp p (fun z => (M z *ᵥ w z) i) x =
    (of fun a b => Dp p (fun z => M z a b) x).mulVec (w x) i +
    (M x).mulVec (fun j => Dp p (fun z => w z j) x) i := by
  simp only [mulVec, dotProduct, Fin.sum_univ_two, of_apply]
  rw [Dp_add p _ _ x ((hM 0 0).mul (hw 0 0)) ((hM 1 0).mul (hw 1 0))
                      ((hM 0 1).mul (hw 0 1)) ((hM 1 1).mul (hw 1 1)),
      Dp_mul p _ _ x (hM 0 0) (hw 0 0) (hM 0 1) (hw 0 1),
      Dp_mul p _ _ x (hM 1 0) (hw 1 0) (hM 1 1) (hw 1 1)]; ring

/-! ═══ C: Residual Identities ═══ -/

/-- C1: D₋(Xv)ᵢ − (A·Xv)ᵢ = (X·D₋v)ᵢ — the Dm residual identity. -/
theorem Dm_Xv_sub_AXv {x : Fin 2 → ℝ} (hx : x ∈ U p)
    (v : (Fin 2 → ℝ) → Fin 2 → ℂ)
    (hX : ∀ i j k, DifferentiableAt ℝ (fun u => X p (update x k u) i j) (x k))
    (hv : ∀ j k, DifferentiableAt ℝ (fun u => v (update x k u) j) (x k)) :
    (fun i => Dm p (fun z => (X p z *ᵥ v z) i) x) - A p x *ᵥ (X p x *ᵥ v x) =
    X p x *ᵥ (fun j => Dm p (fun z => v z j) x) := by
  ext i; simp only [Pi.sub_apply]
  rw [Dm_mulVec_entry p (X p) v x i (fun j k => hX i j k) hv]
  have hDmX : (of fun a b => Dm p (fun z => X p z a b) x) = A p x * X p x :=
    Dminus_X_eq_AX p hx
  rw [hDmX, mulVec_mulVec]; simp [add_sub_cancel_left]

/-- C2: D₊(Yv)ᵢ + (A·Yv)ᵢ = (Y·D₊v)ᵢ where Y = (Xᴴ)⁻¹. -/
theorem Dp_Yv_add_AYv {x : Fin 2 → ℝ} (hx : x ∈ U p)
    (v : (Fin 2 → ℝ) → Fin 2 → ℂ)
    (hY : ∀ i j k, DifferentiableAt ℝ (fun u => ((X p (update x k u))ᴴ)⁻¹ i j) (x k))
    (hv : ∀ j k, DifferentiableAt ℝ (fun u => v (update x k u) j) (x k)) :
    (fun i => Dp p (fun z => (((X p z)ᴴ)⁻¹ *ᵥ v z) i) x) +
    A p x *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ v x) =
    ((X p x)ᴴ)⁻¹ *ᵥ (fun j => Dp p (fun z => v z j) x) := by
  ext i; simp only [Pi.add_apply]
  rw [Dp_mulVec_entry p (fun z => ((X p z)ᴴ)⁻¹) v x i (fun j k => hY i j k) hv]
  have hDpY : (of fun a b => Dp p (fun z => ((X p z)ᴴ)⁻¹ a b) x) =
      -A p x * ((X p x)ᴴ)⁻¹ := Dplus_XstarInv_eq p hx
  rw [hDpY, neg_mul, mulVec_mulVec]
  simp only [neg_mulVec, Pi.neg_apply]; ring

/-! ═══ D: Solution correspondence ═══ -/

theorem Xinv_X_mulVec {x : Fin 2 → ℝ} (hx : x ∈ U p) (w : Fin 2 → ℂ) :
    (X p x)⁻¹ *ᵥ (X p x *ᵥ w) = w := by
  rw [mulVec_mulVec, inv_mul_X p hx, one_mulVec]

theorem X_Xinv_mulVec {x : Fin 2 → ℝ} (hx : x ∈ U p) (w : Fin 2 → ℂ) :
    X p x *ᵥ ((X p x)⁻¹ *ᵥ w) = w := by
  rw [mulVec_mulVec, X_mul_inv p hx, one_mulVec]

theorem Xstar_Y_mulVec {x : Fin 2 → ℝ} (hx : x ∈ U p) (w : Fin 2 → ℂ) :
    (X p x)ᴴ *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ w) = w := by
  rw [mulVec_mulVec, Xstar_mul_inv p hx, one_mulVec]

theorem Y_Xstar_mulVec {x : Fin 2 → ℝ} (hx : x ∈ U p) (w : Fin 2 → ℂ) :
    ((X p x)ᴴ)⁻¹ *ᵥ ((X p x)ᴴ *ᵥ w) = w := by
  rw [mulVec_mulVec, inv_mul_Xstar p hx, one_mulVec]

theorem Xinv_X_mulVec_eqOn (w : Fin 2 → ℂ) :
    Set.EqOn (fun z => (X p z)⁻¹ *ᵥ (X p z *ᵥ w)) (fun _ => w) (U p) :=
  fun _ hx => Xinv_X_mulVec p hx w

theorem X_Xinv_mulVec_eqOn (w : Fin 2 → ℂ) :
    Set.EqOn (fun z => X p z *ᵥ ((X p z)⁻¹ *ᵥ w)) (fun _ => w) (U p) :=
  fun _ hx => X_Xinv_mulVec p hx w

theorem Xstar_Y_mulVec_eqOn (w : Fin 2 → ℂ) :
    Set.EqOn (fun z => (X p z)ᴴ *ᵥ (((X p z)ᴴ)⁻¹ *ᵥ w)) (fun _ => w) (U p) :=
  fun _ hx => Xstar_Y_mulVec p hx w

theorem Y_Xstar_mulVec_eqOn (w : Fin 2 → ℂ) :
    Set.EqOn (fun z => ((X p z)ᴴ)⁻¹ *ᵥ ((X p z)ᴴ *ᵥ w)) (fun _ => w) (U p) :=
  fun _ hx => Y_Xstar_mulVec p hx w

/-! ═══ E: Negative control ═══ -/

/-- Wrong operator: Dbad = √Δ·∂r (missing the −I·∂θ term). -/
def Dbad (f : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) : ℂ :=
  ↑(Real.sqrt (Del p (x 0))) * cpd 0 f x

theorem Dbad_eq_Dm_add (f : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) :
    Dbad p f x = Dm p f x + I * cpd 1 f x := by
  unfold Dbad Dm; ring

/-- The wrong operator Dbad does NOT satisfy the integrating-factor equation
    for X when a ≠ 0: entrywise Dbad X ≠ AX. -/
theorem Dbad_X_ne_AX {x : Fin 2 → ℝ} (hx : x ∈ U p) (ha : p.a ≠ 0) :
    (of fun i j => Dbad p (fun z => X p z i j) x) ≠ A p x * X p x := by
  intro heq
  have h01 := congr_fun (congr_fun heq 0) 1
  simp only [of_apply] at h01
  have hDm : Dm p (fun z => X p z 0 1) x = (A p x * X p x) 0 1 := by
    have h := congr_fun (congr_fun (Dminus_X_eq_AX p hx) 0) 1
    simp only [of_apply] at h; exact h
  have hexp : Dbad p (fun z => X p z 0 1) x =
      (A p x * X p x) 0 1 + I * cpd 1 (fun z => X p z 0 1) x := by
    rw [Dbad_eq_Dm_add, hDm]
  have hzero : I * cpd 1 (fun z => X p z 0 1) x = 0 :=
    left_eq_add.mp (h01.symm.trans hexp)
  have hcpd0 : cpd 1 (fun z => X p z 0 1) x = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h I_ne_zero
    · exact h
  rw [cpd_X01_th p hx] at hcpd0
  have hQ2 : (↑(p.Q ^ 2) : ℂ) ≠ 0 := by
    rw [ofReal_pow]; exact pow_ne_zero 2 (by exact_mod_cast p.hQ)
  have hrho2 : (rhoBar p x) ^ 2 ≠ 0 := pow_ne_zero 2 (rhoBar_ne_zero p hx)
  have h_num : (-(⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ)) ≠ 0 := by
    rw [neg_ne_zero]; intro habs
    have him : (⟨0, -(p.a * Real.sin (x 1))⟩ : ℂ).im = (0 : ℂ).im := congr_arg Complex.im habs
    simp at him
    rcases him with h | h
    · exact ha h
    · exact ne_of_gt (sin_pos_of_mem p hx) h
  exact absurd hcpd0 (mul_ne_zero (mul_ne_zero I_ne_zero hQ2) (div_ne_zero h_num hrho2))

/-! ═══ Axiom audit anchors ═══ -/

#print axioms Dm_Xv_sub_AXv
#print axioms Dp_Yv_add_AYv
#print axioms Xinv_X_mulVec
#print axioms Y_Xstar_mulVec
#print axioms Dbad_X_ne_AX

end Hintz2026

end
