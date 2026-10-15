module

public import RequestProject.WeylFilt.Basic

/-!
# `C19_weyl_filtrations_of_V_tensor.md`: the four maps (Setting, "The four maps")

The four `A`-linear maps are defined on basis vectors exactly as in the file and extended
`A`-linearly (`Basis.constr` on the standard basis `Pi.basisFun`), for a parameter `m : ℕ`:

* `fDeltaLin m : Δ_A(m+1) → V ⊗ Δ_A(m)`, `e'_R ↦ b_0 e_R + b_1 e_{R−1}`;
* `gDeltaLin m : V ⊗ Δ_A(m) → Δ_A(m−1)`, `b_1 e_s ↦ e''_s`, `b_0 e_R ↦ −e''_{R−1}`
  (with `e''_k = 0` outside `[0, m−1]`, so `b_1 e_m ↦ 0` and `b_0 e_0 ↦ 0`);
* `fNablaLin m : ∇_A(m−1) → V ⊗ ∇_A(m)`, `w''_r ↦ b_0 w_{r+1} − b_1 w_r`;
* `gNablaLin m : V ⊗ ∇_A(m) → ∇_A(m+1)`, `b_0 w_r ↦ w'_r`, `b_1 w_r ↦ w'_{r+1}`.

Here `m − 1` is the truncated subtraction of `ℕ`; all statements about these maps assume `m ≥ 1`
as in the file. The basis-vector formulas are restated as theorems (`fDeltaLin_single`, …).
For the proofs, each map is identified with an explicit coordinate formula (`…Coord`).
-/

@[expose] public section

noncomputable section

namespace WeylFilt

open DPLattice Finset

variable {A : Type*} [CommRing A]

/-! ### Definitions on basis vectors -/

/-- "The four maps": `fΔ : Δ_A(m+1) → V ⊗ Δ_A(m)`, `e'_R ↦ b_0 e_R + b_1 e_{R−1}`. -/
def fDeltaLin (m : ℕ) : (Fin (m + 1 + 1) → A) →ₗ[A] (Fin 2 × Fin (m + 1) → A) :=
  (Pi.basisFun A (Fin (m + 1 + 1))).constr A fun R =>
    bvec 0 (ev m ((R : ℕ) : ℤ)) + bvec 1 (ev m ((R : ℕ) - 1 : ℤ))

/-- "The four maps": `gΔ : V ⊗ Δ_A(m) → Δ_A(m−1)`, `b_1 e_s ↦ e''_s`, `b_0 e_R ↦ −e''_{R−1}`
(so `b_1 e_m ↦ 0`, `b_0 e_0 ↦ 0`). -/
def gDeltaLin (m : ℕ) : (Fin 2 × Fin (m + 1) → A) →ₗ[A] (Fin (m - 1 + 1) → A) :=
  (Pi.basisFun A (Fin 2 × Fin (m + 1))).constr A fun p =>
    if p.1 = 0 then -ev (m - 1) ((p.2 : ℕ) - 1 : ℤ) else ev (m - 1) ((p.2 : ℕ) : ℤ)

/-- "The four maps": `f∇ : ∇_A(m−1) → V ⊗ ∇_A(m)`, `w''_r ↦ b_0 w_{r+1} − b_1 w_r`. -/
def fNablaLin (m : ℕ) : (Fin (m - 1 + 1) → A) →ₗ[A] (Fin 2 × Fin (m + 1) → A) :=
  (Pi.basisFun A (Fin (m - 1 + 1))).constr A fun r =>
    bvec 0 (ev m ((r : ℕ) + 1 : ℤ)) - bvec 1 (ev m ((r : ℕ) : ℤ))

/-- "The four maps": `g∇ : V ⊗ ∇_A(m) → ∇_A(m+1)`, `b_0 w_r ↦ w'_r`, `b_1 w_r ↦ w'_{r+1}`. -/
def gNablaLin (m : ℕ) : (Fin 2 × Fin (m + 1) → A) →ₗ[A] (Fin (m + 1 + 1) → A) :=
  (Pi.basisFun A (Fin 2 × Fin (m + 1))).constr A fun p =>
    if p.1 = 0 then ev (m + 1) ((p.2 : ℕ) : ℤ) else ev (m + 1) ((p.2 : ℕ) + 1 : ℤ)

/-! ### The basis-vector formulas -/

/-- "The four maps": `fΔ e'_R = b_0 e_R + b_1 e_{R−1}`. -/
theorem fDeltaLin_single (m : ℕ) (R : Fin (m + 1 + 1)) :
    fDeltaLin (A := A) m (Pi.single R 1) =
      bvec 0 (ev m ((R : ℕ) : ℤ)) + bvec 1 (ev m ((R : ℕ) - 1 : ℤ)) := by
  rw [fDeltaLin, ← Pi.basisFun_apply, Module.Basis.constr_basis]

/-- "The four maps": `gΔ (b_0 e_R) = −e''_{R−1}` and `gΔ (b_1 e_R) = e''_R`. -/
theorem gDeltaLin_single (m : ℕ) (R : Fin (m + 1)) :
    gDeltaLin (A := A) m (bvec 0 (Pi.single R 1)) = -ev (m - 1) ((R : ℕ) - 1 : ℤ) ∧
    gDeltaLin (A := A) m (bvec 1 (Pi.single R 1)) = ev (m - 1) ((R : ℕ) : ℤ) := by
  rw [← single_eq_bvec, ← single_eq_bvec, gDeltaLin, ← Pi.basisFun_apply, ← Pi.basisFun_apply,
    Module.Basis.constr_basis, Module.Basis.constr_basis]
  simp

/-- "The four maps": `f∇ w''_r = b_0 w_{r+1} − b_1 w_r`. -/
theorem fNablaLin_single (m : ℕ) (r : Fin (m - 1 + 1)) :
    fNablaLin (A := A) m (Pi.single r 1) =
      bvec 0 (ev m ((r : ℕ) + 1 : ℤ)) - bvec 1 (ev m ((r : ℕ) : ℤ)) := by
  rw [fNablaLin, ← Pi.basisFun_apply, Module.Basis.constr_basis]

/-- "The four maps": `g∇ (b_0 w_r) = w'_r` and `g∇ (b_1 w_r) = w'_{r+1}`. -/
theorem gNablaLin_single (m : ℕ) (r : Fin (m + 1)) :
    gNablaLin (A := A) m (bvec 0 (Pi.single r 1)) = ev (m + 1) ((r : ℕ) : ℤ) ∧
    gNablaLin (A := A) m (bvec 1 (Pi.single r 1)) = ev (m + 1) ((r : ℕ) + 1 : ℤ) := by
  rw [← single_eq_bvec, ← single_eq_bvec, gNablaLin, ← Pi.basisFun_apply, ← Pi.basisFun_apply,
    Module.Basis.constr_basis, Module.Basis.constr_basis]
  simp

/-- "The four maps": the case list of the file for `gΔ` (`m ≥ 1`): `b_1 e_s ↦ e''_s`
(`0 ≤ s ≤ m−1`), `b_1 e_m ↦ 0`, `b_0 e_0 ↦ 0`, `b_0 e_R ↦ −e''_{R−1}` (`1 ≤ R ≤ m`). -/
theorem gDeltaLin_cases (m : ℕ) (hm : 1 ≤ m) :
    (∀ (s : ℕ) (hs : s ≤ m - 1), gDeltaLin (A := A) m (bvec 1 (Pi.single ⟨s, by omega⟩ 1)) =
      Pi.single ⟨s, by omega⟩ 1) ∧
    gDeltaLin (A := A) m (bvec 1 (Pi.single (Fin.last m) 1)) = 0 ∧
    gDeltaLin (A := A) m (bvec 0 (Pi.single 0 1)) = 0 ∧
    (∀ (R : ℕ) (h1 : 1 ≤ R) (h2 : R ≤ m), gDeltaLin (A := A) m (bvec 0 (Pi.single ⟨R, by omega⟩ 1)) =
      -Pi.single ⟨R - 1, by omega⟩ 1) := by
  refine ⟨fun s hs => ?_, ?_, ?_, fun R h1 h2 => ?_⟩
  · rw [(gDeltaLin_single m _).2]
    funext j; simp [ev, Pi.single_apply, Fin.ext_iff]
  · rw [(gDeltaLin_single m _).2]
    funext j; simp only [ev, Fin.val_last, Pi.zero_apply]; rw [if_neg]; have := j.isLt; omega
  · rw [(gDeltaLin_single m _).1]
    funext j; simp only [ev, Fin.val_zero, Pi.neg_apply, Pi.zero_apply]; rw [if_neg (by omega)]
    simp
  · rw [(gDeltaLin_single m _).1]
    funext j; simp only [ev, Pi.neg_apply, Pi.single_apply, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)

/-! ### Coordinate formulas (auxiliary) -/

/-- (auxiliary) coordinates of `fΔ`. -/
def fDeltaCoord (m : ℕ) : (Fin (m + 1 + 1) → A) →ₗ[A] (Fin 2 × Fin (m + 1) → A) where
  toFun x p := if p.1 = 0 then ext0 x p.2 else ext0 x (p.2 + 1)
  map_add' x y := by funext p; simp only [ext0_add, Pi.add_apply]; split_ifs <;> rfl
  map_smul' c x := by funext p; simp only [ext0_smul, Pi.smul_apply, smul_eq_mul,
    RingHom.id_apply]; split_ifs <;> rfl

/-- (auxiliary) coordinates of `gΔ`. -/
def gDeltaCoord (m : ℕ) : (Fin 2 × Fin (m + 1) → A) →ₗ[A] (Fin (m - 1 + 1) → A) where
  toFun y s := ext0 (slice 1 y) s - ext0 (slice 0 y) (s + 1)
  map_add' x y := by funext p; simp only [map_add, ext0_add, Pi.add_apply]; ring
  map_smul' c x := by funext p; simp only [map_smul, ext0_smul, Pi.smul_apply, smul_eq_mul,
    RingHom.id_apply]; ring

/-- (auxiliary) coordinates of `f∇`. -/
def fNablaCoord (m : ℕ) : (Fin (m - 1 + 1) → A) →ₗ[A] (Fin 2 × Fin (m + 1) → A) where
  toFun x p := if p.1 = 0 then (if 1 ≤ (p.2 : ℕ) then ext0 x (p.2 - 1) else 0) else -ext0 x p.2
  map_add' x y := by funext p; simp only [ext0_add, Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by funext p; simp only [ext0_smul, Pi.smul_apply, smul_eq_mul,
    RingHom.id_apply]; split_ifs <;> ring

/-- (auxiliary) coordinates of `g∇`. -/
def gNablaCoord (m : ℕ) : (Fin 2 × Fin (m + 1) → A) →ₗ[A] (Fin (m + 1 + 1) → A) where
  toFun y n := ext0 (slice 0 y) n + (if 1 ≤ (n : ℕ) then ext0 (slice 1 y) (n - 1) else 0)
  map_add' x y := by funext p; simp only [map_add, ext0_add, Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by funext p; simp only [map_smul, ext0_smul, Pi.smul_apply, smul_eq_mul,
    RingHom.id_apply]; split_ifs <;> ring

lemma ext0_single {n : ℕ} (i : Fin n) (k : ℕ) :
    ext0 (Pi.single i (1 : A)) k = if k = (i : ℕ) then 1 else 0 := by
  unfold ext0; split_ifs <;> simp_all [Pi.single_apply, Fin.ext_iff]

lemma fDeltaLin_eq (m : ℕ) : fDeltaLin (A := A) m = fDeltaCoord m := by
  refine (Pi.basisFun A _).ext fun R => ?_
  rw [fDeltaLin, Module.Basis.constr_basis, Pi.basisFun_apply]
  funext ⟨e, k⟩
  fin_cases e
  all_goals simp [fDeltaCoord, ev, ext0_single]
  all_goals split_ifs
  all_goals first | rfl | (exfalso; omega)

lemma gDeltaLin_eq (m : ℕ) : gDeltaLin (A := A) m = gDeltaCoord m := by
  refine (Pi.basisFun A _).ext fun p => ?_
  rw [gDeltaLin, Module.Basis.constr_basis, Pi.basisFun_apply]
  obtain ⟨e, R⟩ := p
  rw [single_eq_bvec]
  funext k
  fin_cases e
  all_goals simp [gDeltaCoord, ev, ext0_single]
  all_goals split_ifs
  all_goals first | rfl | (exfalso; omega)

lemma fNablaLin_eq (m : ℕ) : fNablaLin (A := A) m = fNablaCoord m := by
  refine (Pi.basisFun A _).ext fun r => ?_
  rw [fNablaLin, Module.Basis.constr_basis, Pi.basisFun_apply]
  funext ⟨e, k⟩
  fin_cases e
  all_goals simp [fNablaCoord, ev, ext0_single]
  all_goals split_ifs
  all_goals first | rfl | (exfalso; omega)

lemma gNablaLin_eq (m : ℕ) : gNablaLin (A := A) m = gNablaCoord m := by
  refine (Pi.basisFun A _).ext fun p => ?_
  rw [gNablaLin, Module.Basis.constr_basis, Pi.basisFun_apply]
  obtain ⟨e, R⟩ := p
  rw [single_eq_bvec]
  funext k
  fin_cases e
  all_goals simp [gNablaCoord, ev, ext0_single]
  all_goals split_ifs
  all_goals first | rfl | (exfalso; omega)

end WeylFilt
