module

public import RequestProject.Strings.All
public import RequestProject.Filt.PartT

/-!
# `CSH1_theorem_H_the_prime_two.md`, Part D — the dictionary `B_m(A) = V^{⊗m}`

Namespace `ColouredSand.ThmH`.  Here `A` is an arbitrary commutative ring.

Encodings:

* `B m A = Finset (Fin m) → A` is the Coloured Sand module `ColouredSand.Strings.B`, with basis
  `e_S = Pi.single S 1`; `V^{⊗m}` is this project's `Filt.tpow A m`, whose basis is
  `(Filt.tpow A m).ι` (`Unit` for `m = 0`, `Fin 2 × (Filt.tpow A n).ι` for `m = n + 1`, the
  first coordinate being the **first** tensor factor, `0 ↦ b_0` of weight `+1`,
  `1 ↦ b_1` of weight `−1`).
* `splitFirst n : Finset (Fin (n+1)) ≃ Fin 2 × Finset (Fin n)` splits a set `S` according to
  whether the first element `0` belongs to it: `S ↦ ([0 ∈ S], {x | x.succ ∈ S})`; its inverse is
  `joinFirst`.
* (D1) `beta A m : Finset (Fin m) ≃ (Filt.tpow A m).ι` is defined by recursion on `m` through
  `splitFirst`: it sends `S` to the pure tensor with `b_1` exactly at the positions of `S` and
  `b_0` elsewhere.
* (D2) `Psi A m : B m A ≃ₗ[A] ((Filt.tpow A m).ι → A)` is `f ↦ f ∘ (beta A m).symm`, so that
  `Psi e_S = δ_{beta S}` (the basis vector of the pure tensor attached to `S`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.ThmH

open Finset

/-! ### Splitting a subset of `Fin (n+1)` at its first element -/

/-- The set `T.map succ ⊆ Fin (n+1)` with `0` added when `e = 1` (auxiliary for (D1) of
`CSH1_theorem_H_the_prime_two.md`). -/
def joinFirst {n : ℕ} (e : Fin 2) (T : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  if e = 1 then insert 0 (T.map (Fin.succEmb n)) else T.map (Fin.succEmb n)

lemma zero_not_mem_map_succ {n : ℕ} (T : Finset (Fin n)) :
    (0 : Fin (n + 1)) ∉ T.map (Fin.succEmb n) := by
  simp [Fin.succ_ne_zero]

lemma succ_mem_joinFirst {n : ℕ} (e : Fin 2) (T : Finset (Fin n)) (x : Fin n) :
    x.succ ∈ joinFirst e T ↔ x ∈ T := by
  unfold joinFirst; split_ifs <;> simp [Fin.succ_ne_zero]

lemma zero_mem_joinFirst {n : ℕ} (e : Fin 2) (T : Finset (Fin n)) :
    (0 : Fin (n + 1)) ∈ joinFirst e T ↔ e = 1 := by
  unfold joinFirst; split_ifs with h <;> simp [h, Fin.succ_ne_zero]

/-- `splitFirst n : Finset (Fin (n+1)) ≃ Fin 2 × Finset (Fin n)`, `S ↦ ([0 ∈ S], S.preimage succ)`
(auxiliary for (D1) of `CSH1_theorem_H_the_prime_two.md`). -/
def splitFirst (n : ℕ) : Finset (Fin (n + 1)) ≃ Fin 2 × Finset (Fin n) where
  toFun S := (if (0 : Fin (n + 1)) ∈ S then 1 else 0,
    S.preimage Fin.succ (Fin.succ_injective _).injOn)
  invFun p := joinFirst p.1 p.2
  left_inv S := by
    ext x
    refine Fin.cases ?_ (fun y => ?_) x
    · rw [zero_mem_joinFirst]; dsimp only; split_ifs with h <;> simp [h]
    · rw [succ_mem_joinFirst]; simp
  right_inv p := by
    obtain ⟨e, T⟩ := p
    refine Prod.ext ?_ ?_
    · simp only [zero_mem_joinFirst]
      split_ifs with h
      · exact h.symm
      · fin_cases e
        · rfl
        · exact absurd rfl h
    · ext x; simp [succ_mem_joinFirst]

lemma splitFirst_symm_apply {n : ℕ} (e : Fin 2) (T : Finset (Fin n)) :
    (splitFirst n).symm (e, T) = joinFirst e T := rfl

lemma card_joinFirst {n : ℕ} (e : Fin 2) (T : Finset (Fin n)) :
    (joinFirst e T).card = (if e = 1 then 1 else 0) + T.card := by
  unfold joinFirst
  split_ifs
  · rw [card_insert_of_notMem (zero_not_mem_map_succ T), card_map]; ring
  · simp

/-! ### (D1) -/

variable (A : Type*) [CommRing A]

/-- **(D1)** of `CSH1_theorem_H_the_prime_two.md`: the bijection
`beta A m : Finset (Fin m) ≃ (Filt.tpow A m).ι`, sending `S` to the pure tensor with `b_1` exactly
at the positions of `S` (recursion on `m`, splitting off the first element with `splitFirst`). -/
def beta : (m : ℕ) → Finset (Fin m) ≃ (Filt.tpow A m).ι
  | 0 => { toFun := fun _ => (), invFun := fun _ => ∅,
           left_inv := fun S => by ext x; exact x.elim0,
           right_inv := fun _ => rfl }
  | n + 1 => (splitFirst n).trans (Equiv.prodCongr (Equiv.refl (Fin 2)) (beta n))

lemma beta_symm_succ (n : ℕ) (e : Fin 2) (i : (Filt.tpow A n).ι) :
    (beta A (n + 1)).symm ((e, i) : Fin 2 × (Filt.tpow A n).ι) =
      joinFirst e ((beta A n).symm i) := rfl

/-- **(D1)** of `CSH1_theorem_H_the_prime_two.md`: `beta A m` is a bijection
`Finset (Fin m) ≃ (Filt.tpow A m).ι` with `wt (beta A m S) = m − 2 |S|`. -/
theorem D1 (m : ℕ) (S : Finset (Fin m)) :
    (Filt.tpow A m).wt (beta A m S) = (m : ℤ) - 2 * S.card := by
  induction m with
  | zero => simp [Subsingleton.elim S ∅]; rfl
  | succ n ih =>
    obtain ⟨⟨e, T⟩, rfl⟩ := (splitFirst n).symm.surjective S
    have hb : beta A (n + 1) ((splitFirst n).symm (e, T)) = (e, beta A n T) := by
      simp [beta]; rfl
    rw [hb, splitFirst_symm_apply, card_joinFirst]
    change DPLattice.wtV e + (Filt.tpow A n).wt (beta A n T) = _
    rw [ih]
    fin_cases e <;> simp [DPLattice.wtV] <;> ring

/-- (D1) in terms of the inverse bijection: `wt i = m − 2 |beta⁻¹ i|`. -/
lemma D1_symm (m : ℕ) (i : (Filt.tpow A m).ι) :
    (Filt.tpow A m).wt i = (m : ℤ) - 2 * ((beta A m).symm i).card := by
  rw [← D1 A m, Equiv.apply_symm_apply]

/-! ### (D2) -/

/-- **(D2)** of `CSH1_theorem_H_the_prime_two.md`: the induced `A`-linear equivalence
`Psi A m : B m A ≃ₗ[A] ((Filt.tpow A m).ι → A)`, `f ↦ f ∘ (beta A m).symm`. -/
def Psi (m : ℕ) : ColouredSand.Strings.B m A ≃ₗ[A] ((Filt.tpow A m).ι → A) :=
  LinearEquiv.funCongrLeft A A (beta A m).symm

@[simp] lemma Psi_apply (m : ℕ) (f : ColouredSand.Strings.B m A) (i : (Filt.tpow A m).ι) :
    Psi A m f i = f ((beta A m).symm i) := rfl

/-- `F^{(1)}` on `V ⊗ M`, coordinatewise: `(F g)(b_0, i) = (F (g(b_0,·))) i` and
`(F g)(b_1, i) = g(b_0, i) + (F (g(b_1,·))) i` (auxiliary for (D2)). -/
lemma tensorV_Fd1_apply (M : DPLattice A) (g : Fin 2 × M.ι → A) (i : M.ι) :
    (DPLattice.tensorV M).Fd 1 g (0, i) = M.Fd 1 (DPLattice.slice 0 g) i ∧
    (DPLattice.tensorV M).Fd 1 g (1, i) = g (0, i) + M.Fd 1 (DPLattice.slice 1 g) i := by
  have hg := DPLattice.eq_bvec_slice g
  have hF : (DPLattice.tensorV M).Fd 1 g =
      DPLattice.bvec 0 (M.Fd 1 (DPLattice.slice 0 g)) +
        DPLattice.bvec 1 (DPLattice.slice 0 g) +
        DPLattice.bvec 1 (M.Fd 1 (DPLattice.slice 1 g)) := by
    conv_lhs => rw [hg]
    rw [map_add, DPLattice.tensorV_Fd_b0 M 1 le_rfl, DPLattice.tensorV_Fd_b1, Nat.sub_self,
      M.isDP.P0_F]
    rfl
  rw [hF]
  constructor
  · simp
  · simp

/-- `U` on `B (n+1)`, at the set `joinFirst 0 T` (auxiliary for (D2)). -/
lemma U_joinFirst0 {n : ℕ} (f : ColouredSand.Strings.B (n + 1) A) (T : Finset (Fin n)) :
    ColouredSand.Strings.U (n + 1) A f (joinFirst 0 T) =
      ColouredSand.Strings.U n A (fun T' => f (joinFirst 0 T')) T := by
  simp only [ColouredSand.Strings.U, LinearMap.coe_mk, AddHom.coe_mk, joinFirst,
    show (0 : Fin 2) ≠ 1 from by decide, if_false]
  rw [sum_map]
  refine sum_congr rfl fun y _ => ?_
  rw [Finset.map_erase]

/-- `U` on `B (n+1)`, at the set `joinFirst 1 T` (auxiliary for (D2)). -/
lemma U_joinFirst1 {n : ℕ} (f : ColouredSand.Strings.B (n + 1) A) (T : Finset (Fin n)) :
    ColouredSand.Strings.U (n + 1) A f (joinFirst 1 T) =
      f (joinFirst 0 T) + ColouredSand.Strings.U n A (fun T' => f (joinFirst 1 T')) T := by
  simp only [ColouredSand.Strings.U, LinearMap.coe_mk, AddHom.coe_mk, joinFirst,
    show (0 : Fin 2) ≠ 1 from by decide, if_false, if_true]
  rw [sum_insert (zero_not_mem_map_succ T), erase_insert (zero_not_mem_map_succ T), sum_map]
  congr 1
  refine sum_congr rfl fun y _ => ?_
  rw [erase_insert_of_ne (show (0 : Fin (n + 1)) ≠ Fin.succEmb n y from
    (Fin.succ_ne_zero y).symm), Finset.map_erase]

/-- (D2)(a), pointwise: `Psi (U f) = F^{(1)} (Psi f)`. -/
lemma Psi_U (m : ℕ) (f : ColouredSand.Strings.B m A) :
    Psi A m (ColouredSand.Strings.U m A f) = (Filt.tpow A m).Fd 1 (Psi A m f) := by
  induction m with
  | zero =>
    funext i
    have h1 : (Filt.tpow A 0).Fd 1 = 0 := rfl
    rw [h1]
    simp [ColouredSand.Strings.U, beta]
  | succ n ih =>
    funext ⟨e, i⟩
    have hs : ∀ e' : Fin 2, DPLattice.slice e' (Psi A (n + 1) f) =
        Psi A n (fun T => f (joinFirst e' T)) := fun e' => by
      funext j; rfl
    obtain ⟨h0, h1⟩ := tensorV_Fd1_apply A (Filt.tpow A n) (Psi A (n + 1) f) i
    fin_cases e
    · change _ = (DPLattice.tensorV (Filt.tpow A n)).Fd 1 (Psi A (n + 1) f) (0, i)
      rw [h0, hs, ← ih]
      change ColouredSand.Strings.U (n + 1) A f (joinFirst 0 ((beta A n).symm i)) = _
      rw [U_joinFirst0]; rfl
    · change _ = (DPLattice.tensorV (Filt.tpow A n)).Fd 1 (Psi A (n + 1) f) (1, i)
      rw [h1, hs, ← ih]
      change ColouredSand.Strings.U (n + 1) A f (joinFirst 1 ((beta A n).symm i)) = _
      rw [U_joinFirst1]; rfl

/-- **(D2)** of `CSH1_theorem_H_the_prime_two.md`: with `Psi A m f = f ∘ (beta A m).symm`,
(a) `Psi ∘ U = F^{(1)} ∘ Psi` and (b) `Psi ∘ (2 • H) = (m − H) ∘ Psi`
(`U`, `H` the Coloured Sand operators, `F^{(1)} = (Filt.tpow A m).Fd 1`, `H` on the right the
weight operator `DPLattice.H`). -/
theorem D2 (m : ℕ) :
    (Psi A m).toLinearMap ∘ₗ ColouredSand.Strings.U m A =
        (Filt.tpow A m).Fd 1 ∘ₗ (Psi A m).toLinearMap ∧
      (Psi A m).toLinearMap ∘ₗ ((2 : A) • ColouredSand.Strings.H m A) =
        ((m : A) • LinearMap.id - DPLattice.H (Filt.tpow A m)) ∘ₗ (Psi A m).toLinearMap := by
  refine ⟨LinearMap.ext fun f => Psi_U A m f, LinearMap.ext fun f => funext fun i => ?_⟩
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Psi_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.id_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    DPLattice.Hop_apply, D1_symm]
  simp only [ColouredSand.Strings.H, LinearMap.coe_mk, AddHom.coe_mk]
  push_cast
  ring

/-! ### (D3) -/

/-- **(D3)** of `CSH1_theorem_H_the_prime_two.md`: for `e ≥ 1` and `c : ℕ`,
`Psi ∘ opM m A (2^e) c = (F^{(1)} + 2^{e−1} ((m + 2c) − H)) ∘ Psi`. -/
theorem D3 (m e c : ℕ) (he : 1 ≤ e) :
    (Psi A m).toLinearMap ∘ₗ ColouredSand.Strings.opM m A ((2 : A) ^ e) (c : A) =
      ((Filt.tpow A m).Fd 1 + ((2 : A) ^ (e - 1)) •
        (((m : A) + 2 * c) • LinearMap.id - DPLattice.H (Filt.tpow A m))) ∘ₗ
        (Psi A m).toLinearMap := by
  refine LinearMap.ext fun f => funext fun i => ?_
  have hU := congrFun (Psi_U A m f) i
  have he' : (2 : A) ^ e = 2 ^ (e - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel he]
  simp only [Psi_apply] at hU
  simp only [ColouredSand.Strings.opM, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.add_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, Psi_apply,
    LinearMap.sub_apply, LinearMap.id_apply, Pi.sub_apply, smul_eq_mul, DPLattice.Hop_apply,
    D1_symm, ← hU]
  simp only [ColouredSand.Strings.H, LinearMap.coe_mk, AddHom.coe_mk]
  rw [he']
  push_cast
  ring

end ColouredSand.ThmH
