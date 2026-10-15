module

public import RequestProject.Splitting.Blocks

/-!
# (A2) The splitting of the Laplacian of the Hamming graph (Theorem A)

This file corresponds to **(A2) The splitting** of `CS2_theorem_A_splitting.md`.

## Encoding

* The Hamming graph `H(d,q)` and its Laplacian `L` are `hammingGraph d q` and `laplacian d q`
  (`RequestProject/Splitting/Basic.lean`): `L` acts on `(Fin d → Fin q) → ℤ` by the Laplacian
  matrix `degMatrix − adjMatrix` of `H(d,q)`.
* `coker L` is `((Fin d → Fin q) → ℤ) ⧸ LinearMap.range L`, and `X_q(m,c)` is
  `Xq q m c = B_m ⧸ range (q (c + H) + U)` with `B_m`, `H`, `U` from
  `RequestProject/Strings/Basic.lean`.
* The direct sum `⨁_{j=0}^{d} X_q(d−j, j)^{⊕ C(d,j)(q−2)^j}` is the (finite) product over the
  index type `Σ j : Fin (d+1), Fin (C(d,j) · (q−2)^j)` of `X_q(d − j, j)`.
  (For `q = 2` only `j = 0` occurs, since `Fin (C(d,j) · 0^j)` is empty for `j ≥ 1`.)
* "`≅` as `ℤ`-modules" is the existence of a `ℤ`-linear equivalence.

## Proof

`laplacian_conj` (change to the tensor basis built from `e_0, −σ, f_1, …, f_{q−2}`),
`cokerEquivPi` with `Nop_block` (block decomposition indexed by the types `k`), and the count
`card_blockJ` of the types with `|T| = j`.
-/

@[expose] public section

open Finset

namespace ColouredSand.Splitting

open ColouredSand.Strings

/-- `X_q(m,c) ≅ X_q(m',c')` when `m = m'` and `c = c'`. -/
noncomputable def xqCongr {q m m' c c' : ℕ} (hm : m = m') (hc : c = c') :
    Xq q m c ≃ₗ[ℤ] Xq q m' c' := by
  subst hm; subst hc; exact LinearEquiv.refl ℤ _

/-- The value `j = |T|` of a type `k`, in `Fin (d+1)`. -/
def blockJFin {n d : ℕ} (k : Fin d → Option (Fin n)) : Fin (d + 1) :=
  ⟨blockJ k, Nat.lt_succ_of_le (blockJ_le k)⟩

/-- The types `k` with `|T| = j` are enumerated by `Fin (C(d,j) (q−2)^j)`. -/
noncomputable def typeEquiv (n d : ℕ) :
    (Fin d → Option (Fin n)) ≃ Σ j : Fin (d + 1), Fin (d.choose j * n ^ (j : ℕ)) :=
  (Equiv.sigmaFiberEquiv (blockJFin (n := n) (d := d))).symm.trans
    (Equiv.sigmaCongrRight fun j => Fintype.equivFinOfCardEq (by
      rw [← card_blockJ (n := n) (d := d) j]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun k => Fin.ext_iff)))

lemma typeEquiv_fst {n d : ℕ} (k : Fin d → Option (Fin n)) :
    ((typeEquiv n d k).1 : ℕ) = blockJ k := rfl

/-- **(A2)** with `q = n + 2`. -/
theorem theorem_A_aux (n d : ℕ) :
    Nonempty ((((Fin d → Fin (n + 2)) → ℤ) ⧸ LinearMap.range (laplacian d (n + 2))) ≃ₗ[ℤ]
      ∀ σ : (Σ j : Fin (d + 1), Fin (d.choose j * n ^ (j : ℕ))), Xq (n + 2) (d - σ.1) σ.1) := by
  let Ψ := tensorEquiv d (hamBasis n)
  have hconj : ∀ x, Nop n d (Ψ.symm x) = Ψ.symm (laplacian d (n + 2) x) := by
    intro x
    have h := laplacian_conj (n := n) (d := d) (Ψ.symm x)
    change laplacian d (n + 2) (Ψ (Ψ.symm x)) = Ψ (Nop n d (Ψ.symm x)) at h
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, LinearEquiv.symm_apply_apply]
  let e1 := cokerEquivOfConj (laplacian d (n + 2)) (Nop n d) Ψ.symm Ψ.symm hconj
  let e2 := cokerEquivPi (blockEquiv n d) (Nop n d)
    (fun k => Mq (n + 2) (blockM k) (blockJ k)) (fun f k S => Nop_block f k S)
  let e3 : (∀ k : Fin d → Option (Fin n), Xq (n + 2) (blockM k) (blockJ k)) ≃ₗ[ℤ]
      ∀ k : Fin d → Option (Fin n), Xq (n + 2) (d - (typeEquiv n d k).1) (typeEquiv n d k).1 :=
    LinearEquiv.piCongrRight fun k =>
      xqCongr (by rw [blockM_eq, typeEquiv_fst]) (typeEquiv_fst k).symm
  let e4 := LinearEquiv.piCongrLeft ℤ
    (fun σ : (Σ j : Fin (d + 1), Fin (d.choose j * n ^ (j : ℕ))) => Xq (n + 2) (d - σ.1) σ.1)
    (typeEquiv n d)
  exact ⟨((e1.trans e2).trans e3).trans e4⟩

/-- **(A2) The splitting (Theorem A).**  For `q ≥ 2` and every `d`, as `ℤ`-modules,
`coker L ≅ ⨁_{j=0}^{d} X_q(d−j, j)^{⊕ C(d,j)(q−2)^j}`,
where `L` is the Laplacian of the Hamming graph `H(d,q)` and `X_q(m,c) = coker (q (c + H) + U)`
on `B_m`.  The direct sum is the product over `Σ j : Fin (d+1), Fin (C(d,j) (q−2)^j)`.
(The file assumes `d ≥ 1`; the statement also holds for `d = 0`.) -/
theorem theorem_A (d q : ℕ) (hq : 2 ≤ q) :
    Nonempty ((((Fin d → Fin q) → ℤ) ⧸ LinearMap.range (laplacian d q)) ≃ₗ[ℤ]
      ∀ σ : (Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))), Xq q (d - σ.1) σ.1) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 2 := ⟨q - 2, by omega⟩
  rw [Nat.add_sub_cancel]
  exact theorem_A_aux n d

end ColouredSand.Splitting
