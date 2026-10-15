module

public import RequestProject.OddSplitting.DsumCasimir
public import RequestProject.OddSES.All

/-!
# `CSI5_the_splitting.md`: Part T — the three tensor decompositions of the odd dance

Namespace `ColouredSand.OddTwist`. `p` is a prime (`[Fact p.Prime]`), oddness is assumed where it
is needed (as `3 ≤ p`; in (T1) it follows from `2 ≤ r ≤ p − 2`), `N : DPLattice ℤ_[p]`,
`V := V ℤ_[p]` (C18), `tensor = Tensor2.tensor` (C23), `dsum = Lemma35.dsum` (C22),
`≅` is `Doubling.Iso` (C20).

Encoding of the file's `psi p r N` (CSI3): `psi p N r h1 h2` with `h1 : 1 ≤ r`, `h2 : r ≤ p − 1`;
in the statements below these proofs are discharged by `omega` from the hypotheses on `r`
(`psi` does not depend on them, see `psi_congr`). `twist p (tensor V N)` is CSI4's `Psip p N`.

* **(T0)** `tensor_T0`: `tensor V (twist p N) ≅ psi p 1 N` (CSI3 (B4), inverted; every prime `p`).
* **(T1)** `tensor_T1`: for `2 ≤ r ≤ p − 2`, `tensor V (psi p r N) ≅ psi p (r+1) N ⊕ psi p (r−1) N`.
* **(T2)** `tensor_T2`: for `3 ≤ p`, `tensor V (psi p 1 N) ≅ psi p 2 N ⊕ (twist p N ⊕ twist p N)`.
* **(T3)** `tensor_T3`: for `3 ≤ p`,
  `tensor V (psi p (p−1) N) ≅ twist p (tensor V N) ⊕ psi p (p−2) N`.

Each of (T1)–(T3) is (H2) (`splitting_H2`) applied to a short exact sequence of CSI4 (S5): `S5_mid`,
`S5_one`, `S5_last`, with the classes
`a = (r+1)²` (or `a = 0` for `twist p (tensor V N)`) and `b = (r−1)²` (or `b = 0` for
`twist ⊕ twist`). The congruence hypotheses are CSI4 (C2) (`C2`, on `psi`) and (C3) (`C3`, on
`twist`; with `N := tensor V N` for `Psip`), transported to direct sums by `Dcas_sq_dsum`. The
differences `a − b` are `4r` and `−(p−2)²`, units since `p` is odd (`isUnit_natCast_padic`).
The statements are literally those of the file (no adaptation was needed: CSI4's (S5) has
exactly the shapes required).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DPLattice

variable {p : ℕ} [Fact p.Prime] {N : DPLattice ℤ_[p]}

variable (p N) in
/-- Part T (auxiliary): `psi p N r h1 h2` depends only on `r`. -/
lemma psi_congr {r r' : ℕ} (h : r = r') (h1 : 1 ≤ r) (h2 : r ≤ p - 1) (h1' : 1 ≤ r')
    (h2' : r' ≤ p - 1) : psi p N r h1 h2 = psi p N r' h1' h2' := by
  subst h; rfl

/-- Part T (auxiliary): the congruence hypothesis of Part H on `psi p N s` with `a = s²`
(CSI4 (C2)). -/
lemma hyp_psi (s : ℕ) (hs1 : 1 ≤ s) (hsp : s ≤ p - 1) :
    ∃ R, Dcas (psi p N s hs1 hsp) ((s : ℤ_[p]) ^ 2) ∘ₗ Dcas (psi p N s hs1 hsp) ((s : ℤ_[p]) ^ 2) =
      (p : ℤ_[p]) • R :=
  (C2 s hs1 hsp).2.2

/-- Part T (auxiliary): the congruence hypothesis of Part H on `twist p N` with `b = 0`
(CSI4 (C3)). -/
lemma hyp_twist (N : DPLattice ℤ_[p]) :
    ∃ R, Dcas (twist p N) 0 ∘ₗ Dcas (twist p N) 0 = (p : ℤ_[p]) • R :=
  Dcas_sq_zero_of_casimir _ (C3 (N := N))

/-- **(T0)** (Part T of `CSI5_the_splitting.md`): `tensor V (twist p N) ≅ psi p 1 N`, from
CSI3 (B4). -/
theorem tensor_T0 (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) :
    Nonempty (Doubling.Iso (Tensor2.tensor (V ℤ_[p]) (twist p N)) (psi p N 1 h1 h2)) :=
  (B4_iso p N h1 h2).map Doubling.Iso.symm

/-- **(T1)** (Part T of `CSI5_the_splitting.md`): for `2 ≤ r ≤ p − 2`,
`tensor V (psi p r N) ≅ psi p (r+1) N ⊕ psi p (r−1) N`. (H2) applied to CSI4's `S5_mid`, with
`a = (r+1)²`, `b = (r−1)²`, `a − b = 4r`. -/
theorem tensor_T1 (r : ℕ) (h2r : 2 ≤ r) (hr : r ≤ p - 2) :
    Nonempty (Doubling.Iso (Tensor2.tensor (V ℤ_[p]) (psi p N r (by omega) (by omega)))
      (Lemma35.dsum (psi p N (r + 1) (by omega) (by omega))
        (psi p N (r - 1) (by omega) (by omega)))) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [psi_congr p N (show s + 1 - 1 = s by omega) _ _ (by omega) (by omega)]
  have hpp : p.Prime := Fact.out
  have hp : 4 ≤ p := by omega
  refine splitting_H2 (S5_mid (N := N) s (by omega) (by omega))
    (a := ((s + 1 + 1 : ℕ) : ℤ_[p]) ^ 2) (b := ((s : ℕ) : ℤ_[p]) ^ 2) ?_ (hyp_psi _ _ _)
    (hyp_psi _ _ _)
  have hu : IsUnit (((4 * (s + 1) : ℕ)) : ℤ_[p]) := by
    refine isUnit_natCast_padic fun hd => ?_
    rcases (Nat.Prime.dvd_mul hpp).1 hd with h4 | h4
    · have h2' : p ∣ 2 ^ 2 := by norm_num; exact h4
      have := Nat.le_of_dvd (by norm_num) (hpp.dvd_of_dvd_pow h2')
      omega
    · have := Nat.le_of_dvd (by omega) h4
      omega
  convert hu using 1
  push_cast
  ring

/-- **(T2)** (Part T of `CSI5_the_splitting.md`): `r = 1`, for every odd prime `p`:
`tensor V (psi p 1 N) ≅ psi p 2 N ⊕ (twist p N ⊕ twist p N)`. (H2) applied to CSI4's `S5_one`,
with `a = 4 = (1+1)²`, `b = 0`. -/
theorem tensor_T2 (hp3 : 3 ≤ p) (h1 : 1 ≤ 1) (h2 : 1 ≤ p - 1) :
    Nonempty (Doubling.Iso (Tensor2.tensor (V ℤ_[p]) (psi p N 1 h1 h2))
      (Lemma35.dsum (psi p N 2 (by omega) (by omega))
        (Lemma35.dsum (twist p N) (twist p N)))) := by
  have hpp : p.Prime := Fact.out
  refine splitting_H2 (S5_one (N := N) hp3 h1 h2) (a := ((1 + 1 : ℕ) : ℤ_[p]) ^ 2) (b := 0)
    ?_
    (hyp_psi _ _ _) (Dcas_sq_dsum _ _ (hyp_twist N) (hyp_twist N))
  have hu : IsUnit (((4 : ℕ)) : ℤ_[p]) := by
    refine isUnit_natCast_padic fun hd => ?_
    have h2' : p ∣ 2 ^ 2 := by norm_num; exact hd
    have := Nat.le_of_dvd (by norm_num) (hpp.dvd_of_dvd_pow h2')
    omega
  convert hu using 1
  push_cast
  ring

/-- **(T3)** (Part T of `CSI5_the_splitting.md`): `r = p − 1`, for every odd prime `p`:
`tensor V (psi p (p−1) N) ≅ twist p (tensor V N) ⊕ psi p (p−2) N` (for `p = 3`: `r = 2` and the
quotient is `psi 3 1 N`). (H2) applied to CSI4's `S5_last`, with `a = 0`, `b = (p−2)²`,
`a − b = −(p−2)²`. -/
theorem tensor_T3 (hp3 : 3 ≤ p) :
    Nonempty (Doubling.Iso (Tensor2.tensor (V ℤ_[p]) (psi p N (p - 1) (by omega) le_rfl))
      (Lemma35.dsum (twist p (Tensor2.tensor (V ℤ_[p]) N))
        (psi p N (p - 2) (by omega) (by omega)))) := by
  have hpp : p.Prime := Fact.out
  obtain ⟨s, hs⟩ : ∃ s, s + 2 = p := ⟨p - 2, by omega⟩
  rw [psi_congr p N (show p - 1 = s + 1 by omega) _ _ (by omega) (by omega),
    psi_congr p N (show p - 2 = s by omega) _ _ (by omega) (by omega)]
  refine splitting_H2 (S5_last (N := N) s (by omega) hs) (a := 0)
    (b := ((s : ℕ) : ℤ_[p]) ^ 2) ?_
    (hyp_twist _) (hyp_psi _ _ _)
  have hu : IsUnit ((s : ℕ) : ℤ_[p]) := by
    refine isUnit_natCast_padic fun hd => ?_
    have := Nat.le_of_dvd (by omega) hd
    omega
  rw [zero_sub, IsUnit.neg_iff]
  exact hu.pow 2

end ColouredSand.OddTwist
