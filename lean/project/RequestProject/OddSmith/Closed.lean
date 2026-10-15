module

public import RequestProject.OddSmith.Zero
public import RequestProject.OddSmith.Coker
public import RequestProject.OddTheoremI.All

/-!
# Part Y of `CSI18_theorem_4_4_smith_form_of_Mp.md`: the closed form of `Y_p(λ, i, e)`

## Encoding

* CSI10's `Cmod p l i e = (slots → ℤ_[p]) ⧸ range (p^k • Mp p l i e)` (matrices acting on column
  vectors) and `Zq p a = ℤ_[p] ⧸ (p^a)`; `Yp p l i e` is `Y_p(λ, i, e)` and `Sp p l` is `S_p(λ)`.
* `Π_{j<N} ℤ_[p] ⧸ p^{k + C + ŷ(N−1−j)}` is `(j : Fin N) → Zq p (kTop p l + E j)` for a function
  `E : ℕ → ℕ` with `(E j : ℤ) = C + ŷ(N − 1 − j)` for `j < N` (the exponents are natural numbers);
  likewise for `i = 0` with `Fin (N − 1)` and `E j = eK + ŷ^♯(N − 2 − j)`.
* Over `ℤ_[p]` the matrices `P, Q` of (S3)/(Z3) are invertible (an integer prime to `p` is a unit
  of `ℤ_[p]`, `oddSmith_isUnit_int`), so the cokernel of `p^k • Mp` is that of the diagonal matrix
  `p^k • diag(u_j p^{E_j})` (`oddSmith_coker_of_smith`).
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open Finset Matrix TheoremF

variable (p : ℕ) [hp : Fact p.Prime]

/-- An integer prime to `p` is a unit of `ℤ_[p]` (Part Y of `CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
lemma oddSmith_isUnit_int {z : ℤ} (hz : ¬ (p : ℤ) ∣ z) : IsUnit (z : ℤ_[p]) :=
  PadicInt.isUnit_iff.2 (le_antisymm (PadicInt.norm_le_one _)
    (not_lt.1 fun h => hz ((PadicInt.norm_int_lt_one_iff_dvd z).1 h)))

lemma oddSmith_isUnit_det_map {ι : Type*} [Fintype ι] [DecidableEq ι] {P : Matrix ι ι ℤ}
    (hP : ¬ (p : ℤ) ∣ P.det) : IsUnit (P.map (Int.cast : ℤ → ℤ_[p])).det := by
  have h := RingHom.map_det (Int.castRingHom ℤ_[p]) P
  rw [RingHom.mapMatrix_apply] at h
  have h' : (P.map (Int.castRingHom ℤ_[p])) = P.map (Int.cast : ℤ → ℤ_[p]) := rfl
  rw [← h', ← h]
  exact oddSmith_isUnit_int p hP

/-- **Cokernel from a Smith form** (Part Y of `CSI18_theorem_4_4_smith_form_of_Mp.md`, general form):
if `M` read along `σ : Fin n ≃ S` is the image of an integer matrix `MZ` and `P·MZ·Q = diagonal d`
with `p ∤ det P, det Q`, then for every `c`,
`(S → ℤ_[p]) ⧸ range (c • M) ≃ Π_j ℤ_[p] ⧸ (c · d j)`. -/
theorem oddSmith_coker_of_smith {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ} (σ : Fin n ≃ S)
    (M : Matrix S S ℤ_[p]) (MZ : Matrix (Fin n) (Fin n) ℤ)
    (hM : M.submatrix σ σ = MZ.map (Int.cast : ℤ → ℤ_[p])) (c : ℤ_[p])
    (P Q : Matrix (Fin n) (Fin n) ℤ) (hP : ¬ (p : ℤ) ∣ P.det) (hQ : ¬ (p : ℤ) ∣ Q.det)
    (d : Fin n → ℤ) (hD : P * MZ * Q = diagonal d) :
    Nonempty (((S → ℤ_[p]) ⧸ LinearMap.range (c • M.mulVecLin)) ≃ₗ[ℤ_[p]]
      ((j : Fin n) → ℤ_[p] ⧸ Ideal.span {c * (d j : ℤ_[p])})) := by
  have h1 : c • M.mulVecLin = (c • M).mulVecLin := by
    ext v; simp
  have hmap : ∀ A B : Matrix (Fin n) (Fin n) ℤ,
      (A * B).map (Int.cast : ℤ → ℤ_[p]) = A.map Int.cast * B.map Int.cast := fun A B =>
    Matrix.map_mul (f := Int.castRingHom ℤ_[p])
  have h2 : (c • M).submatrix σ σ = c • MZ.map (Int.cast : ℤ → ℤ_[p]) := by
    rw [← hM]; ext a b; simp
  have h3 : P.map (Int.cast : ℤ → ℤ_[p]) * (c • MZ.map (Int.cast : ℤ → ℤ_[p])) *
      Q.map (Int.cast : ℤ → ℤ_[p]) = diagonal (fun j => c * (d j : ℤ_[p])) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, ← hmap, ← hmap, hD]
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [diagonal_apply_ne _ hab]
  let e1 : ((S → ℤ_[p]) ⧸ LinearMap.range (c • M.mulVecLin)) ≃ₗ[ℤ_[p]]
      ((S → ℤ_[p]) ⧸ LinearMap.range (c • M).mulVecLin) :=
    Submodule.quotEquivOfEq _ _ (by rw [h1])
  let e2 := oddSmithReindexQuot σ (c • M)
  let e3 : ((Fin n → ℤ_[p]) ⧸ LinearMap.range ((c • M).submatrix σ σ).mulVecLin) ≃ₗ[ℤ_[p]]
      ((Fin n → ℤ_[p]) ⧸ LinearMap.range (c • MZ.map (Int.cast : ℤ → ℤ_[p])).mulVecLin) :=
    Submodule.quotEquivOfEq _ _ (by rw [h2])
  let e4 := oddSmithUnitQuot (c • MZ.map (Int.cast : ℤ → ℤ_[p])) (P.map (Int.cast : ℤ → ℤ_[p]))
    (Q.map (Int.cast : ℤ → ℤ_[p])) (oddSmith_isUnit_det_map p hP) (oddSmith_isUnit_det_map p hQ)
  let e5 : ((Fin n → ℤ_[p]) ⧸ LinearMap.range (P.map (Int.cast : ℤ → ℤ_[p]) *
      (c • MZ.map (Int.cast : ℤ → ℤ_[p])) * Q.map (Int.cast : ℤ → ℤ_[p])).mulVecLin) ≃ₗ[ℤ_[p]]
      ((Fin n → ℤ_[p]) ⧸ LinearMap.range (diagonal (fun j => c * (d j : ℤ_[p]))).mulVecLin) :=
    Submodule.quotEquivOfEq _ _ (by rw [h3])
  exact ⟨e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (oddSmithDiagQuot _)))))⟩

lemma oddSmith_span_unit_pow {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) (k E : ℕ) :
    Ideal.span {(p : ℤ_[p]) ^ k * (((u * (p : ℤ) ^ E : ℤ)) : ℤ_[p])} =
      Ideal.span {(p : ℤ_[p]) ^ (k + E)} := by
  rw [show (p : ℤ_[p]) ^ k * (((u * (p : ℤ) ^ E : ℤ)) : ℤ_[p]) = (u : ℤ_[p]) * (p : ℤ_[p]) ^ (k + E)
    by push_cast; ring]
  exact Ideal.span_singleton_mul_left_unit (oddSmith_isUnit_int p hu) _

/-- The cokernel in the full-rank case (Part Y of `CSI18_theorem_4_4_smith_form_of_Mp.md`). -/
theorem oddSmith_coker_full {S : Type*} [Fintype S] [DecidableEq S] {n : ℕ} (σ : Fin n ≃ S)
    (M : Matrix S S ℤ_[p]) (MZ : Matrix (Fin n) (Fin n) ℤ)
    (hM : M.submatrix σ σ = MZ.map (Int.cast : ℤ → ℤ_[p])) (k : ℕ)
    (P Q : Matrix (Fin n) (Fin n) ℤ) (hP : ¬ (p : ℤ) ∣ P.det) (hQ : ¬ (p : ℤ) ∣ Q.det)
    (u : ℕ → ℤ) (hu : ∀ j, ¬ (p : ℤ) ∣ u j) (E : ℕ → ℕ)
    (hD : P * MZ * Q = diagonal (fun j : Fin n => u j * (p : ℤ) ^ E j)) :
    Nonempty (((S → ℤ_[p]) ⧸ LinearMap.range ((p : ℤ_[p]) ^ k • M.mulVecLin)) ≃ₗ[ℤ_[p]]
      ((j : Fin n) → Zq p (k + E j))) := by
  obtain ⟨e1⟩ := oddSmith_coker_of_smith p σ M MZ hM _ P Q hP hQ _ hD
  exact ⟨e1.trans (LinearEquiv.piCongrRight fun j =>
    Submodule.quotEquivOfEq _ _ (oddSmith_span_unit_pow p (hu j) k (E j)))⟩

/-- The cokernel in the corank-one case (Part Y of `CSI18_theorem_4_4_smith_form_of_Mp.md`): the last
diagonal entry is `0`. -/
theorem oddSmith_coker_corank_one {S : Type*} [Fintype S] [DecidableEq S] {N : ℕ} (hN : 1 ≤ N)
    (σ : Fin N ≃ S) (M : Matrix S S ℤ_[p]) (MZ : Matrix (Fin N) (Fin N) ℤ)
    (hM : M.submatrix σ σ = MZ.map (Int.cast : ℤ → ℤ_[p])) (k : ℕ)
    (P Q : Matrix (Fin N) (Fin N) ℤ) (hP : ¬ (p : ℤ) ∣ P.det) (hQ : ¬ (p : ℤ) ∣ Q.det)
    (u : ℕ → ℤ) (hu : ∀ j, ¬ (p : ℤ) ∣ u j) (E : ℕ → ℕ)
    (hD : P * MZ * Q = diagonal (fun j : Fin N =>
      if (j : ℕ) < N - 1 then u j * (p : ℤ) ^ E j else 0)) :
    Nonempty (((S → ℤ_[p]) ⧸ LinearMap.range ((p : ℤ_[p]) ^ k • M.mulVecLin)) ≃ₗ[ℤ_[p]]
      (ℤ_[p] × ((j : Fin (N - 1)) → Zq p (k + E j)))) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  obtain ⟨e1⟩ := oddSmith_coker_of_smith p σ M MZ hM _ P Q hP hQ _ hD
  have hlast : Ideal.span {(p : ℤ_[p]) ^ k *
      (((if ((Fin.last n : Fin (n + 1)) : ℕ) < n + 1 - 1 then u (Fin.last n) * (p : ℤ) ^ E (Fin.last n)
        else 0 : ℤ)) : ℤ_[p])} = ⊥ := by
    rw [if_neg (by simp), Int.cast_zero, mul_zero, Ideal.span_singleton_eq_bot]
  have hcs : ∀ j : Fin n, Ideal.span {(p : ℤ_[p]) ^ k *
      (((if ((Fin.castSucc j : Fin (n + 1)) : ℕ) < n + 1 - 1 then
        u (Fin.castSucc j) * (p : ℤ) ^ E (Fin.castSucc j) else 0 : ℤ)) : ℤ_[p])} =
      Ideal.span {(p : ℤ_[p]) ^ (k + E j)} := fun j => by
    rw [if_pos (by simp)]
    exact oddSmith_span_unit_pow p (hu j) k (E j)
  exact ⟨e1.trans ((oddSmithSnocEquiv _).trans (LinearEquiv.prodCongr
    (Submodule.quotEquivOfEqBot _ hlast)
    (LinearEquiv.piCongrRight fun j => Submodule.quotEquivOfEq _ _ (hcs j))))⟩

/-- **(Y1)**, `i ≥ 1` (Part Y of `CSI18_theorem_4_4_smith_form_of_Mp.md`): for an odd prime `p`,
`e ≥ 1` and `i ≥ 1`,
`(slots → ℤ_[p]) ⧸ range (p^k • Mp p λ i e) ≃ₗ[ℤ_[p]] Π_{j<N} ℤ_[p] ⧸ p^{k + C + ŷ(N−1−j)}`. -/
theorem oddSmith_Y1_pos (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) :
    ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l),
        (E j : ℤ) = oddSmithC p l i e + oddSmithYhat p l i e (2 ^ #(Iset p l) - 1 - j)) ∧
      Nonempty (Cmod p l i e ≃ₗ[ℤ_[p]] ((j : Fin (2 ^ #(Iset p l))) → Zq p (kTop p l + E j))) := by
  obtain ⟨P, Q, hP, hQ, u, hu, E, hE, hD⟩ := oddSmith_S3 p hodd l i e he hi
  exact ⟨E, hE, oddSmith_coker_full p (oddSmithSlot p l i e) (Mp p l i e) (oddSmithMZ p l i e)
    (oddSmith_Z0 p l i e) (kTop p l) P Q hP hQ u hu E hD⟩

/-- **(Y1)**, `i = 0`, `I ≠ ∅` (Part Y of `CSI18_theorem_4_4_smith_form_of_Mp.md`): for an odd prime
`p` and `e ≥ 1`,
`(slots → ℤ_[p]) ⧸ range (p^k • Mp p λ 0 e) ≃ₗ[ℤ_[p]] ℤ_[p] × Π_{j<N−1} ℤ_[p] ⧸ p^{k + eK + ŷ^♯(N−2−j)}`. -/
theorem oddSmith_Y1_zero (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hne : (Iset p l).Nonempty) :
    ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l) - 1,
        (E j : ℤ) = (e : ℤ) * (oddSmithK p l : ℤ) +
          oddSmithYhatSharp p l e (2 ^ #(Iset p l) - 2 - j)) ∧
      Nonempty (Cmod p l 0 e ≃ₗ[ℤ_[p]]
        (ℤ_[p] × ((j : Fin (2 ^ #(Iset p l) - 1)) → Zq p (kTop p l + E j)))) := by
  obtain ⟨P, Q, hP, hQ, u, hu, E, hE, hD⟩ := oddSmith_Z3 p hodd l e he hne
  exact ⟨E, hE, oddSmith_coker_corank_one p Nat.one_le_two_pow (oddSmithSlot p l 0 e) (Mp p l 0 e)
    (oddSmithMZ p l 0 e) (oddSmith_Z0 p l 0 e) (kTop p l) P Q hP hQ u hu E hD⟩

/-- **(Y1)**, `i = 0`, `I = ∅` (Part Y of `CSI18_theorem_4_4_smith_form_of_Mp.md`): for `e ≥ 1`,
`(slots → ℤ_[p]) ⧸ range (p^k • Mp p λ 0 e) ≃ₗ[ℤ_[p]] ℤ_[p]` (one slot, `Mp = 0`). Oddness of `p` is
not needed. -/
theorem oddSmith_Y1_zero_empty (l e : ℕ) (he : 1 ≤ e) (hI : Iset p l = ∅) :
    Nonempty (Cmod p l 0 e ≃ₗ[ℤ_[p]] ℤ_[p]) := by
  have hMZ := (oddSmith_Z1 p l e he).2.2 hI
  have hMp : Mp p l 0 e = 0 := by
    ext x y
    obtain ⟨a, rfl⟩ := (oddSmithSlot p l 0 e).surjective x
    obtain ⟨b, rfl⟩ := (oddSmithSlot p l 0 e).surjective y
    rw [← oddSmith_MZ_cast, hMZ]; simp
  have hbot : LinearMap.range ((p : ℤ_[p]) ^ kTop p l • (Mp p l 0 e).mulVecLin) = ⊥ := by
    rw [hMp]; ext v; simp
  have hcard : Fintype.card (slots p l 0 e) = 1 := by rw [card_slots, hI, card_empty, pow_zero]
  obtain ⟨hU⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 hcard
  exact ⟨(Submodule.quotEquivOfEqBot _ hbot).trans (LinearEquiv.funUnique _ ℤ_[p] ℤ_[p])⟩

/-- **(Y2)**, `i ≥ 1` (Part Y of `CSI18_theorem_4_4_smith_form_of_Mp.md`, with CSI10's Theorem D_p):
for an odd prime `p`, `e ≥ 1` and `i ≥ 1`,
`Y_p(λ, i, e) ≃ₗ[ℤ_[p]] S_p(λ) × Π_{j<N} ℤ_[p] ⧸ p^{k + C + ŷ(N−1−j)}`. -/
theorem oddSmith_Y2_pos (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) :
    ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l),
        (E j : ℤ) = oddSmithC p l i e + oddSmithYhat p l i e (2 ^ #(Iset p l) - 1 - j)) ∧
      Nonempty (Yp p l i e ≃ₗ[ℤ_[p]]
        (Sp p l × ((j : Fin (2 ^ #(Iset p l))) → Zq p (kTop p l + E j)))) := by
  obtain ⟨E, hE, ⟨e2⟩⟩ := oddSmith_Y1_pos p hodd l i e he hi
  obtain ⟨e1⟩ := I1 p hodd l i e he
  exact ⟨E, hE, ⟨e1.trans (LinearEquiv.prodCongr (LinearEquiv.refl _ _) e2)⟩⟩

/-- **(Y2)**, `i = 0`, `I ≠ ∅` (Part Y of `CSI18_theorem_4_4_smith_form_of_Mp.md`, with CSI10's
Theorem D_p): for an odd prime `p` and `e ≥ 1`,
`Y_p(λ, 0, e) ≃ₗ[ℤ_[p]] S_p(λ) × (ℤ_[p] × Π_{j<N−1} ℤ_[p] ⧸ p^{k + eK + ŷ^♯(N−2−j)})`. -/
theorem oddSmith_Y2_zero (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hne : (Iset p l).Nonempty) :
    ∃ E : ℕ → ℕ, (∀ j < 2 ^ #(Iset p l) - 1,
        (E j : ℤ) = (e : ℤ) * (oddSmithK p l : ℤ) +
          oddSmithYhatSharp p l e (2 ^ #(Iset p l) - 2 - j)) ∧
      Nonempty (Yp p l 0 e ≃ₗ[ℤ_[p]]
        (Sp p l × (ℤ_[p] × ((j : Fin (2 ^ #(Iset p l) - 1)) → Zq p (kTop p l + E j))))) := by
  obtain ⟨E, hE, ⟨e2⟩⟩ := oddSmith_Y1_zero p hodd l e he hne
  obtain ⟨e1⟩ := I1 p hodd l 0 e he
  exact ⟨E, hE, ⟨e1.trans (LinearEquiv.prodCongr (LinearEquiv.refl _ _) e2)⟩⟩

/-- **(Y2)**, `i = 0`, `I = ∅` (Part Y of `CSI18_theorem_4_4_smith_form_of_Mp.md`, with CSI10's
Theorem D_p): for an odd prime `p` and `e ≥ 1`, `Y_p(λ, 0, e) ≃ₗ[ℤ_[p]] S_p(λ) × ℤ_[p]`. -/
theorem oddSmith_Y2_zero_empty (hodd : Odd p) (l e : ℕ) (he : 1 ≤ e) (hI : Iset p l = ∅) :
    Nonempty (Yp p l 0 e ≃ₗ[ℤ_[p]] (Sp p l × ℤ_[p])) := by
  obtain ⟨e2⟩ := oddSmith_Y1_zero_empty p l e he hI
  obtain ⟨e1⟩ := I1 p hodd l 0 e he
  exact ⟨e1.trans (LinearEquiv.prodCongr (LinearEquiv.refl _ _) e2)⟩

end ColouredSand.OddTwist
