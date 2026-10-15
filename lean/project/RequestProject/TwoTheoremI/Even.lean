module

public import RequestProject.FamilyGroup.All
public import RequestProject.Windows.All
public import RequestProject.Families.All

/-!
# `CSX2_theorem_I_prime_two.md`, Setting and Part E — the final matrix is even

Namespace `ColouredSand.TwoI`.

## Encodings (the *Setting* of `CSX2_theorem_I_prime_two.md`)

Everything is reused from the Dancing Sand modules of this project:

* `ds : List Bool` is a digit list, lowest digit first; `k = ds.length`,
  `n = Dance.mCount ds` (`= |I|`, with `I = Windows.Ids ds`, by `Windows.card_Ids`), `N = 2 ^ n`.
  For a family `λ` one takes `ds = Families.ds λ` (see `Digits.lean` for (I6)).
* `α : ℕ` with `α ≥ 1` (it is `e = v_2(q)`), `i : ℕ`.
* `M = Windows.finalMatrix ℤ ds α i : Matrix (Fin N) (Fin N) ℤ` is the final matrix of the dance.
* `CmodTwo ds α i := (Fin N → ℤ_[2]) ⧸ range (2^k • Matrix.toLin' (M.map (Int.castRingHom ℤ_[2])))`
  is the "big" part `coker(2^k M)` of Theorem D (the second factor of `FamilyGroup.X_equiv_coker`).
* "`2 ∣ M s s'`" is divisibility in `ℤ`.
* The Smith forms are those of `DanceSmith.S3` (`i ≥ 1`) and `DanceSmith.Z3` (`i = 0`), whose
  exponents are `(E j : ℤ) = Cst + yHat ds α i (N − 1 − j)`, resp. `α 2^k + yHatS ds α (N − 2 − j)`;
  (E2) is stated directly on these clocks.

## Statements

* **(E1)** `twoI_E1`: for `α ≥ 1`, every `ds` (also `k = 0`) and every `i`, `2 ∣ M s s'`.
  For `k = 0` the matrix is `1 × 1` with entry `2^α i` (`twoI_finalMatrix_nil`).
  No convention beyond those of Theorem D (`Windows.theorem_D_ii`, `theorem_D_iii`) is needed.
* **(E2)** `twoI_E2_pos` (`i ≥ 1`) and `twoI_E2_zero` (`i = 0`, `I ≠ ∅`), together with the
  general principle `twoI_one_le_of_smith`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.TwoI

open Finset Matrix Windows

/-- *Setting* of `CSX2_theorem_I_prime_two.md`: `CmodTwo ds α i := coker(2^k M)` over `ℤ_[2]`,
i.e. `(Fin N → ℤ_[2]) ⧸ range (2^k • Matrix.toLin' (M.map (Int.castRingHom ℤ_[2])))` with
`M = finalMatrix ℤ ds α i`, `k = ds.length`, `N = 2 ^ Dance.mCount ds`. -/
abbrev CmodTwo (ds : List Bool) (α i : ℕ) : Type :=
  (Fin (2 ^ Dance.mCount ds) → ℤ_[2]) ⧸ LinearMap.range ((2 : ℤ_[2]) ^ ds.length •
    Matrix.toLin' ((finalMatrix ℤ ds α i).map (Int.castRingHom ℤ_[2])))

/-- The closed-form entry on the empty dancers with `k = 0` is `2^α i` (auxiliary for (E1) of
`CSX2_theorem_I_prime_two.md`, case `k = 0`). -/
lemma twoI_Mc_nil (α i : ℕ) :
    Deficit.Mc ∅ 0 (α : ℤ) i ∅ ∅ = (2 : ℚ) ^ α * i := by
  simp [Deficit.Mc, Deficit.a, Rulers.oE_empty, Deficit.pi0]

/-- For `ds = []` (`k = 0`, `N = 1`) the final matrix is the `1 × 1` matrix `(2^α i)` (Part E of
`CSX2_theorem_I_prime_two.md`, case `k = 0`, "compute the `1 × 1` matrix directly"). -/
theorem twoI_finalMatrix_nil (α i : ℕ) (hα : 1 ≤ α) (s s' : Fin (2 ^ Dance.mCount [])) :
    finalMatrix ℤ [] α i s s' = 2 ^ α * i := by
  have hI : Ids [] = ∅ := by simp [Ids]
  have hD : ∀ s : ℕ, Dset [] s = ∅ := fun s => by simp [Dset, hI]
  have h := (theorem_D_ii [] α i hα s s').1 (by rw [hD, hD])
  rw [hD, hD, hI, show ([] : List Bool).length = 0 from rfl, twoI_Mc_nil] at h
  exact_mod_cast h

/-- `o(E) = 0` only for `E = ∅` (auxiliary for (E1) of `CSX2_theorem_I_prime_two.md`). -/
lemma twoI_oE_eq_zero {E : Finset ℕ} (h : Rulers.oE E = 0) : E = ∅ := by
  by_contra hne
  obtain ⟨t, ht⟩ := Finset.nonempty_iff_ne_empty.2 hne
  have : 2 ^ t ≤ Rulers.oE E := by
    unfold Rulers.oE
    exact Finset.single_le_sum (f := fun t => 2 ^ t) (fun _ _ => Nat.zero_le _) ht
  have := Nat.one_le_two_pow (n := t)
  omega

/-- The valuation bound of (E1) of `CSX2_theorem_I_prime_two.md`: in the situation of
`Windows.theorem_D_iii`, `v_2(M s s') ≥ 1`. -/
lemma twoI_val_ge_one (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α)
    (s s' : Fin (2 ^ Dance.mCount ds)) (hD : Dset ds s' ⊆ Dset ds s)
    (hi : 0 < i + Rulers.oE (Dset ds s)) :
    1 ≤ padicValInt 2 (finalMatrix ℤ ds α i s s') := by
  obtain ⟨-, hv⟩ := theorem_D_iii ds hk α i hα s s' hD hi
  set A := Rulers.oE (Dset ds s)
  set B := Rulers.oE (Dset ds s')
  set Δ := Dset ds s \ Dset ds s'
  have hΔI : Δ ⊆ Ids ds := sdiff_subset.trans (filter_subset _ _)
  have hAB : Rulers.oE Δ + B = A := Rulers.oE_sdiff hD
  have hlt : Rulers.oE Δ < 2 ^ ds.length :=
    Rulers.oE_lt _ _ (fun t ht => lt_of_mem_Ids (hΔI ht))
  have hdelta : 0 ≤ Rulers.delta ds.length Δ := by
    rw [← (Deficit.lemma_4_5 hk (fun t ht => lt_of_mem_Ids ht) hΔI).2]
    exact Int.natCast_nonneg _
  have hsum : ((B + 2 ^ ds.length - A : ℕ) : ℤ) * α ≤
      ∑ d ∈ Ico A (B + 2 ^ ds.length), ((α : ℤ) + (Rulers.v2 (i + d) : ℤ)) := by
    have h1 : ∑ d ∈ Ico A (B + 2 ^ ds.length), (α : ℤ) ≤
        ∑ d ∈ Ico A (B + 2 ^ ds.length), ((α : ℤ) + (Rulers.v2 (i + d) : ℤ)) :=
      sum_le_sum fun d _ => by have := Int.natCast_nonneg (Rulers.v2 (i + d)); linarith
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul] at h1
    exact h1
  have hcast : ((B + 2 ^ ds.length - A : ℕ) : ℤ) = (2 : ℤ) ^ ds.length - Rulers.oE Δ := by
    rw [Nat.cast_sub (by omega)]; push_cast; rw [← hAB]; push_cast; ring
  rw [hcast] at hsum
  have hx : (1 : ℤ) ≤ (2 : ℤ) ^ ds.length - Rulers.oE Δ := by
    have : ((Rulers.oE Δ : ℕ) : ℤ) < ((2 ^ ds.length : ℕ) : ℤ) := by exact_mod_cast hlt
    push_cast at this; linarith
  have hα' : (1 : ℤ) ≤ α := by exact_mod_cast hα
  have : (1 : ℤ) ≤ (padicValInt 2 (finalMatrix ℤ ds α i s s') : ℤ) := by
    rw [hv]; nlinarith
  exact_mod_cast this

/-- **(E1)** of `CSX2_theorem_I_prime_two.md` (Part E, the final matrix is even): for `α ≥ 1`,
every digit list `ds` (also `k = 0`) and every `i`, every entry of `M = finalMatrix ℤ ds α i` is
even. -/
theorem twoI_E1 (ds : List Bool) (α i : ℕ) (hα : 1 ≤ α) (s s' : Fin (2 ^ Dance.mCount ds)) :
    2 ∣ finalMatrix ℤ ds α i s s' := by
  rcases Nat.eq_zero_or_pos ds.length with hk | hk
  · obtain rfl : ds = [] := List.eq_nil_of_length_eq_zero hk
    rw [twoI_finalMatrix_nil α i hα]
    exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _
  by_cases hD : Dset ds s' ⊆ Dset ds s
  swap
  · rw [(theorem_D_ii ds α i hα s s').2 hD]; exact dvd_zero _
  by_cases hi : 0 < i + Rulers.oE (Dset ds s)
  · have h1 := twoI_val_ge_one ds hk α i hα s s' hD hi
    exact (dvd_pow_self (2 : ℤ) (by omega)).trans
      (padicValInt_dvd (p := 2) (finalMatrix ℤ ds α i s s'))
  · have hi0 : i = 0 := by omega
    have hs0 : Dset ds s = ∅ := twoI_oE_eq_zero (by omega)
    have hs0' : Dset ds s' = ∅ := subset_empty.1 (hs0 ▸ hD)
    have hM := (theorem_D_ii ds α i hα s s').1 hD
    rw [hs0, hs0', hi0] at hM
    have hMc : Deficit.Mc (Ids ds) ds.length (α : ℤ) 0 ∅ ∅ = 0 := by
      unfold Deficit.Mc
      apply mul_eq_zero_of_right
      apply prod_eq_zero (i := 0)
      · simp [Rulers.oE_empty]
      · simp [Deficit.pi0]
    rw [hMc] at hM
    have : finalMatrix ℤ ds α 0 s s' = 0 := by exact_mod_cast hM
    rw [hi0, this]; exact dvd_zero _

/-- The principle behind (E2) of `CSX2_theorem_I_prime_two.md`: if `P M Q = diag(d)` and every entry
of `M` is even, then every `d j` is even. -/
lemma twoI_even_of_smith {n : ℕ} (P M Q : Matrix (Fin n) (Fin n) ℤ) (hM : ∀ s s', 2 ∣ M s s')
    (d : Fin n → ℤ) (h : P * M * Q = diagonal d) (j : Fin n) : 2 ∣ d j := by
  choose M' hM' using hM
  have hM2 : M = (2 : ℤ) • Matrix.of M' := by ext s s'; simp [hM']
  have := congrFun (congrFun h j) j
  rw [diagonal_apply_eq, hM2, Matrix.mul_smul, Matrix.smul_mul] at this
  rw [← this, Matrix.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

/-- (E2) of `CSX2_theorem_I_prime_two.md`, the principle: if `P M Q = diag(u_j 2^{E_j})` with
`2 ∣ M` and `u_j` odd, then `E_j ≥ 1`. -/
lemma twoI_one_le_of_smith {n : ℕ} (P M Q : Matrix (Fin n) (Fin n) ℤ) (hM : ∀ s s', 2 ∣ M s s')
    (u : Fin n → ℤ) (hu : ∀ j, Odd (u j)) (E : Fin n → ℕ)
    (h : P * M * Q = diagonal (fun j => u j * 2 ^ E j)) (j : Fin n) : 1 ≤ E j := by
  have h2 := twoI_even_of_smith P M Q hM _ h j
  by_contra h0
  have hE : E j = 0 := by omega
  simp only [hE, pow_zero, mul_one] at h2
  exact (Int.not_even_iff_odd.2 (hu j)) (even_iff_two_dvd.2 h2)

/-- **(E2)** of `CSX2_theorem_I_prime_two.md`, case `i ≥ 1` (Part E): for `k ≥ 1`, `α ≥ 1`,
`i ≥ 1` and every position `p < N`, `1 ≤ C + ŷ(p)` (`C = DanceSmith.Cst ds α i`,
`ŷ = DanceSmith.yHat ds α i`); equivalently every exponent `E j` of `DanceSmith.S3` is `≥ 1`. -/
theorem twoI_E2_pos (ds : List Bool) (hk : 1 ≤ ds.length) (α i : ℕ) (hα : 1 ≤ α) (hi : 1 ≤ i)
    (p : ℕ) (hp : p < 2 ^ Dance.mCount ds) :
    1 ≤ DanceSmith.Cst ds α i + DanceSmith.yHat ds α i p := by
  obtain ⟨P, Q, -, -, u, hu, E, hE, hD⟩ := DanceSmith.S3 ds hk α i hα hi
  have h1 := twoI_one_le_of_smith P _ Q (twoI_E1 ds α i hα) (fun j => u j) (fun j => hu j)
    (fun j => E j) hD ⟨2 ^ Dance.mCount ds - 1 - p, by omega⟩
  have h2 := hE (2 ^ Dance.mCount ds - 1 - p) (by omega)
  rw [show 2 ^ Dance.mCount ds - 1 - (2 ^ Dance.mCount ds - 1 - p) = p by omega] at h2
  have : (1 : ℤ) ≤ (E (2 ^ Dance.mCount ds - 1 - p) : ℤ) := by exact_mod_cast h1
  linarith

/-- **(E2)** of `CSX2_theorem_I_prime_two.md`, case `i = 0` (Part E): for `k ≥ 1`, `α ≥ 1`,
`I ≠ ∅` and every position `q < N − 1`, `1 ≤ α 2^k + ŷ^♯(q)` (`ŷ^♯ = DanceSmith.yHatS ds α`);
equivalently every exponent `E j` (`j < N − 1`) of `DanceSmith.Z3` is `≥ 1`. -/
theorem twoI_E2_zero (ds : List Bool) (hk : 1 ≤ ds.length) (α : ℕ) (hα : 1 ≤ α)
    (hne : Ids ds ≠ ∅) (q : ℕ) (hq : q < 2 ^ Dance.mCount ds - 1) :
    1 ≤ (α : ℤ) * 2 ^ ds.length + DanceSmith.yHatS ds α q := by
  obtain ⟨P, Q, -, -, u, hu, E, hE, hD⟩ := DanceSmith.Z3 ds hk α hα hne
  have h2 := twoI_even_of_smith P _ Q (twoI_E1 ds α 0 hα) _ hD ⟨2 ^ Dance.mCount ds - 2 - q, by omega⟩
  simp only [show 2 ^ Dance.mCount ds - 2 - q < 2 ^ Dance.mCount ds - 1 by omega, if_true] at h2
  have h1 : 1 ≤ E (2 ^ Dance.mCount ds - 2 - q) := by
    by_contra h0
    rw [show E (2 ^ Dance.mCount ds - 2 - q) = 0 by omega, pow_zero, mul_one] at h2
    exact (Int.not_even_iff_odd.2 (hu _)) (even_iff_two_dvd.2 h2)
  have h3 := hE (2 ^ Dance.mCount ds - 2 - q) (by omega)
  rw [show 2 ^ Dance.mCount ds - 2 - (2 ^ Dance.mCount ds - 2 - q) = q by omega] at h3
  have : (1 : ℤ) ≤ (E (2 ^ Dance.mCount ds - 2 - q) : ℤ) := by exact_mod_cast h1
  linarith

end ColouredSand.TwoI
