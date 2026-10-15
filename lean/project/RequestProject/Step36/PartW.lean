module

public import RequestProject.Lemma35b.PartL
public import RequestProject.Lift2.All
public import RequestProject.Filt.All

@[expose] public section

noncomputable section

/-!
# `C30_the_step_of_theorem_36.md`: Part W — the isomorphism of C24 preserves weights

Encodings (namespace `Step36`), reusing C18 (`DPLattice`, `tensorV`, `tensorWt`, `wtV`),
C20 (`phi`, `phiWt`, `Iso`), C21 (`baseChange`), C22 (`dsum`, `hL`, `himg`),
C24 (`lemma35Iso`, `lemma35Iso_single`, `L5img`, `uIdx`), C25 (`IsWtPres`) and
C28 (`isWtPres_inverse`):

* A vector of `M` is `M.ι → A`, `δ_i = Pi.single i 1`. The basis of
  `(V ⊗ V ⊗ Φ(N))^φ = baseChange φ (tensorV (tensorV (phi N)))` is `Fin 2 × (Fin 2 × (Fin 2 × N.ι))`,
  the index `(a,(b,(c,i)))` having weight `wV a + wV b + 2 N.wt i + wV c` (`wV = wtV`,
  `wtV 0 = 1`, `wtV 1 = −1`).
* `qWt q` is the weight of the target `L5img i q` minus the common term `2 N.wt i`:
  `qWt (inl r) = 2 wV e' + wV e` with `uIdx r = (e, e')`, and `qWt (inr (inl e)) =
  qWt (inr (inr e)) = wV e`.
* "weight-preserving" is C25's `IsWtPres` (over `B`, for the lattices `baseChange φ _`, which carry
  the weights of the lattices over `A`).
-/

namespace Step36

open DPLattice WeylFilt Doubling Twist Lemma35 Tensor2 Lemma35b LemmaW Cocycle Lift2

section W

variable {A B : Type*} [CommRing A] [CommRing B]

/-- (W1), auxiliary: the weight of the target `L5img i q` of `δ_q` (`q` a basis index of
`D = Δ(3) ⊕ V ⊕ V`) minus the common term `2 N.wt i`. -/
def qWt : ID → ℤ
  | Sum.inl r => 2 * wtV (uIdx r).2 + wtV (uIdx r).1
  | Sum.inr (Sum.inl e) => wtV e
  | Sum.inr (Sum.inr e) => wtV e

/-- (W1), the finite check on the table `himg` (eight rows): every term `δ_q` of
`himg (a,(b,c))` has `qWt q = wV a + wV b + wV c`, i.e. the coefficient of `δ_q` vanishes
otherwise. -/
theorem himg_wt (a b c : Fin 2) (q : ID) (hq : qWt q ≠ wtV a + wtV b + wtV c) :
    himg (B := B) (a, (b, c)) q = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> rcases q with r | e | e <;>
    (try fin_cases r) <;> (try fin_cases e) <;>
    simp_all [himg, qWt, uIdx, wtV, Lemma35.eD, Lemma35.bD, Lemma35.cD]

variable (φ : A →+* B) [IsDomain A] [CharZero A] [OddUnits A] (N : DPLattice A)

/-- (W1), auxiliary: the only basis vector in the support of `L5img i q` has weight
`2 N.wt i + qWt q`. -/
lemma L5img_wt (i : N.ι) (q : ID)
    (j : (baseChange φ (dsum (dsum (phi N) (phi N)) (phi (tensorV N)))).ι)
    (hj : L5img φ N i q j ≠ 0) :
    (baseChange φ (dsum (dsum (phi N) (phi N)) (phi (tensorV N)))).wt j =
      2 * N.wt i + qWt q := by
  rcases q with r | e | e
  · simp only [L5img, Pi.single_apply] at hj
    split_ifs at hj with h
    · subst h
      show 2 * (wtV (uIdx r).2 + N.wt i) + wtV (uIdx r).1 = _
      simp only [qWt]; ring
    · exact absurd rfl hj
  · simp only [L5img, Pi.single_apply] at hj
    split_ifs at hj with h
    · subst h; rfl
    · exact absurd rfl hj
  · simp only [L5img, Pi.single_apply] at hj
    split_ifs at hj with h
    · subst h; rfl
    · exact absurd rfl hj

variable (h2 : (2 : B) = 0)

/-- **(W1)** For every DP-lattice `N` over `A`, the underlying map of C24's
`lemma35Iso φ h2 N : (V ⊗ V ⊗ Φ(N))^φ ≅ (Φ(N)^2 ⊕ Φ(V ⊗ N))^φ` is weight-preserving.
Proof: by `lemma35Iso_single` the image of `δ_{(a,(b,(c,i)))}` is `Σ_q hL(δ_{(a,(b,c))})_q ·
L5img i q`; by the finite check `himg_wt` every term with a nonzero coefficient has target weight
`2 N.wt i + wV a + wV b + wV c` (`L5img_wt`), the weight of the source. -/
theorem W1 : IsWtPres (lemma35Iso φ h2 N).hom.toLin := by
  rintro ⟨a, b, c, i⟩ j hne
  rw [lemma35Iso_single]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [hL, ofImg_single]
  by_cases hq : qWt q = wtV a + wtV b + wtV c
  · by_cases hj : L5img φ N i q j = 0
    · rw [hj, mul_zero]
    · exfalso
      apply hne
      rw [L5img_wt φ N i q j hj, hq]
      show wtV a + (wtV b + (2 * N.wt i + wtV c)) = _
      ring
  · rw [himg_wt a b c q hq, zero_mul]

/-- **(W2)** The inverse map `(lemma35Iso φ h2 N).inv.toLin` is weight-preserving
(C28 `isWtPres_inverse`, from (W1) and the two composites of the `Iso`). -/
theorem W2 : IsWtPres (lemma35Iso φ h2 N).inv.toLin :=
  isWtPres_inverse (W1 φ N h2) (congrArg Hom.toLin (lemma35Iso φ h2 N).hom_inv)
    (congrArg Hom.toLin (lemma35Iso φ h2 N).inv_hom)

end W

end Step36
