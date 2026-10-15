module

public import RequestProject.Families.Group
public import RequestProject.Families.Quot

/-!
# `C32_theorem_38_the_groups_of_the_families.md`: Part T — Theorem 3.8

Encodings (namespace `Families`):

* The hypotheses of C30 (A1) are C28's explicit propositions `H1 φ`, `H2 φ`, `H3 A`,
  `OneAddTwoUnit A` and `h2 : (2 : B) = 0` (for `φ : A →+* B`), passed as arguments, with
  `[IsDomain A] [CharZero A] [OddUnits A]`, exactly as in C31 `FamDec.D2`.
* The cokernel of the Laplacian is `(G n → A) ⧸ range (lap A n)` (C17); products over the list
  `L n` (C31) are dependent function types over `Fin (L n).length`; `(n − λ) / 2` is natural
  subtraction and division.
* (T3) The multiplicity form is a product over `Σ λ : Fin (n + 1), Fin (m λ n)`, with `m λ n`
  C31's multiplicity; it is obtained from (T2) by the reindexing `famReindex`
  `Fin (L n).length ≃ Σ λ : Fin (n + 1), Fin (m λ n)`, which sends a position of `L n` to its
  entry `λ` and to the rank of the position among the occurrences of `λ`.
* For `A = ℤ_[2]` the hypotheses are supplied by C28 `Lift2.Z1` and C21 `Twist.C3_hyp`
  (`B = ZMod 2`, `φ = PadicInt.toZMod`).
-/

@[expose] public section

noncomputable section

namespace Families

open DPLattice Doubling Lemma35 Cocycle Filt Step36 FamDec Lift2

universe u

/-! ### The arithmetic of the support -/

/-- On the support of `L n`, `λ + 2 · ((n − λ) / 2) = n` (from C31 (M3) and `L 0 = [0]`;
auxiliary for (T1) of `C32_theorem_38_the_groups_of_the_families.md`). -/
lemma add_two_mul_half (n lam : ℕ) (h : lam ∈ L n) : lam + 2 * ((n - lam) / 2) = n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [L_zero, List.mem_singleton] at h; subst h; rfl
  · obtain ⟨-, h2, h3⟩ := M3 n hn lam h
    omega

/-! ### (T1) -/

section T1

variable {A B : Type u} [CommRing A] [CommRing B] [IsDomain A] [CharZero A] [OddUnits A]
  {φ : A →+* B}

/-- On a summand `T(λ)` of `V^{⊗n}`, `F + n − H = sigL A λ 1 ((n − λ)/2)` (auxiliary for (T1) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
lemma laplace_eq_sigL (n lam : ℕ) (h : lam ∈ L n) :
    (T A lam).Fd 1 + (n : A) • LinearMap.id - H (T A lam) = sigL A lam 1 ((n - lam) / 2) := by
  have hn : (n : A) = (lam : A) + 2 * (((n - lam) / 2 : ℕ) : A) := by
    have := congrArg (fun z : ℕ => (z : A)) (add_two_mul_half n lam h)
    push_cast at this
    exact this.symm
  rw [sigL, Nat.sub_self, pow_zero, one_smul, hn]
  abel

/-- **(T1)** of `C32_theorem_38_the_groups_of_the_families.md` (explicit equivalence, from an
isomorphism `u : tpow A n ≅ dsumList ((L n).map (T A))` as given by C31 (D2)):
`(G n → A) ⧸ range (lap A n) ≃ₗ[A] Π_j SysT A (ds λ_j) (Fin 1) ⧸ range (sigma A (ds λ_j) 1 ((n − λ_j)/2))`,
`λ_j = (L n).get j`.  Built from (Q0)–(Q2), C18 `C1equiv` and (B2). -/
def T1equiv (n : ℕ) (u : Doubling.Iso (DPLattice.tensorPow A n) (dsumList ((L n).map (T A)))) :
    ((CubeLaplacian.G n → A) ⧸ LinearMap.range (CubeLaplacian.lap A n)) ≃ₗ[A]
      ((j : Fin (L n).length) → Dance.SysT A (ds ((L n).get j)) (Fin 1) ⧸
        LinearMap.range (Dance.sigma A (ds ((L n).get j)) 1 ((n - (L n).get j) / 2))) :=
  let Θ2 := Classical.choose (dsumMap_exists (T A) (L n))
  have hΘ2 := Classical.choose_spec (dsumMap_exists (T A) (L n))
  let Θ := (isoEquiv u).trans Θ2
  have hF : ∀ x, Θ ((DPLattice.tensorPow A n).Fd 1 x) =
      fun j => (T A ((L n).get j)).Fd 1 (Θ x j) := fun x => by
    have := LinearMap.congr_fun (u.hom.comm_F 1) x
    simp only [LinearMap.comp_apply] at this
    simp only [Θ, LinearEquiv.trans_apply]
    rw [← hΘ2.1]
    exact congrArg Θ2 this
  have hH : ∀ x, Θ (H (DPLattice.tensorPow A n) x) =
      fun j => H (T A ((L n).get j)) (Θ x j) := fun x => by
    have := LinearMap.congr_fun u.hom.comm_H x
    simp only [LinearMap.comp_apply] at this
    simp only [Θ, LinearEquiv.trans_apply]
    rw [← hΘ2.2]
    exact congrArg Θ2 this
  (C1equiv n (fun j => T A ((L n).get j)) Θ hF hH).trans
    (LinearEquiv.piCongrRight fun j =>
      (Submodule.quotEquivOfEq _ _
        (congrArg LinearMap.range (laplace_eq_sigL n _ (List.get_mem _ _)))).trans
        (sigEquiv ((L n).get j) 1 ((n - (L n).get j) / 2)))

/-- **(T1)** of `C32_theorem_38_the_groups_of_the_families.md` (list form): under the hypotheses
of C30 (A1), for every `n`,
`(G n → A) ⧸ range (lap A n) ≃ₗ[A]
  Π_{j : Fin (L n).length} SysT A (ds λ_j) (Fin 1) ⧸ range (sigma A (ds λ_j) 1 ((n − λ_j) / 2))`
with `λ_j = (L n).get j`.  From C31 (D2), (Q0)–(Q2), C18 `C1` and (B2). -/
theorem T1 (h1 : H1 φ) (hk : H2 φ) (h3 : H3 A) (hU : OneAddTwoUnit A) (h2 : (2 : B) = 0)
    (n : ℕ) :
    Nonempty (((CubeLaplacian.G n → A) ⧸ LinearMap.range (CubeLaplacian.lap A n)) ≃ₗ[A]
      ((j : Fin (L n).length) → Dance.SysT A (ds ((L n).get j)) (Fin 1) ⧸
        LinearMap.range (Dance.sigma A (ds ((L n).get j)) 1 ((n - (L n).get j) / 2)))) := by
  obtain ⟨u⟩ := FamDec.D2 h1 hk h3 hU h2 n
  rw [Q0] at u
  exact ⟨T1equiv n u⟩

end T1

/-! ### (T2) -/

/-- **(T2)** of `C32_theorem_38_the_groups_of_the_families.md` (Theorem 3.8 of the paper,
`A = ℤ_[2]`): for every `n`,
`ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+ Π_{j : Fin (L n).length} FamilyGroup.X (ds λ_j) 1 ((n − λ_j) / 2)`,
`λ_j = (L n).get j`.  From (T1) (hypotheses by C28 `Lift2.Z1` and C21 `Twist.C3_hyp`) and C17
(D2). -/
theorem T2 (n : ℕ) :
    Nonempty (ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
      ((j : Fin (L n).length) → FamilyGroup.X (ds ((L n).get j)) 1 ((n - (L n).get j) / 2))) := by
  obtain ⟨d⟩ := CubeLaplacian.D2 n
  obtain ⟨e⟩ := T1 (φ := (PadicInt.toZMod : ℤ_[2] →+* ZMod 2)) Lift2.Z1.1 Lift2.Z1.2.1
    Lift2.Z1.2.2.1 Lift2.Z1.2.2.2 Twist.C3_hyp.2.2.2.2.1 n
  exact ⟨d.symm.trans e.toAddEquiv⟩

/-! ### (T3) -/

/-- The number of positions of `l` carrying the entry `a` is `l.count a` (auxiliary for (T3) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
lemma card_get_eq (l : List ℕ) (a : ℕ) :
    Fintype.card {j : Fin l.length // l.get j = a} = l.count a := by
  rw [Fintype.card_subtype]
  have := Fin.card_filter_univ_eq_vector_get_eq_count a (⟨l, rfl⟩ : List.Vector ℕ l.length)
  simpa [List.Vector.get] using this

/-- The reindexing `Fin l.length ≃ Σ a : Fin k, Fin (l.count a.val)` of a list of numbers `< k` by
entry and rank among the occurrences of the entry (auxiliary for (T3) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
def famReindex (l : List ℕ) (k : ℕ) (hl : ∀ x ∈ l, x < k) :
    Fin l.length ≃ Σ a : Fin k, Fin (l.count a.val) :=
  (Equiv.sigmaFiberEquiv (fun j : Fin l.length => (⟨l.get j, hl _ (List.get_mem l j)⟩ : Fin k))).symm.trans
    (Equiv.sigmaCongrRight fun a => Fintype.equivFinOfCardEq (by
      rw [← card_get_eq l a]
      exact Fintype.card_congr (Equiv.subtypeEquivRight fun j => by simp [Fin.ext_iff])))

/-- The reindexing sends a position to its entry (auxiliary for (T3) of
`C32_theorem_38_the_groups_of_the_families.md`). -/
lemma famReindex_get (l : List ℕ) (k : ℕ) (hl : ∀ x ∈ l, x < k) (q : Σ a : Fin k, Fin (l.count a.val)) :
    l.get ((famReindex l k hl).symm q) = q.1 := by
  obtain ⟨a, r⟩ := q
  simp only [famReindex, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.sigmaCongrRight_symm,
    Equiv.sigmaCongrRight_apply, Equiv.sigmaFiberEquiv_apply]
  have key : ∀ x : {j : Fin l.length // (⟨l.get j, hl _ (List.get_mem l j)⟩ : Fin k) = a},
      l.get x.1 = a.1 := fun x => congrArg Fin.val x.2
  exact key _

/-- Transport of the group `X^{(1)}(λ, (n − λ)/2)` along an equality of `λ` (auxiliary for (T3)
of `C32_theorem_38_the_groups_of_the_families.md`). -/
def castX (n : ℕ) {a b : ℕ} (h : a = b) :
    FamilyGroup.X (ds a) 1 ((n - a) / 2) ≃ₗ[ℤ_[2]] FamilyGroup.X (ds b) 1 ((n - b) / 2) := by
  subst h; exact LinearEquiv.refl _ _

/-- **(T3)** of `C32_theorem_38_the_groups_of_the_families.md` (multiplicity form): for every `n`,
`ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+ Π_{q : Σ λ : Fin (n + 1), Fin (m λ n)} FamilyGroup.X (ds q.1) 1 ((n − q.1) / 2)`,
that is `ℤ_2 ⊕ Syl_2 K(Q_n) ≅ ⊕_λ X^{(1)}(λ, (n − λ)/2)^{m_λ(n)}`.  From (T2) and the reindexing
of `L n` by entries and multiplicities (the counting form of C31 (M4)). -/
theorem T3 (n : ℕ) :
    Nonempty (ℤ_[2] × CubeLaplacian.Syl2 (CubeLaplacian.K n) ≃+
      ((q : Σ lam : Fin (n + 1), Fin (m lam n)) →
        FamilyGroup.X (ds q.1) 1 ((n - q.1) / 2))) := by
  obtain ⟨e⟩ := T2 n
  have hl : ∀ x ∈ L n, x < n + 1 := fun x hx => Nat.lt_succ_of_le (le_of_mem_L n x hx)
  let r := famReindex (L n) (n + 1) hl
  let P : ℕ → Type := fun a => FamilyGroup.X (ds a) 1 ((n - a) / 2)
  let e1 : ((j : Fin (L n).length) → P ((L n).get j)) ≃ₗ[ℤ_[2]]
      ((q : Σ a : Fin (n + 1), Fin ((L n).count a.val)) → P q.1) :=
    (LinearEquiv.piCongrLeft ℤ_[2] (fun j => P ((L n).get j)) r.symm).symm.trans
      (LinearEquiv.piCongrRight fun q => castX n (famReindex_get (L n) (n + 1) hl q))
  exact ⟨e.trans e1.toAddEquiv⟩

end Families
