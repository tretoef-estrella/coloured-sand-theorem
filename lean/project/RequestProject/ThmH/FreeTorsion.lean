module

public import RequestProject.Splitting.Rescaling

/-!
# `CSH1_theorem_H_the_prime_two.md`, (T3) — rank and torsion of the cokernel of `q (c + H) + U`

Namespace `ColouredSand.ThmH`.  Auxiliary to (T3) of `CSH1_theorem_H_the_prime_two.md`: over a
commutative domain `R`, for `q ≠ 0` and `c : ℕ` (with `R` of characteristic zero), the cokernel
`N = B m R ⧸ range (opM m R q c)` is `R^{[c = 0]} ⊕ tors N`, where `R^{[c=0]}` is encoded as
`Fin (if c = 0 then 1 else 0) → R` and `tors N` as `Submodule.torsion R N`.

Proof (as in the file): `opM e_T = q (c + |T|) e_T + Σ_{x ∉ T} e_{T ∪ {x}}` is triangular for the
order by size, with diagonal `q (c + |T|)`, which vanishes only at `T = ∅` when `c = 0`.  By
downward induction on `|T|`, the class of every `e_T` with `q (c + |T|) ≠ 0` is torsion.  When
`c = 0`, the coordinate at `∅` vanishes on the range of `opM` and splits off a free summand `R`
(section `r ↦ [r e_∅]`), whose kernel is exactly the torsion.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.ThmH

open Finset ColouredSand.Strings

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R]

omit [CharZero R] in
/-- If `a ≠ 0` and `a • x` is torsion, then `x` is torsion (auxiliary for (T3)). -/
lemma mem_torsion_of_smul_mem {M : Type*} [AddCommGroup M] [Module R M] {a : R} (ha : a ≠ 0)
    {x : M} (h : a • x ∈ Submodule.torsion R M) : x ∈ Submodule.torsion R M := by
  rw [Submodule.mem_torsion_iff] at h ⊢
  obtain ⟨b, hb⟩ := h
  refine ⟨b * ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩, ?_⟩
  rw [mul_smul]
  simpa [Submonoid.smul_def] using hb

/-- The class of `e_T` in the cokernel of `opM` is torsion whenever `c + |T| ≠ 0`
(auxiliary for (T3); downward induction on `|T|`). -/
lemma mk_single_mem_torsion (m : ℕ) {q : R} (hq : q ≠ 0) (c : ℕ) (T : Finset (Fin m))
    (hT : c ≠ 0 ∨ T.Nonempty) :
    Submodule.Quotient.mk (p := LinearMap.range (opM m R q (c : R))) (Pi.single T 1) ∈
      Submodule.torsion R (B m R ⧸ LinearMap.range (opM m R q (c : R))) := by
  induction h : m - T.card using Nat.strong_induction_on generalizing T with
  | _ k ih =>
    subst h
    set P := LinearMap.range (opM m R q (c : R))
    have hrel : opM m R q (c : R) (Pi.single T 1) =
        (q * ((c : R) + T.card)) • (Pi.single T 1 : B m R) +
          ∑ x ∈ Tᶜ, (Pi.single (insert x T) 1 : B m R) := by
      rw [← U_single]
      ext S
      simp only [opM, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      simp only [ColouredSand.Strings.H, LinearMap.coe_mk, AddHom.coe_mk]
      by_cases hS : S = T
      · subst hS; simp
      · simp [Pi.single_apply, hS]
    have hzero : Submodule.Quotient.mk (p := P) (opM m R q (c : R) (Pi.single T 1)) = 0 :=
      (Submodule.Quotient.mk_eq_zero P).2 (LinearMap.mem_range_self _ _)
    rw [hrel, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul,
      add_eq_zero_iff_eq_neg] at hzero
    have hsum : Submodule.Quotient.mk (p := P) (∑ x ∈ Tᶜ, (Pi.single (insert x T) 1 : B m R)) ∈
        Submodule.torsion R (B m R ⧸ P) := by
      rw [← Submodule.mkQ_apply, map_sum]
      refine Submodule.sum_mem _ fun x hx => ?_
      have hxT : x ∉ T := by simpa using hx
      have hlt : m - (insert x T).card < m - T.card := by
        rw [card_insert_of_notMem hxT]
        have : (insert x T).card ≤ m := by
          simpa using card_le_univ (insert x T)
        rw [card_insert_of_notMem hxT] at this
        omega
      exact ih _ hlt (insert x T) (Or.inr (insert_nonempty x T)) rfl
    have hne : q * ((c : R) + T.card) ≠ 0 := by
      refine mul_ne_zero hq ?_
      have : c + T.card ≠ 0 := by
        rcases hT with hc | hT
        · omega
        · have := hT.card_pos; omega
      exact_mod_cast this
    refine mem_torsion_of_smul_mem hne ?_
    rw [hzero]
    exact Submodule.neg_mem _ hsum

/-- Every class `[g]` with `g ∅ = 0` (or any class when `c ≠ 0`) is torsion (auxiliary for (T3)). -/
lemma mk_mem_torsion (m : ℕ) {q : R} (hq : q ≠ 0) (c : ℕ) (g : B m R)
    (hg : c ≠ 0 ∨ g ∅ = 0) :
    Submodule.Quotient.mk (p := LinearMap.range (opM m R q (c : R))) g ∈
      Submodule.torsion R (B m R ⧸ LinearMap.range (opM m R q (c : R))) := by
  have hg' : g = ∑ T, g T • (Pi.single T 1 : B m R) := by
    ext S; simp [Finset.sum_apply, Pi.single_apply]
  rw [hg', ← Submodule.mkQ_apply, map_sum]
  refine Submodule.sum_mem _ fun T _ => ?_
  rw [map_smul]
  by_cases hT : c ≠ 0 ∨ T.Nonempty
  · exact Submodule.smul_mem _ _ (mk_single_mem_torsion m hq c T hT)
  · push_neg at hT
    obtain ⟨hc, hT⟩ := hT
    subst hT
    rcases hg with hg | hg
    · exact absurd hc hg
    · rw [hg, zero_smul]; exact Submodule.zero_mem _

omit [IsDomain R] in
/-- The coordinate at `∅` vanishes on the range of `opM m R q 0` (auxiliary for (T3)). -/
lemma opM_zero_apply_empty (m : ℕ) (q : R) (g : B m R) :
    opM m R q ((0 : ℕ) : R) g ∅ = 0 := by
  simp [opM, ColouredSand.Strings.H, ColouredSand.Strings.U]

/-- The coordinate at `∅`, on the cokernel of `opM m R q 0` (auxiliary for (T3)). -/
def phiEmpty (m : ℕ) (q : R) :
    (B m R ⧸ LinearMap.range (opM m R q ((0 : ℕ) : R))) →ₗ[R] R :=
  (LinearMap.range (opM m R q ((0 : ℕ) : R))).liftQ (LinearMap.proj ∅) (by
    rintro _ ⟨g, rfl⟩
    exact opM_zero_apply_empty m q g)

/-- The section `r ↦ [r e_∅]` (auxiliary for (T3)). -/
def secEmpty (m : ℕ) (q : R) :
    R →ₗ[R] (B m R ⧸ LinearMap.range (opM m R q ((0 : ℕ) : R))) :=
  (LinearMap.range (opM m R q ((0 : ℕ) : R))).mkQ ∘ₗ LinearMap.single R (fun _ => R) ∅

omit [IsDomain R] in
lemma phiEmpty_secEmpty (m : ℕ) (q : R) (r : R) : phiEmpty m q (secEmpty m q r) = r := by
  simp [phiEmpty, secEmpty]

lemma phiEmpty_torsion (m : ℕ) (q : R) {x : B m R ⧸ LinearMap.range (opM m R q ((0 : ℕ) : R))}
    (hx : x ∈ Submodule.torsion R _) : phiEmpty m q x = 0 := by
  rw [Submodule.mem_torsion_iff] at hx
  obtain ⟨a, ha⟩ := hx
  rw [Submonoid.smul_def] at ha
  have h := congrArg (phiEmpty m q) ha
  rw [map_smul, map_zero, smul_eq_mul] at h
  exact (mul_eq_zero.1 h).resolve_left (nonZeroDivisors.coe_ne_zero a)

lemma sub_secEmpty_mem_torsion (m : ℕ) {q : R} (hq : q ≠ 0)
    (x : B m R ⧸ LinearMap.range (opM m R q ((0 : ℕ) : R))) :
    x - secEmpty m q (phiEmpty m q x) ∈ Submodule.torsion R _ := by
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have : Submodule.Quotient.mk (p := LinearMap.range (opM m R q ((0 : ℕ) : R))) g -
      secEmpty m q (phiEmpty m q (Submodule.Quotient.mk g)) =
      Submodule.Quotient.mk (g - Pi.single ∅ (g ∅)) := by
    simp [phiEmpty, secEmpty, Submodule.Quotient.mk_sub]
  rw [this]
  exact mk_mem_torsion m hq 0 _ (Or.inr (by simp))

/-- **Free part and torsion of the cokernel** (auxiliary for (T3) of
`CSH1_theorem_H_the_prime_two.md`): over a commutative domain of characteristic zero, for
`q ≠ 0` and `c : ℕ`,
`(Fin (if c = 0 then 1 else 0) → R) × tors (coker opM) ≃ₗ[R] coker opM`. -/
def freeTorsionEquiv (m : ℕ) {q : R} (hq : q ≠ 0) (c : ℕ) :
    ((Fin (if c = 0 then 1 else 0) → R) ×
        Submodule.torsion R (B m R ⧸ LinearMap.range (opM m R q (c : R)))) ≃ₗ[R]
      (B m R ⧸ LinearMap.range (opM m R q (c : R))) := by
  by_cases hc : c = 0
  · subst hc
    rw [if_pos rfl]
    let N := B m R ⧸ LinearMap.range (opM m R q ((0 : ℕ) : R))
    let toF : N →ₗ[R] (Fin 1 → R) × Submodule.torsion R N :=
      (LinearMap.pi fun _ => phiEmpty m q).prod
        (LinearMap.codRestrict _ (LinearMap.id - secEmpty m q ∘ₗ phiEmpty m q)
          (fun x => sub_secEmpty_mem_torsion m hq x))
    let invF : (Fin 1 → R) × Submodule.torsion R N →ₗ[R] N :=
      (secEmpty m q ∘ₗ LinearMap.proj 0).coprod (Submodule.subtype _)
    refine (LinearEquiv.ofLinear toF invF ?_ ?_).symm
    · refine LinearMap.ext fun ⟨r, t⟩ => ?_
      have ht := phiEmpty_torsion m q t.2
      have hinv : invF (r, t) = secEmpty m q (r 0) + t := rfl
      change toF (invF (r, t)) = (r, t)
      rw [hinv]
      refine Prod.ext (funext fun i => ?_) (Subtype.ext ?_)
      · change phiEmpty m q (secEmpty m q (r 0) + t) = r i
        rw [map_add, phiEmpty_secEmpty, ht, add_zero, Subsingleton.elim i 0]
      · change secEmpty m q (r 0) + t - secEmpty m q (phiEmpty m q (secEmpty m q (r 0) + t)) = t
        rw [map_add, phiEmpty_secEmpty, ht, add_zero, add_sub_cancel_left]
    · refine LinearMap.ext fun x => ?_
      change secEmpty m q (phiEmpty m q x) + (x - secEmpty m q (phiEmpty m q x)) = x
      abel
  · rw [if_neg hc]
    have htop : Submodule.torsion R (B m R ⧸ LinearMap.range (opM m R q (c : R))) = ⊤ := by
      refine eq_top_iff.2 fun x _ => ?_
      obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact mk_mem_torsion m hq c g (Or.inl hc)
    haveI : Subsingleton (Fin 0 → R) := inferInstance
    exact (LinearEquiv.uniqueProd).trans
      ((LinearEquiv.ofEq _ _ htop).trans (Submodule.topEquiv))

end ColouredSand.ThmH
