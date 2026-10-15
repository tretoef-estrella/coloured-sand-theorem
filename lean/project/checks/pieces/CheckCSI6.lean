import RequestProject.OddDance.All

/-!
# CheckCSI6 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI6 (`CSI6_the_dance_lattices.md`): the dance lattice `L(λ)` by its three
defining cases (`λ + 1 = d₀ + p (b + 1)` written out); the rank by the base-`p` digits; the
tensor rule `V ⊗ L(λ)` in every case with `V ⊗ X` written as `Tensor2.tensor (V ℤ_[p]) X`;
`V^{⊗m} ⊗ ℤ_p ≅ ⊕ L(λ)` for every `m`; additivity of `Φ_p`, `Ψ_r`; agreement with CSG5 in the
range `m ≤ p² + p − 1`; (K3) for simple weights. Then `#print axioms`.
-/

namespace CheckCSI6

open ColouredSand.OddTwist DPLattice

variable {p : ℕ} [Fact p.Prime]

/-- (L1): the three cases of the definition. -/
theorem hL (b d l : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ p - 1) :
    (l + 1 < p → danceL p l = delta ℤ_[p] l) ∧
    danceL p (p * (b + 1) - 1) = twist p (danceL p b) ∧
    danceL p (d + p * (b + 1) - 1) = psi p (danceL p b) d hd1 hd2 := by
  refine ⟨fun h => danceL_lt p h, ?_, danceL_psi_eq p b d hd1 hd2⟩
  have h : p * (b + 1) - 1 = p * b + p - 1 := by rw [Nat.mul_succ]
  rw [h]; exact danceL_twist_eq p b

/-- (L2): rank = leading digit × p^k × 2^(number of nonzero lower digits). -/
theorem hRank (l : ℕ) :
    Fintype.card (danceL p l).ι =
      (Nat.digits p (l + 1)).getD ((Nat.digits p (l + 1)).length - 1) 0 *
        p ^ ((Nat.digits p (l + 1)).length - 1) *
        2 ^ ((Finset.range ((Nat.digits p (l + 1)).length - 1)).filter
          (fun t => (Nat.digits p (l + 1)).getD t 0 ≠ 0)).card :=
  card_danceL_digits p l

/-- (R1): the list of weights of `V ⊗ L(λ)`, every case. -/
theorem hRule (l : ℕ) (hp3 : 3 ≤ p) :
    VdotL p 0 = [1] ∧
    (1 ≤ l → l ≤ p - 2 → VdotL p l = [l + 1, l - 1]) ∧
    (p - 1 ≤ l → (l + 1) % p = 0 → VdotL p l = [l + 1]) ∧
    (p - 1 ≤ l → (l + 1) % p = 1 → VdotL p l = [l + 1, l - 1, l - 1]) ∧
    (p - 1 ≤ l → 2 ≤ (l + 1) % p → (l + 1) % p ≤ p - 2 → VdotL p l = [l + 1, l - 1]) ∧
    (p - 1 ≤ l → (l + 1) % p = p - 1 →
      VdotL p l = (l - 1) :: (VdotL p ((l + 1) / p - 1)).map (fun b' => p * b' + p - 1)) := by
  refine ⟨VdotL_zero p, fun h1 h2 => VdotL_small h1 h2, fun h1 h2 => VdotL_d0_zero (by omega) h1 h2,
    fun h1 h2 => VdotL_d0_one (by omega) h1 h2, fun h1 h2 h3 => VdotL_d0_mid h1 h2 h3,
    fun h1 h2 => VdotL_d0_top hp3 h1 h2⟩

/-- (R2): `V ⊗ L(λ) ≅ ⊕_{μ ∈ VdotL λ} L(μ)` for every `λ`, `p` odd. -/
theorem hTensor (hp2 : p ≠ 2) (l : ℕ) :
    Nonempty (Doubling.Iso (Tensor2.tensor (V ℤ_[p]) (danceL p l))
      (Step36.dsumList ((VdotL p l).map (danceL p)))) :=
  tensor_danceL p hp2 l

/-- (R3): every tensor power, list form and multiplicity form. -/
theorem hTpow (hp2 : p ≠ 2) (m : ℕ) :
    Nonempty (Doubling.Iso (Filt.tpow ℤ_[p] m) (Step36.dsumList ((LL p m).map (danceL p)))) ∧
    Nonempty (Doubling.Iso (Filt.tpow ℤ_[p] m)
      (Step36.dsumList (((List.range (m + 1)).flatMap fun l =>
        List.replicate ((LL p m).count l) l).map (danceL p)))) :=
  ⟨tpow_danceL p hp2 m, tpow_danceL_mult p hp2 m⟩

/-- (R3): the lists `LL`. -/
theorem hLL (m : ℕ) : LL p 0 = [0] ∧ LL p (m + 1) = (LL p m).flatMap (VdotL p) :=
  ⟨rfl, rfl⟩

/-- (A1)–(A3): `Φ_p` and `Ψ_r` are additive and respect isomorphisms. -/
theorem hA (N N' : DPLattice ℤ_[p]) (Ls : List (DPLattice ℤ_[p]))
    (h : Nonempty (Doubling.Iso N N')) (r : ℕ) (h1 : 1 ≤ r) (h2 : r ≤ p - 1) :
    Nonempty (Doubling.Iso (twist p (Lemma35.dsum N N')) (Lemma35.dsum (twist p N) (twist p N'))) ∧
    Nonempty (Doubling.Iso (psi p (Lemma35.dsum N N') r h1 h2)
      (Lemma35.dsum (psi p N r h1 h2) (psi p N' r h1 h2))) ∧
    Nonempty (Doubling.Iso (twist p N) (twist p N')) ∧
    Nonempty (Doubling.Iso (psi p N r h1 h2) (psi p N' r h1 h2)) ∧
    Nonempty (Doubling.Iso (twist p (Step36.dsumList Ls)) (Step36.dsumList (Ls.map (twist p)))) :=
  ⟨(A1_additive p N N').1, (A1_additive p N N').2 r h1 h2, (A2_iso p h).1, (A2_iso p h).2 r h1 h2,
    (A3_dsumList p Ls).1⟩

/-- (K1), (K2): agreement with CSG5 for `m ≤ p² + p − 1`. -/
theorem hK (hp3 : 3 ≤ p) (m l : ℕ) (hm : m ≤ p ^ 2 + p - 1) :
    (LL p m).Perm (ColouredSand.TiltDec.LP p m) ∧ (LL p m).count l = ColouredSand.TiltDec.mP p l m :=
  ⟨K2_perm hp3 hm, K2_count hp3 hm l⟩

end CheckCSI6

#print axioms CheckCSI6.hL
#print axioms CheckCSI6.hRank
#print axioms CheckCSI6.hRule
#print axioms CheckCSI6.hTensor
#print axioms CheckCSI6.hTpow
#print axioms CheckCSI6.hLL
#print axioms CheckCSI6.hA
#print axioms CheckCSI6.hK
#print axioms ColouredSand.OddTwist.K1_perm
#print axioms ColouredSand.OddTwist.K3_simple
#print axioms ColouredSand.OddTwist.danceL
#print axioms ColouredSand.OddTwist.leading_digit_ne_zero
