import RequestProject.OddRulers.All

/-!
# CheckCSI13 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI13 (`CSI13_the_odd_cost_form.md`): `s_p`, `κ_p` and the two rulers
written out; Kummer; Part L (L1 Legendre and its two sums, L2, L3, L4); Part P (P1 for `i ≥ 1`
and `i = 0`; P2: support, `i ≥ 1`, the zero row and `i = 0`, each with the non-vanishing).
Then `#print axioms`.
-/

namespace CheckCSI13

open ColouredSand.OddTwist Finset

/-- The setting written out: digit sum, carries, the rulers. -/
theorem hDefs (p e k μ x a b : ℕ) (I E : Finset ℕ) (dg : ℕ → ℕ) :
    sP p x = (Nat.digits p x).sum ∧
    kappaP p a b = (((sP p a : ℤ) + sP p b) - sP p (a + b)) / ((p : ℤ) - 1) ∧
    rulerP p e k I dg μ E =
      ∑ t ∈ E, ((Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t) - kappaP p μ (oW p dg E) ∧
    rulerSharpP p e k I dg E = (if E = ∅ then 0 else
      ∑ t ∈ E, ((Rulers.h k I t : ℤ) - e * dg t * (p : ℤ) ^ t) - ((k : ℤ) - Rulers.minOr k E)) :=
  ⟨rfl, rfl, rfl, rfl⟩

variable {p : ℕ} [Fact p.Prime]

/-- Kummer: `κ_p(a, b) = v_p C(a+b, a)`. -/
theorem hKummer (a b : ℕ) : kappaP p a b = padicValNat p ((a + b).choose a) :=
  kappaP_eq_padicValNat_choose a b

/-- (L1) Legendre in base `p`, and its two sums. -/
theorem hL1 (n μ x y : ℕ) (hxy : x ≤ y) (hx : 1 ≤ x) :
    (padicValNat p n.factorial : ℚ) = ((n : ℚ) - sP p n) / ((p : ℚ) - 1) ∧
    ∑ d ∈ Ico x y, (padicValNat p (μ + 1 + d) : ℚ) =
      (((y : ℚ) - x) - sP p (μ + y) + sP p (μ + x)) / ((p : ℚ) - 1) ∧
    ∑ d ∈ Ico x y, (padicValNat p d : ℚ) =
      (((y : ℚ) - x) - sP p (y - 1) + sP p (x - 1)) / ((p : ℚ) - 1) :=
  ⟨L1_legendre n, L1_sum μ x y hxy, L1_sum_neg x y hx hxy⟩

/-- (L2). -/
theorem hL2 (dg : ℕ → ℕ) (E : Finset ℕ) (hd : ∀ t ∈ E, dg t < p) (x : ℕ) :
    (sP p (x + oW p dg E) : ℤ) =
      sP p x + ∑ t ∈ E, (dg t : ℤ) - ((p : ℤ) - 1) * kappaP p x (oW p dg E) :=
  L2 dg E hd x

/-- (L3). -/
theorem hL3 (k dk : ℕ) (I E : Finset ℕ) (dg : ℕ → ℕ) (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 0 < dg t ∧ dg t < p) (hdk1 : 1 ≤ dk) (hdk : dk ≤ p - 1)
    (hne : E.Nonempty) (hE : E ⊆ I) :
    sP p (dk * p ^ k) = dk ∧
    kappaP p (dk * p ^ k - 1) (oW p dg E) = (k : ℤ) - E.min' hne :=
  ⟨L3_sP_K k dk hdk, L3_kappa hI hd hdk1 hdk hne hE⟩

/-- (L4) = C3's `lemma_5_1_a`. -/
theorem hL4 (k : ℕ) (I a b : Finset ℕ) (hI : ∀ t ∈ I, t < k) (hba : b ⊆ a) (ha : a ⊆ I) :
    ((a \ b).card : ℤ) + Rulers.delta k (a \ b) =
      ∑ t ∈ a, (Rulers.h k I t : ℤ) - ∑ t ∈ b, (Rulers.h k I t : ℤ) +
        Rulers.gamma k I (a \ b) :=
  L4 hI hba ha

/-- (P1), `i ≥ 1`. -/
theorem hP1 (k dk e i : ℕ) (I a b : Finset ℕ) (dg : ℕ → ℕ) (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 0 < dg t ∧ dg t < p) (hdk1 : 1 ≤ dk) (hdk : dk ≤ p - 1)
    (hba : b ⊆ a) (ha : a ⊆ I) (hi : 1 ≤ i) :
    -(dk : ℤ) * (((p ^ k - 1) / (p - 1) : ℕ) : ℤ) +
        ∑ t ∈ a \ b, (1 + (dg t : ℤ) * (((p ^ t - 1) / (p - 1) : ℕ) : ℤ)) +
        Rulers.delta k (a \ b) + e * (((dk * p ^ k : ℕ) : ℤ) - oW p dg (a \ b)) +
        ∑ d ∈ Ico (oW p dg a) (oW p dg b + dk * p ^ k), (padicValNat p (i + d) : ℤ) =
      e * ((dk * p ^ k : ℕ) : ℤ) + kappaP p (i - 1) (dk * p ^ k) + rulerP p e k I dg (i - 1) a -
        rulerP p e k I dg (i - 1 + dk * p ^ k) b + Rulers.gamma k I (a \ b) :=
  oddRul_P1 hI hd hdk1 hdk hba ha e i hi

/-- (P1), `i = 0`, `a ≠ ∅`. -/
theorem hP1zero (k dk e : ℕ) (I a b : Finset ℕ) (dg : ℕ → ℕ) (hI : ∀ t ∈ I, t < k)
    (hd : ∀ t ∈ I, 0 < dg t ∧ dg t < p) (hdk1 : 1 ≤ dk) (hdk : dk ≤ p - 1)
    (hba : b ⊆ a) (ha : a ⊆ I) (hne : a.Nonempty) :
    -(dk : ℤ) * (((p ^ k - 1) / (p - 1) : ℕ) : ℤ) +
        ∑ t ∈ a \ b, (1 + (dg t : ℤ) * (((p ^ t - 1) / (p - 1) : ℕ) : ℤ)) +
        Rulers.delta k (a \ b) + e * (((dk * p ^ k : ℕ) : ℤ) - oW p dg (a \ b)) +
        ∑ d ∈ Ico (oW p dg a) (oW p dg b + dk * p ^ k), (padicValNat p d : ℤ) =
      e * ((dk * p ^ k : ℕ) : ℤ) + rulerSharpP p e k I dg a - rulerSharpP p e k I dg b +
        Rulers.gamma k I (a \ b) :=
  P1_zero hI hd hdk1 hdk hba ha hne e

/-- (P2): support, `i ≥ 1`, zero row, `i = 0`. -/
theorem hP2 (hodd : Odd p) (l i e : ℕ) (he : 1 ≤ e) (hi : 1 ≤ i) (x y : slots p l i e)
    (x0 y0 : slots p l 0 e) :
    (¬ labL p l i e (kTop p l) y ⊆ labL p l i e (kTop p l) x → Mp p l i e x y = 0) ∧
    (labL p l i e (kTop p l) y ⊆ labL p l i e (kTop p l) x →
      Mp p l i e x y ≠ 0 ∧
      ((Mp p l i e x y).valuation : ℤ) =
        e * ((digitL p l (kTop p l) * p ^ kTop p l : ℕ) : ℤ) +
          kappaP p (i - 1) (digitL p l (kTop p l) * p ^ kTop p l) +
          rulerP p e (kTop p l) (Iset p l) (digitL p l) (i - 1) (labL p l i e (kTop p l) x) -
          rulerP p e (kTop p l) (Iset p l) (digitL p l)
            (i - 1 + digitL p l (kTop p l) * p ^ kTop p l) (labL p l i e (kTop p l) y) +
          Rulers.gamma (kTop p l) (Iset p l)
            (labL p l i e (kTop p l) x \ labL p l i e (kTop p l) y)) ∧
    (labL p l 0 e (kTop p l) x0 = ∅ → Mp p l 0 e x0 y0 = 0) ∧
    (labL p l 0 e (kTop p l) x0 ≠ ∅ →
      labL p l 0 e (kTop p l) y0 ⊆ labL p l 0 e (kTop p l) x0 →
      Mp p l 0 e x0 y0 ≠ 0 ∧
      ((Mp p l 0 e x0 y0).valuation : ℤ) =
        e * ((digitL p l (kTop p l) * p ^ kTop p l : ℕ) : ℤ) +
          rulerSharpP p e (kTop p l) (Iset p l) (digitL p l) (labL p l 0 e (kTop p l) x0) -
          rulerSharpP p e (kTop p l) (Iset p l) (digitL p l) (labL p l 0 e (kTop p l) y0) +
          Rulers.gamma (kTop p l) (Iset p l)
            (labL p l 0 e (kTop p l) x0 \ labL p l 0 e (kTop p l) y0)) :=
  ⟨P2_support p l i e he x y, P2_pos p hodd l i e he hi x y, P2_zero_row p l e he x0 y0,
    fun hx hba => P2_zero p hodd l e he x0 y0 hx hba⟩

end CheckCSI13

#print axioms CheckCSI13.hDefs
#print axioms CheckCSI13.hKummer
#print axioms CheckCSI13.hL1
#print axioms CheckCSI13.hL2
#print axioms CheckCSI13.hL3
#print axioms CheckCSI13.hL4
#print axioms CheckCSI13.hP1
#print axioms CheckCSI13.hP1zero
#print axioms CheckCSI13.hP2
