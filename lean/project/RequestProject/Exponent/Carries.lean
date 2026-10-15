module

public import Mathlib

/-!
# (C3) Lemma 5: carries

This file corresponds to **(C3) Lemma 5, carries** of `CS4_theorem_C_exponent.md`.

## Encoding

* `v_p` is `padicValNat p`, `C(b, L)` is `Nat.choose b L` and `⌊log_p d⌋` is `Nat.log p d`.
* `carryTerm p e L b = e L + v_p(L) + v_p C(b, L)`.
* A maximum over a finite set of natural numbers is `Finset.sup` (which is `0` on the empty set,
  so the statements also make sense, and hold, for `d = 0`).  The index set
  `{(L, b) : 1 ≤ L ≤ b ≤ d}` is `carryPairs d`.

## Results

* `vp_add_vp_choose_le_log` (the Kummer bound): `v_p(L) + v_p C(b, L) ≤ ⌊log_p b⌋`.
* `lemma5`: `max_{1 ≤ L ≤ b ≤ d} (e L + v_p(L) + v_p C(b,L)) = max_{1 ≤ s ≤ d} (e s + v_p(s))`.
  The file assumes `e ≥ 1`; the proof below works for every `e` (more general).
* `lemma5_zero`: for `e = 0` the left side equals `⌊log_p d⌋`.

## Proof

As in the file.  The Kummer bound uses Mathlib's `padicValNat_choose` (Kummer's theorem: the
valuation is the number of `i ≥ 1` with `p^i ≤ L mod p^i + (b − L) mod p^i`).  The upper bound is
by strong induction on `b`, with `λ = ⌊log_p b⌋` and `s* = p^λ ⌊b / p^λ⌋`.
-/

@[expose] public section

open Finset

namespace ColouredSand.Exponent

/-- `e L + v_p(L) + v_p C(b, L)`, the quantity maximised in Lemma 5. -/
def carryTerm (p e L b : ℕ) : ℕ := e * L + padicValNat p L + padicValNat p (b.choose L)

/-- The index set `{(L, b) : 1 ≤ L ≤ b ≤ d}` of Lemma 5. -/
def carryPairs (d : ℕ) : Finset (ℕ × ℕ) := (Icc 1 d ×ˢ Icc 1 d).filter fun x => x.1 ≤ x.2

lemma mem_carryPairs {d : ℕ} {x : ℕ × ℕ} : x ∈ carryPairs d ↔ 1 ≤ x.1 ∧ x.1 ≤ x.2 ∧ x.2 ≤ d := by
  simp only [carryPairs, mem_filter, mem_product, mem_Icc]
  omega

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The Kummer bound.**  For `1 ≤ L ≤ b`, `v_p(L) + v_p C(b, L) ≤ ⌊log_p b⌋`. -/
theorem vp_add_vp_choose_le_log {L b : ℕ} (hL : 1 ≤ L) (hLb : L ≤ b) :
    padicValNat p L + padicValNat p (b.choose L) ≤ Nat.log p b := by
  set a := padicValNat p L
  set lam := Nat.log p b
  have ha : a ≤ lam :=
    Nat.le_log_of_pow_le hp.out.one_lt ((Nat.le_of_dvd (by omega) pow_padicValNat_dvd).trans hLb)
  rw [padicValNat_choose (b := lam + 1) hLb (Nat.lt_succ_self _)]
  have hsub : {i ∈ Ico 1 (lam + 1) | p ^ i ≤ L % p ^ i + (b - L) % p ^ i} ⊆ Ico (a + 1) (lam + 1) := by
    intro i hi
    simp only [mem_filter, mem_Ico] at hi ⊢
    refine ⟨?_, hi.1.2⟩
    by_contra hia
    have hdvd : p ^ i ∣ L := (pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd
    rw [Nat.mod_eq_zero_of_dvd hdvd, zero_add] at hi
    exact absurd hi.2 (not_le.mpr (Nat.mod_lt _ (pow_pos hp.out.pos i)))
  have := card_le_card hsub
  rw [Nat.card_Ico] at this
  omega

/-- If `p^λ` divides `x` and `1 ≤ y < p^λ`, then `v_p(x + y) = v_p(y)`. -/
lemma vp_add_of_lt {x y lam : ℕ} (hx : p ^ lam ∣ x) (hy : 1 ≤ y) (hyl : y < p ^ lam) :
    padicValNat p (x + y) = padicValNat p y := by
  have hv : padicValNat p y < lam := by
    by_contra h
    exact absurd ((Nat.le_of_dvd (by omega) pow_padicValNat_dvd).trans_lt hyl)
      (not_lt.mpr (Nat.pow_le_pow_right hp.out.pos (not_lt.mp h)))
  apply le_antisymm
  · by_contra h
    have h1 : p ^ (padicValNat p y + 1) ∣ x + y :=
      (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
    have h2 : p ^ (padicValNat p y + 1) ∣ x := (pow_dvd_pow p (by omega)).trans hx
    have h3 : p ^ (padicValNat p y + 1) ∣ y := (Nat.dvd_add_right h2).mp h1
    have := (padicValNat_dvd_iff_le (p := p) (by omega)).mp h3
    omega
  · have h2 : p ^ padicValNat p y ∣ x := (pow_dvd_pow p hv.le).trans hx
    exact (padicValNat_dvd_iff_le (by omega)).mp (dvd_add h2 pow_padicValNat_dvd)

/-- The upper bound of Lemma 5 for a single pair: for `1 ≤ L ≤ b` there is `1 ≤ s ≤ b` with
`e L + v_p(L) + v_p C(b,L) ≤ e s + v_p(s)`. -/
theorem carryTerm_le_exists (e : ℕ) :
    ∀ b L : ℕ, 1 ≤ L → L ≤ b → ∃ s, 1 ≤ s ∧ s ≤ b ∧ carryTerm p e L b ≤ e * s + padicValNat p s := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
  intro L hL hLb
  have hb0 : b ≠ 0 := by omega
  set lam := Nat.log p b
  set P := p ^ lam with hP
  have hPpos : 0 < P := pow_pos hp.out.pos _
  have hPb : P ≤ b := Nat.pow_log_le_self p hb0
  have hbP : b < p * P := by
    have := Nat.lt_pow_succ_log_self hp.out.one_lt b
    rwa [pow_succ, mul_comm] at this
  set s := P * (b / P) with hs
  have hq1 : 1 ≤ b / P := (Nat.one_le_div_iff hPpos).mpr hPb
  have hsb : s ≤ b := Nat.mul_div_le b P
  have hs1 : P ≤ s := Nat.le_mul_of_pos_right P hq1
  have hvs : lam ≤ padicValNat p s := by
    rw [hs, padicValNat.mul (by positivity) (by omega), hP, padicValNat.prime_pow]
    omega
  set r := b % P with hr
  have hbr : b = s + r := (Nat.div_add_mod b P).symm
  have hrP : r < P := Nat.mod_lt _ hPpos
  by_cases hLs : L ≤ s
  · refine ⟨s, by omega, hsb, ?_⟩
    have := vp_add_vp_choose_le_log (p := p) hL hLb
    unfold carryTerm
    have : e * L ≤ e * s := Nat.mul_le_mul_left e hLs
    omega
  · -- `L = s + r'` with `1 ≤ r' ≤ r < P`
    set r' := L - s with hr'
    have hLr : L = s + r' := by omega
    have hr'1 : 1 ≤ r' := by omega
    have hr'r : r' ≤ r := by omega
    obtain ⟨t, ht1, htr, ht⟩ := ih r (by omega) r' hr'1 hr'r
    have hPs : P ∣ s := Dvd.intro _ rfl
    refine ⟨s + t, by omega, by omega, ?_⟩
    have hvL : padicValNat p L = padicValNat p r' := by
      rw [hLr]; exact vp_add_of_lt hPs hr'1 (by omega)
    have hvt : padicValNat p (s + t) = padicValNat p t := vp_add_of_lt hPs ht1 (by omega)
    have hch : padicValNat p (b.choose L) = padicValNat p (r.choose r') := by
      have hlogr : Nat.log p r < lam + 1 :=
        Nat.lt_succ_of_le (Nat.log_mono_right (by omega))
      rw [padicValNat_choose (b := lam + 1) hLb (Nat.lt_succ_self _),
        padicValNat_choose (b := lam + 1) hr'r hlogr]
      congr 1
      refine filter_congr fun i hi => ?_
      rw [mem_Ico] at hi
      have hdi : p ^ i ∣ s := (pow_dvd_pow p (by omega)).trans hPs
      have h1 : L % p ^ i = r' % p ^ i := by
        rw [hLr, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdi, zero_add, Nat.mod_mod]
      have h2 : b - L = r - r' := by omega
      rw [h1, h2]
    unfold carryTerm at ht ⊢
    rw [hvL, hch, hvt, hLr, mul_add, mul_add]
    omega

/-- **(C3) Lemma 5, carries.**  For a prime `p` and integers `d`, `e`:
`max_{1 ≤ L ≤ b ≤ d} (e L + v_p(L) + v_p C(b,L)) = max_{1 ≤ s ≤ d} (e s + v_p(s))`.

The file states this for `d ≥ 1` and `e ≥ 1`; it holds for all `d, e ≥ 0` (maxima over the empty
set being `0`), which is more general. -/
theorem lemma5 (p : ℕ) [Fact p.Prime] (d e : ℕ) :
    (carryPairs d).sup (fun x => e * x.1 + padicValNat p x.1 + padicValNat p (x.2.choose x.1)) =
      (Icc 1 d).sup (fun s => e * s + padicValNat p s) := by
  apply le_antisymm
  · refine Finset.sup_le fun x hx => ?_
    rw [mem_carryPairs] at hx
    obtain ⟨s, hs1, hsb, hle⟩ := carryTerm_le_exists (p := p) e x.2 x.1 hx.1 hx.2.1
    exact hle.trans (le_sup (f := fun s => e * s + padicValNat p s)
      (mem_Icc.mpr ⟨hs1, hsb.trans hx.2.2⟩))
  · refine Finset.sup_le fun s hs => ?_
    rw [mem_Icc] at hs
    have := le_sup (f := fun x : ℕ × ℕ => e * x.1 + padicValNat p x.1 +
      padicValNat p (x.2.choose x.1)) (mem_carryPairs.mpr (show 1 ≤ (s, s).1 ∧ (s, s).1 ≤ (s, s).2 ∧
        (s, s).2 ≤ d from ⟨hs.1, le_rfl, hs.2⟩))
    simpa using this

/-- `max_{1 ≤ s ≤ d} v_p(s) = ⌊log_p d⌋`. -/
lemma sup_vp_eq_log (p : ℕ) [Fact p.Prime] (d : ℕ) :
    (Icc 1 d).sup (fun s => padicValNat p s) = Nat.log p d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  apply le_antisymm
  · refine Finset.sup_le fun s hs => ?_
    rw [mem_Icc] at hs
    exact Nat.le_log_of_pow_le (Fact.out : p.Prime).one_lt
      ((Nat.le_of_dvd (by omega) pow_padicValNat_dvd).trans hs.2)
  · have hmem : p ^ Nat.log p d ∈ Icc 1 d :=
      mem_Icc.mpr ⟨Nat.one_le_pow _ _ (Fact.out : p.Prime).pos, Nat.pow_log_le_self p hd.ne'⟩
    have := le_sup (f := fun s => padicValNat p s) hmem
    simpa [padicValNat.prime_pow] using this

/-- **(C3) Lemma 5, case `e = 0`.**  `max_{1 ≤ L ≤ b ≤ d} (v_p(L) + v_p C(b,L)) = ⌊log_p d⌋`
(for every `d`; the file assumes `d ≥ 1`). -/
theorem lemma5_zero (p : ℕ) [Fact p.Prime] (d : ℕ) :
    (carryPairs d).sup (fun x => 0 * x.1 + padicValNat p x.1 + padicValNat p (x.2.choose x.1)) =
      Nat.log p d := by
  rw [lemma5, ← sup_vp_eq_log]
  simp

end ColouredSand.Exponent
