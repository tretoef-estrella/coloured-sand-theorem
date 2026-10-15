import RequestProject.TiltDec.All

/-!
# CheckCSG5 (Grepy Sand, 13 Oct 2026)

Hand restatement of CSG5 (`CSG5_the_induction.md`): the rule (M1) written case by case with every
weight by hand, the recursion (M2), the number β written by hand with `Nat.choose`, and the
statements (D1), (D2), (D3), (W2), (W3), (W4), (W5) checked against the certified theorems of
`ColouredSand.TiltDec`. Then `#print axioms`.
-/

namespace CheckCSG5

open DPLattice WeylFilt Doubling Lemma35 Filt Step36 ColouredSand.Glue ColouredSand.Blocks
  ColouredSand.TiltP ColouredSand.TiltRules ColouredSand.TiltDec

/-- β by hand: `C(n,k) − C(n,k−1)`, `k = (n − l)/2`, if `l ≤ n` and `l ≡ n (mod 2)`; else `0`. -/
def hBeta (n l : ℕ) : ℤ :=
  if l ≤ n ∧ l % 2 = n % 2 then
    (Nat.choose n ((n - l) / 2) : ℤ) -
      (if (n - l) / 2 = 0 then 0 else (Nat.choose n ((n - l) / 2 - 1) : ℤ))
  else 0

example (n l : ℕ) : betaCG n l = hBeta n l := rfl
example : hBeta 6 2 = 9 := by decide
example : hBeta 6 0 = 5 := by decide
example : hBeta 6 6 = 1 := by decide
example : hBeta 6 3 = 0 := by decide

/-- (M1) by hand, case by case (`r = (l − p) % p + 1`, `a = (l − p) / p`, `μ = l − 2r`). -/
theorem hM1 (p : ℕ) (hp : 3 ≤ p) :
    VdotP p 0 = [1] ∧
    (∀ l, IsSimpleWt p l → 1 ≤ l → l ≤ p - 2 → VdotP p l = [l + 1, l - 1]) ∧
    (∀ l, IsSimpleWt p l → p - 1 ≤ l → VdotP p l = [l + 1]) ∧
    (∀ l, ¬ IsSimpleWt p l → (l - p) % p + 1 = 1 → VdotP p l = [l + 1, l - 1, l - 1]) ∧
    (∀ l, ¬ IsSimpleWt p l → 2 ≤ (l - p) % p + 1 → (l - p) % p + 1 ≤ p - 2 →
      VdotP p l = [l + 1, l - 1]) ∧
    (∀ l, ¬ IsSimpleWt p l → (l - p) % p + 1 = p - 1 → 1 ≤ (l - p) / p → (l - p) / p ≤ p - 2 →
      VdotP p l = [l + 1, l - 1, l - 2 * ((l - p) % p + 1) - 1]) ∧
    (∀ l, ¬ IsSimpleWt p l → (l - p) % p + 1 = p - 1 → ((l - p) / p = 0 ∨ (l - p) / p = p - 1) →
      VdotP p l = [l + 1, l - 1]) :=
  ⟨VdotP_zero p, fun _ hs h1 h2 => VdotP_simple_small hs h1 h2,
    fun _ hs h => VdotP_simple_large (by omega) hs h, fun _ hs hr => VdotP_r_one hs hr,
    fun _ hs h1 h2 => VdotP_r_mid hs h1 h2, fun _ hs hr h1 h2 => VdotP_r_top_pos hp hs hr h1 h2,
    fun _ hs hr ha => VdotP_r_top_ext hp hs hr ha⟩

/-- (M2) and (M3) by hand. -/
theorem hM23 (p : ℕ) (hp : 2 ≤ p) :
    LP p 0 = [0] ∧ (∀ n, LP p (n + 1) = (LP p n).flatMap (VdotP p)) ∧
    (∀ n lam, mP p lam n = (LP p n).count lam) ∧
    (∀ n, ∀ lam ∈ LP p n, lam ≤ n ∧ lam % 2 = n % 2) :=
  ⟨rfl, fun _ => rfl, fun _ _ => rfl, fun n => M3 hp n⟩

/-- (D1), (D2), (D3) by hand. -/
theorem hD (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (∀ l, l ≤ p ^ 2 + p - 2 →
      Nonempty (Iso (tensorV (Ttilt p l)) (dsumList ((VdotP p l).map (Ttilt p))))) ∧
    (∀ n, n ≤ p ^ 2 + p - 1 →
      Nonempty (Iso (tpow ℤ_[p] n) (dsumList ((LP p n).map (Ttilt p))))) ∧
    (∀ n, n ≤ p ^ 2 + p - 1 →
      Nonempty (Iso (tpow ℤ_[p] n) (dsumList ((List.range (n + 1)).flatMap
        (fun lam => List.replicate ((LP p n).count lam) (Ttilt p lam)))))) :=
  ⟨fun _ h => D1 hp2 h, fun _ h => D2 hp2 h, fun _ h => D3 hp2 h⟩

/-- (W2)–(W5) by hand. -/
theorem hW (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp : 3 ≤ p) :
    (∀ n, n ≤ p ^ 2 + p - 1 → ((LP p n).flatMap (weylP p)).Perm (CG n)) ∧
    (∀ n l, ((CG n).count l : ℤ) = hBeta n l) ∧
    (∀ n l m, n ≤ p ^ 2 + p - 1 → ¬ IsSimpleWt p m → m ≤ n → m - 2 * ((m - p) % p + 1) = l →
      ((LP p n).count l : ℤ) + (LP p n).count m = hBeta n l) ∧
    (∀ n l, n ≤ p ^ 2 + p - 1 →
      (∀ m ≤ n, ¬ IsSimpleWt p m → m - 2 * ((m - p) % p + 1) ≠ l) →
      ((LP p n).count l : ℤ) = hBeta n l) ∧
    (∀ m₁ m₂, ¬ IsSimpleWt p m₁ → ¬ IsSimpleWt p m₂ → m₁ ≤ p ^ 2 + p - 1 → m₂ ≤ p ^ 2 + p - 1 →
      m₁ - 2 * ((m₁ - p) % p + 1) = m₂ - 2 * ((m₂ - p) % p + 1) → m₁ = m₂) ∧
    (∀ n, n ≤ p ^ 2 + p - 1 →
      ((LP p n).map (fun lam => Fintype.card (Ttilt p lam).ι)).sum = 2 ^ n) :=
  ⟨fun _ h => W2 hp h, W3, fun _ _ _ h hs hmn hm => W4_of_plus hp h hs hmn hm,
    fun _ _ h hh => W4_of_no_plus hp h hh,
    fun _ _ h1 h2 h3 h4 h5 => W4_inj (by omega) h1 h2 h3 h4 h5, fun _ h => W5_card hp2 h⟩

end CheckCSG5

#print axioms CheckCSG5.hM1
#print axioms CheckCSG5.hM23
#print axioms CheckCSG5.hD
#print axioms CheckCSG5.hW
#print axioms ColouredSand.TiltDec.D1
#print axioms ColouredSand.TiltDec.D2
#print axioms ColouredSand.TiltDec.D3
#print axioms ColouredSand.TiltDec.W2
#print axioms ColouredSand.TiltDec.W3
#print axioms ColouredSand.TiltDec.W4
#print axioms ColouredSand.TiltDec.W4_inj
#print axioms ColouredSand.TiltDec.W5
#print axioms ColouredSand.TiltDec.W5_card
#print axioms ColouredSand.TiltDec.M3
