import RequestProject.OddWindows.All

/-!
# CheckCSI12 (Grepy Ship, 14 Oct 2026)

Hand restatement of CSI12 (`CSI12_the_odd_windows.md`): `o_D`, `π_0`, `b_h`, `x_h·f` and the
coefficients `c^{(h)}` (Part C) written out; the slot labels (A side keeps, C side adds `h`) and the
bijection with the subsets of `I ∩ [0, h)` with its three clauses written out; (W1) and (W2) with
the windows written out, and (W2) for any number `s ≥ 1` of factors; (C1) for digit lists and for
the digits of `λ + 1`. Then `#print axioms`.
-/

namespace CheckCSI12

open ColouredSand.OddTwist Finset

/-- The setting and Part C written out. -/
theorem hDefs (p e i d h : ℕ) (dg : ℕ → ℕ) (I D Δ : Finset ℕ) (f : Finset ℕ → ℚ) :
    oW p dg D = ∑ t ∈ D, dg t * p ^ t ∧
    piW p e i d = (p : ℚ) ^ e * ((i : ℚ) + d) ∧
    bW p dg h = (-1) ^ (p - dg h + 1) ∧
    xMul h f Δ = (if h ∈ Δ then f (Δ \ {h}) else 0) ∧
    cW p I dg 0 Δ = (if Δ = ∅ then 1 else 0) ∧
    cW p I dg (h + 1) Δ = (-1 / (p : ℚ)) * starPow (cW p I dg h) p Δ +
      (if h ∈ I then 1 else 0) * ((-1) ^ (p - dg h + 1)) *
        (if h ∈ Δ then starPow (cW p I dg h) (p - dg h) (Δ \ {h}) else 0) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The labels: start at `∅`; a zero digit keeps the label; at a split, `(s, false)` (A side)
keeps the label of `s`, `(s, true)` (C side) adds `h`. -/
theorem hLab {A : Type*} [CommRing A] (p : ℕ) (dg : ℕ → ℕ) (D₀ : SData A) (h : ℕ) :
    (∀ x, slotLab p dg D₀ 0 x = ∅) ∧
    (∀ (hd : dg h = 0) (x : (iterD p dg (h + 1) D₀).S), slotLab p dg D₀ (h + 1) x =
      slotLab p dg D₀ h (cast (stepD_S_zero p _ hd (iterD p dg h D₀)) x)) ∧
    (∀ (hd : dg h ≠ 0) (x : (iterD p dg (h + 1) D₀).S), slotLab p dg D₀ (h + 1) x =
      (if (cast (stepD_S_pos p _ hd (iterD p dg h D₀)) x).2 then
        insert h (slotLab p dg D₀ h (cast (stepD_S_pos p _ hd (iterD p dg h D₀)) x).1)
      else slotLab p dg D₀ h (cast (stepD_S_pos p _ hd (iterD p dg h D₀)) x).1)) :=
  ⟨fun _ => rfl, fun hd x => slotLab_succ_zero p dg D₀ h hd x,
    fun hd x => slotLab_succ_pos p dg D₀ h hd x⟩

variable (p : ℕ) [hp : Fact p.Prime]

/-- Slots as subsets, the three clauses written out. -/
theorem hSlots (l i e h : ℕ) (hh : h ≤ kTop p l) :
    labL p l i e h = slotLab p (digitL p l) ⟨Unit, Q0 ℤ_[p] p e i⟩ h ∧
    (∀ x, labL p l i e h x ⊆ (Iset p l).filter (· < h)) ∧
    Function.Injective (labL p l i e h) ∧
    (∀ E ⊆ (Iset p l).filter (· < h), ∃ x, labL p l i e h x = E) :=
  let H := slots_as_subsets p l i e h hh
  ⟨rfl, H.sub, H.inj, H.surj⟩

/-- **(W1)** written out. -/
theorem hW1 (l i e h : ℕ) (he : 1 ≤ e) (hh : h ≤ kTop p l) (f : ℕ)
    (x y : (Qdata p l i e h).S) :
    (((p : ℤ_[p]) * (Qdata p l i e h).Q f x y : ℤ_[p]) : ℚ_[p]) =
      ((if labL p l i e h y ⊆ labL p l i e h x then
          cW p (Iset p l) (digitL p l) h (labL p l i e h x \ labL p l i e h y) *
            ∏ d ∈ Icc (p ^ h * f + ∑ t ∈ labL p l i e h x, digitL p l t * p ^ t)
              (p ^ h * f + ∑ t ∈ labL p l i e h y, digitL p l t * p ^ t + p ^ h - 1),
              (p : ℚ) ^ e * ((i : ℚ) + d)
        else 0 : ℚ) : ℚ_[p]) := by
  have := W1_windows p l i e h he hh f x y
  simpa [Matrix.smul_apply, smul_eq_mul, oW, piW] using this

/-- **(W2)** written out (`K = d_k p^k`). -/
theorem hW2 (l i e : ℕ) (he : 1 ≤ e) (x y : slots p l i e) :
    (Mp p l i e x y : ℚ_[p]) =
      ((if labL p l i e (kTop p l) y ⊆ labL p l i e (kTop p l) x then
          starPow (cW p (Iset p l) (digitL p l) (kTop p l)) (digitL p l (kTop p l))
              (labL p l i e (kTop p l) x \ labL p l i e (kTop p l) y) *
            ∏ d ∈ Icc (∑ t ∈ labL p l i e (kTop p l) x, digitL p l t * p ^ t)
              (∑ t ∈ labL p l i e (kTop p l) y, digitL p l t * p ^ t +
                digitL p l (kTop p l) * p ^ kTop p l - 1), (p : ℚ) ^ e * ((i : ℚ) + d)
        else 0 : ℚ) : ℚ_[p]) :=
  W2_Mp p l i e he x y

/-- **(W2)** for any level `h ≤ k` and any number `s ≥ 1` of factors. -/
theorem hW2s (l i e h s : ℕ) (he : 1 ≤ e) (hh : h ≤ kTop p l) (hs : 1 ≤ s)
    (x y : (Qdata p l i e h).S) :
    ((((p : ℤ_[p]) ^ s • prodQ (Qdata p l i e h).Q 0 s) x y : ℤ_[p]) : ℚ_[p]) =
      ((if labL p l i e h y ⊆ labL p l i e h x then
          starPow (cW p (Iset p l) (digitL p l) h) s (labL p l i e h x \ labL p l i e h y) *
            ∏ d ∈ Icc (oW p (digitL p l) (labL p l i e h x))
              (oW p (digitL p l) (labL p l i e h y) + s * p ^ h - 1), piW p e i d
        else 0 : ℚ) : ℚ_[p]) :=
  W2_gen PadicInt.Coe.ringHom p (digitL p l) (Iset p l) e i hp.out.two_le he h
    (fun t _ => digitL_lt hp.out l t) (fun t ht => mem_Iset_iff p l t (by omega)) s hs x y

end CheckCSI12

namespace CheckCSI12

open ColouredSand.OddTwist Finset

/-- **(C1)** for digit lists (CSI11's `ds`, `I = Iod ds`). -/
theorem hC1 {p : ℕ} (hp : 2 ≤ p) (ds : List ℕ) (hds : ∀ d ∈ ds, d < p) (h : ℕ) (Δ : Finset ℕ) :
    cW p (Iod ds) (fun t => ds.getD t 0) h Δ =
      (-1 / (p : ℚ)) ^ ((p ^ h - 1) / (p - 1)) * (aP p ds h Δ : ℚ) *
        ∏ t ∈ Δ, (-((-1 : ℚ) ^ (p - ds.getD t 0 + 1)) *
          (-(p : ℚ)) ^ (1 + ds.getD t 0 * ((p ^ t - 1) / (p - 1)))) :=
  C1_rescaling hp ds hds h Δ

/-- **(C1)** for the digits of `λ + 1`. -/
theorem hC1lam {p : ℕ} (hp : p.Prime) (l h : ℕ) (Δ : Finset ℕ) :
    cW p (Iset p l) (digitL p l) h Δ =
      (-1 / (p : ℚ)) ^ ((p ^ h - 1) / (p - 1)) * (aP p (dsL p l) h Δ : ℚ) *
        ∏ t ∈ Δ, (-((-1 : ℚ) ^ (p - digitL p l t + 1)) *
          (-(p : ℚ)) ^ (1 + digitL p l t * ((p ^ t - 1) / (p - 1)))) :=
  C1_lambda hp l h Δ

end CheckCSI12

#print axioms CheckCSI12.hDefs
#print axioms CheckCSI12.hLab
#print axioms CheckCSI12.hSlots
#print axioms CheckCSI12.hW1
#print axioms CheckCSI12.hW2
#print axioms CheckCSI12.hW2s
#print axioms CheckCSI12.hC1
#print axioms CheckCSI12.hC1lam
#print axioms ColouredSand.OddTwist.W1_gen
#print axioms ColouredSand.OddTwist.W2_gen
