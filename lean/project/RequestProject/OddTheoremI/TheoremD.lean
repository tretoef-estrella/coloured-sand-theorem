module

public import RequestProject.OddTheoremI.Reindex
public import RequestProject.OddTheoremI.Digits
public import RequestProject.OddLevels.All
public import RequestProject.OddPayment.TheoremA
public import RequestProject.OddSplitMove.TheoremM

/-!
# `CSI10_theorem_Dp_and_theorem_I.md`, Part D — Theorem D_p

Namespace `ColouredSand.OddTwist`. Assembles CSI6 (`danceL`, its rank), CSI7 (`corollary_Ap2`),
CSI8 (`corollary_M2`) and CSI9 (`G2_twist`, `G2_psi`, `G3_operator`, `L1`, `G1_delta`).

## Encodings

* `p` is an odd prime: `[Fact p.Prime]` and `hp : Odd p`.
* `Zq p a = ℤ_[p] ⧸ Ideal.span {p^a}` is the cyclic module `ℤ_[p] ⧸ p^a`.
* `σ = sigmaOp p λ e i = Fd 1 + p^e • (D_fl + i)` on `(danceL p λ).ι → ℤ_[p]` (CSI9 (G3), with
  `D_fl = Dop (flL p λ)`), and `Yp p λ i e = ((danceL p λ).ι → ℤ_[p]) ⧸ range σ` is `Y_p(λ, i, e)`.
* The product `Π_{t=1}^{k−1} (Fin n_t → ℤ_[p] ⧸ p^t)` is the dependent function type
  `(t : Fin (k − 1)) → Fin n_{t+1} → Zq p (t + 1)` (the index `t : Fin (k−1)` stands for the paper's
  `t + 1 ∈ [1, k−1]`).
* "`p^k • Mp` acting as in CSI7" is, with CSI9 (L1)'s convention, `(p : ℤ_[p])^k • (Mp p λ i e).mulVecLin`
  on `slots p λ i e → ℤ_[p]` (column vectors, `v ↦ M v`).

## Proof

`theorem_D_gen` is the induction on the digits, for an arbitrary starting slot type with data
`D : SData ℤ_[p]` and an arbitrary starting scalar `c = p^h`: at level `t` the factor is
`Fin (cntT p λ t · |S|) → Zq p (h + t)`, where `cntT p λ t = (p−1) d_k p^{k−t−1} 2^{|I|}`; the last
torsion factor is `Fin (lastCnt p λ · |S|) → Zq p (h + k)` with `lastCnt p λ = (d_k − 1) 2^{|I|}`;
and the final data is `finD p λ D` (the moves of all the digits `d_0, …, d_{k−1}` applied to `D`).
Each step reindexes the system along `eTw`/`ePsi` (CSI9 (G2)), applies `corollary_Ap2` resp.
`corollary_M2` with `c = p^h`, counts the factor `Sys/p^h` with CSI6's rank, and recurses on
`b = (λ+1)/p − 1` with `h + 1`. The base `λ + 1 < p` is CSI9 (L1) (through `idxDelta`, `G1_delta`).
Theorem D_p (`theorem_Dp`) is the case `D = (Unit, Q_0)`, `h = 0`, through CSI9 (G3); its level `0`
factor is `ℤ_[p] ⧸ p^0 = 0`.
-/

@[expose] public section

noncomputable section

namespace ColouredSand.OddTwist

open DirectSum DPLattice
open scoped Pointwise

variable (p : ℕ) [Fact p.Prime]

/-- The cyclic module `ℤ_[p] ⧸ p^a` (Part D of `CSI10_theorem_Dp_and_theorem_I.md`). -/
abbrev Zq (a : ℕ) : Type := ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ a}

/-- The operator `σ = Fd 1 + p^e • (D_fl + i)` on `danceL p λ` (Setting of
`CSI10_theorem_Dp_and_theorem_I.md`, CSI9 (G3)). -/
abbrev sigmaOp (l e i : ℕ) : Module.End ℤ_[p] ((danceL p l).ι → ℤ_[p]) :=
  (danceL p l).Fd 1 + (p : ℤ_[p]) ^ e •
    (Dop (flL p l) + (i : ℤ_[p]) • (1 : Module.End ℤ_[p] ((danceL p l).ι → ℤ_[p])))

/-- **`Y_p(λ, i, e)`**, the cokernel of `σ` on `danceL p λ` (Setting of
`CSI10_theorem_Dp_and_theorem_I.md`). -/
abbrev Yp (l i e : ℕ) : Type := ((danceL p l).ι → ℤ_[p]) ⧸ LinearMap.range (sigmaOp p l e i)

/-- The number of copies at level `t`: `(p−1) d_k p^{k−t−1} 2^{|I|}` (Part D of
`CSI10_theorem_Dp_and_theorem_I.md`). -/
def cntT (l t : ℕ) : ℕ := (p - 1) * digitL p l (kTop p l) * p ^ (kTop p l - t - 1) * 2 ^ (Iset p l).card

/-- The number of copies of `ℤ_[p] ⧸ p^k`: `(d_k − 1) 2^{|I|}` (Part D of
`CSI10_theorem_Dp_and_theorem_I.md`). -/
def lastCnt (l : ℕ) : ℕ := (digitL p l (kTop p l) - 1) * 2 ^ (Iset p l).card

/-- The data after the moves of all the digits `d_0, …, d_{k−1}` of `λ + 1` (Part D of
`CSI10_theorem_Dp_and_theorem_I.md`). -/
def finD (l : ℕ) (D : SData ℤ_[p]) : SData ℤ_[p] := iterD p (digitL p l) (kTop p l) D

/-! ### Small equivalences -/

variable {p}

/-- `(Fin m → ℤ_[p] ⧸ p^a) ≃ (Fin n → ℤ_[p] ⧸ p^b)` for `m = n`, `a = b`. -/
def levelEquiv {m n a b : ℕ} (hm : m = n) (hab : a = b) :
    (Fin m → Zq p a) ≃ₗ[ℤ_[p]] (Fin n → Zq p b) := by
  subst hm hab; exact LinearEquiv.refl _ _

/-- Splitting off the level `0` of a product over `Fin (K + 1)` of torsion factors. -/
def levelSplit (K h m₀ : ℕ) (c : ℕ → ℕ) (d : ℕ → ℕ) (h0 : m₀ = c 0)
    (hs : ∀ t : ℕ, d t = c (t + 1)) :
    ((Fin m₀ → Zq p h) × ((t : Fin K) → Fin (d t) → Zq p (h + 1 + t))) ≃ₗ[ℤ_[p]]
      ((t : Fin (K + 1)) → Fin (c t) → Zq p (h + t)) :=
  (LinearEquiv.prodCongr
    (levelEquiv (m := m₀) (n := c ((0 : Fin (K + 1)) : ℕ)) (a := h)
      (b := h + ((0 : Fin (K + 1)) : ℕ)) (by simpa using h0) (by simp))
    (LinearEquiv.piCongrRight fun t : Fin K => levelEquiv (m := d t)
      (n := c ((t.succ : Fin (K + 1)) : ℕ)) (a := h + 1 + t) (b := h + ((t.succ : Fin (K + 1)) : ℕ))
      (by simpa using hs t) (by simp only [Fin.val_succ]; ring))).trans
    (Fin.consLinearEquiv ℤ_[p] (fun t : Fin (K + 1) => Fin (c t) → Zq p (h + t)))

lemma mulVecLin_smul' {X : Type*} [Fintype X] [DecidableEq X] (c : ℤ_[p]) (M : Matrix X X ℤ_[p]) :
    (c • M).mulVecLin = c • M.mulVecLin :=
  LinearMap.ext fun v => by simp

/-- The cast `opDS (cast) (M.Fd 1) = famF N` along `M = N`. -/
lemma opDS_cast_famF {M N : DPLattice ℤ_[p]} (h : M = N) :
    opDS (Equiv.cast (congrArg DPLattice.ι h)).symm (M.Fd 1) = famF N := by
  subst h; rfl

/-- Conjugating `c • Gp` by `sysRe`. -/
def reindexQuot {κ ι : Type} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    {S : Type} [Fintype S] [DecidableEq S] (fl : ι → ℕ) (e : κ ≃ ι)
    (T : Module.End ℤ_[p] (ι → ℤ_[p])) (Q : ℕ → Matrix S S ℤ_[p]) (c : ℤ_[p]) :
    (Payment.Sys (fun _ : ι => ℤ_[p]) S ⧸
        LinearMap.range (c • Gp p fl (opDS (Equiv.refl ι) T) Q)) ≃ₗ[ℤ_[p]]
      (Payment.Sys (fun _ : κ => ℤ_[p]) S ⧸ LinearMap.range (c • Gp p (fl ∘ e) (opDS e T) Q)) :=
  quotConj (sysRe ℤ_[p] S e) _ _ (by
    rw [LinearMap.comp_smul, sysRe_comp_Gp, LinearMap.smul_comp])

/-! ### The digit recursion of the data -/

variable (p)

lemma finD_small {l : ℕ} (h : l + 1 < p) (D : SData ℤ_[p]) : finD p l D = D := by
  rw [finD, kTop_small h]; rfl

lemma finD_step {l : ℕ} (h : ¬ l + 1 < p) (D : SData ℤ_[p]) :
    finD p l D = finD p ((l + 1) / p - 1) (stepD p ((l + 1) % p) D) := by
  have hp2 := (Fact.out : p.Prime).two_le
  rw [finD, kTop_step hp2 h, iterD_succ', digitL_step_zero hp2 h, finD]
  congr 1
  funext s
  exact digitL_step_succ hp2 h s

/-! ### The counts along the recursion -/

lemma cnt_zero_step {l : ℕ} (hl : ¬ l + 1 < p) (n : ℕ) :
    (if (l + 1) % p = 0 then 1 else 2) * (p - 1) *
      (Fintype.card (danceL p ((l + 1) / p - 1)).ι * n) = cntT p l 0 * n := by
  have hp2 := (Fact.out : p.Prime).two_le
  rw [card_danceL_kTop, cntT, digitL_step_top hp2 hl, kTop_step hp2 hl, Iset_card_step hp2 hl]
  simp only [Nat.add_sub_cancel, Nat.sub_zero]
  split_ifs <;> ring

lemma cnt_succ_step {l : ℕ} (hl : ¬ l + 1 < p) (n t : ℕ) :
    cntT p ((l + 1) / p - 1) t * ((if (l + 1) % p = 0 then 1 else 2) * n) =
      cntT p l (t + 1) * n := by
  have hp2 := (Fact.out : p.Prime).two_le
  rw [cntT, cntT, digitL_step_top hp2 hl, kTop_step hp2 hl, Iset_card_step hp2 hl]
  rw [show kTop p ((l + 1) / p - 1) + 1 - (t + 1) - 1 = kTop p ((l + 1) / p - 1) - t - 1 by omega]
  split_ifs <;> ring

lemma last_step {l : ℕ} (hl : ¬ l + 1 < p) (n : ℕ) :
    lastCnt p ((l + 1) / p - 1) * ((if (l + 1) % p = 0 then 1 else 2) * n) = lastCnt p l * n := by
  have hp2 := (Fact.out : p.Prime).two_le
  rw [lastCnt, lastCnt, digitL_step_top hp2 hl, Iset_card_step hp2 hl]
  split_ifs <;> ring

/-! ### Theorem D_p, general form -/

set_option maxHeartbeats 1000000 in
/-- **Theorem D_p, general form** (Part D of `CSI10_theorem_Dp_and_theorem_I.md`, the induction on
the digits, for an arbitrary starting slot type with data `D` and an arbitrary scalar `c = p^h`):
`Sys(danceL p λ, S) ⧸ range (p^h • Gp p flL F Q) ≃
  (Π_{t<k} Fin (cntT t · |S|) → ℤ_[p] ⧸ p^{h+t}) × (Fin (lastCnt · |S|) → ℤ_[p] ⧸ p^{h+k}) ×
  ((S_fin → ℤ_[p]) ⧸ range (p^{h+k} • (p^{d_k} • Q_fin 0 ⋯ Q_fin (d_k − 1))))`,
where `(S_fin, Q_fin) = finD p λ D`. -/
theorem theorem_D_gen (hp : Odd p) (l : ℕ) : ∀ (D : SData ℤ_[p]) (h : ℕ),
    Nonempty ((Payment.Sys (fun _ : (danceL p l).ι => ℤ_[p]) D.S ⧸
        LinearMap.range ((p : ℤ_[p]) ^ h • Gp p (flL p l) (famF (danceL p l)) D.Q)) ≃ₗ[ℤ_[p]]
      (((t : Fin (kTop p l)) → Fin (cntT p l t * Fintype.card D.S) → Zq p (h + t)) ×
        (Fin (lastCnt p l * Fintype.card D.S) → Zq p (h + kTop p l)) ×
        (((finD p l D).S → ℤ_[p]) ⧸ LinearMap.range ((p : ℤ_[p]) ^ (h + kTop p l) •
          ((p : ℤ_[p]) ^ digitL p l (kTop p l) •
            prodQ (finD p l D).Q 0 (digitL p l (kTop p l))).mulVecLin)))) := by
  induction l using Nat.strong_induction_on with
  | _ l ih =>
  intro D h
  have hp2 := (Fact.out : p.Prime).two_le
  by_cases hl : l + 1 < p
  · -- the last level: CSI9 (L1)
    have e1 := reindexQuot (fl := flL p l) (e := (idxDelta p l hl).symm) ((danceL p l).Fd 1) D.Q
      ((p : ℤ_[p]) ^ h)
    have hfl : flL p l ∘ (idxDelta p l hl).symm = Fin.val := funext fun r => G1_delta p l hl r
    have hF : opDS (idxDelta p l hl).symm ((danceL p l).Fd 1) = famF (delta ℤ_[p] l) :=
      opDS_cast_famF (danceL_lt p hl)
    rw [hfl, hF] at e1
    obtain ⟨e2⟩ := L1 p (l + 1) (by omega) (by omega) D.Q ((p : ℤ_[p]) ^ h)
    rw [Nat.add_sub_cancel] at e2
    have hlast : lastCnt p l = l := by
      simp [lastCnt, kTop_small hl, digitL_small hl, Iset_card_small hl]
    rw [finD_small p hl D, kTop_small hl, digitL_small hl]
    refine ⟨(e1.trans e2).trans (?_ : _ ≃ₗ[ℤ_[p]] _)⟩
    refine (LinearEquiv.prodCongr ?_ ?_).trans LinearEquiv.uniqueProd.symm
    · exact ((LinearEquiv.piCongrRight fun _ => quotFinEquiv D.S _).trans (finPiPi _ _ _)).trans
        (levelEquiv (by rw [hlast]) (by simp))
    · exact Submodule.quotEquivOfEq _ _ (by rw [mulVecLin_smul', add_zero])
  · have hb : ((l + 1) / p - 1) < l := b_lt hp2 (by omega)
    have hk : kTop p l = kTop p ((l + 1) / p - 1) + 1 := kTop_step hp2 hl
    have hsucc : digitL p l (kTop p ((l + 1) / p - 1) + 1) = digitL p ((l + 1) / p - 1) (kTop p ((l + 1) / p - 1)) := digitL_step_succ hp2 hl _
    by_cases hd : (l + 1) % p = 0
    · -- digit `0`: the twist move (CSI7)
      have e1 := reindexQuot (fl := flL p l) (e := eTw p l hl hd) ((danceL p l).Fd 1) D.Q
        ((p : ℤ_[p]) ^ h)
      obtain ⟨hfl, hF⟩ := G2_twist p l hl hd
      rw [show flL p l ∘ eTw p l hl hd = flT p (flL p ((l + 1) / p - 1)) from funext hfl, hF] at e1
      obtain ⟨e2⟩ := corollary_Ap2 p hp (flL p ((l + 1) / p - 1)) (famF (danceL p ((l + 1) / p - 1))) D.Q h
      obtain ⟨e3⟩ := ih ((l + 1) / p - 1) hb ⟨D.S, QT p D.Q⟩ (h + 1)
      have hfin : finD p l D = finD p ((l + 1) / p - 1) ⟨D.S, QT p D.Q⟩ := by
        rw [finD_step p hl D, hd, stepD_zero]
      have e1' : (Payment.Sys (fun _ : (danceL p l).ι => ℤ_[p]) D.S ⧸
          LinearMap.range ((p : ℤ_[p]) ^ h • Gp p (flL p l) (famF (danceL p l)) D.Q)) ≃ₗ[ℤ_[p]]
          (Payment.Sys (NT p (fun _ : (danceL p ((l + 1) / p - 1)).ι => ℤ_[p])) D.S ⧸ LinearMap.range
            ((p : ℤ_[p]) ^ h • Gp p (flT p (flL p ((l + 1) / p - 1))) (FT p (famF (danceL p ((l + 1) / p - 1)))) D.Q)) := e1
      have e23 := e2.trans (LinearEquiv.prodCongr (LinearEquiv.refl _ _) e3)
      rw [hfin, hk, hsucc]
      refine ⟨(e1'.trans e23).trans (?_ : _ ≃ₗ[ℤ_[p]] _)⟩
      refine (LinearEquiv.prodAssoc ℤ_[p] _ _ _).symm.trans (?_ : _ ≃ₗ[ℤ_[p]] _)
      refine LinearEquiv.prodCongr ?_ (LinearEquiv.prodCongr (levelEquiv ?_ ?_)
        (Submodule.quotEquivOfEq _ _ ?_))
      · refine LinearEquiv.trans (LinearEquiv.prodCongr (piFinQuotEquiv (p - 1) (danceL p ((l + 1) / p - 1)).ι _)
          (LinearEquiv.refl _ _)) (?_ : _ ≃ₗ[ℤ_[p]] _)
        refine levelSplit (kTop p ((l + 1) / p - 1)) h _ (fun t => cntT p l t * Fintype.card D.S)
          (fun t => cntT p ((l + 1) / p - 1) t * Fintype.card D.S) ?_ ?_
        · simpa [hd] using cnt_zero_step p hl (Fintype.card D.S)
        · intro t
          simpa [hd] using cnt_succ_step p hl (Fintype.card D.S) t
      · simpa [hd] using last_step p hl (Fintype.card D.S)
      · ring
      · rw [show h + (kTop p ((l + 1) / p - 1) + 1) = h + 1 + kTop p ((l + 1) / p - 1) by ring]
    · -- digit `d₀ ≠ 0`: the split move (CSI8)
      have hd1 : 1 ≤ (l + 1) % p := by omega
      have hdp : (l + 1) % p < p := Nat.mod_lt _ (by omega)
      obtain ⟨hfl, hF⟩ := G2_psi p l hl hd1
      have hfl' : flL p l ∘ ePsi p l hl hd1 = flS p ((l + 1) % p) (flL p ((l + 1) / p - 1)) := funext hfl
      have hG : Gp p (flL p l ∘ ePsi p l hl hd1) (opDS (ePsi p l hl hd1) ((danceL p l).Fd 1)) D.Q =
          Gp p (flS p ((l + 1) % p) (flL p ((l + 1) / p - 1))) (FS p ((l + 1) % p) hd1 (famF (danceL p ((l + 1) / p - 1)))) D.Q := by
        rw [hfl', hF]
      have hr0 : 0 < (l + 1) % p := by omega
      obtain ⟨e2⟩ := corollary_M2 p ((l + 1) % p) hp hr0 hdp (flL p ((l + 1) / p - 1)) (famF (danceL p ((l + 1) / p - 1))) D.Q h
      obtain ⟨e3⟩ := ih ((l + 1) / p - 1) hb ⟨D.S × Bool, QS p ((l + 1) % p) D.Q⟩ (h + 1)
      have hfin : finD p l D = finD p ((l + 1) / p - 1) ⟨D.S × Bool, QS p ((l + 1) % p) D.Q⟩ := by
        rw [finD_step p hl D, stepD_pos p _ hd]
      have e1' : (Payment.Sys (fun _ : (danceL p l).ι => ℤ_[p]) D.S ⧸
          LinearMap.range ((p : ℤ_[p]) ^ h • Gp p (flL p l) (famF (danceL p l)) D.Q)) ≃ₗ[ℤ_[p]]
          (Payment.Sys (NS p (fun _ : (danceL p ((l + 1) / p - 1)).ι => ℤ_[p])) D.S ⧸ LinearMap.range
            ((p : ℤ_[p]) ^ h • Gp p (flS p ((l + 1) % p) (flL p ((l + 1) / p - 1)))
              (FS p ((l + 1) % p) hd1 (famF (danceL p ((l + 1) / p - 1)))) D.Q)) :=
        (reindexQuot (fl := flL p l) (e := ePsi p l hl hd1) ((danceL p l).Fd 1) D.Q
          ((p : ℤ_[p]) ^ h)).trans (Submodule.quotEquivOfEq _ _ (by rw [hG]))
      have e23 := e2.trans (LinearEquiv.prodCongr (LinearEquiv.refl _ _) e3)
      rw [hfin, hk, hsucc]
      refine ⟨(e1'.trans e23).trans (?_ : _ ≃ₗ[ℤ_[p]] _)⟩
      refine (LinearEquiv.prodAssoc ℤ_[p] _ _ _).symm.trans (?_ : _ ≃ₗ[ℤ_[p]] _)
      refine LinearEquiv.prodCongr ?_ (LinearEquiv.prodCongr (levelEquiv ?_ ?_)
        (Submodule.quotEquivOfEq _ _ ?_))
      · refine LinearEquiv.trans (LinearEquiv.prodCongr
          (piFinQuotEquiv (2 * (p - 1)) (danceL p ((l + 1) / p - 1)).ι _) (LinearEquiv.refl _ _)) (?_ : _ ≃ₗ[ℤ_[p]] _)
        refine levelSplit (kTop p ((l + 1) / p - 1)) h _ (fun t => cntT p l t * Fintype.card D.S)
          (fun t => cntT p ((l + 1) / p - 1) t * Fintype.card (D.S × Bool)) ?_ ?_
        · have := cnt_zero_step p hl (Fintype.card D.S)
          rw [if_neg hd] at this
          exact this
        · intro t
          have := cnt_succ_step p hl (Fintype.card D.S) t
          rw [if_neg hd] at this
          show cntT p ((l + 1) / p - 1) t * Fintype.card (D.S × Bool) = cntT p l (t + 1) * Fintype.card D.S
          rw [Fintype.card_prod, Fintype.card_bool, ← this]; ring
      · have := last_step p hl (Fintype.card D.S)
        rw [if_neg hd] at this
        change lastCnt p ((l + 1) / p - 1) * Fintype.card (D.S × Bool) = _
        rw [Fintype.card_prod, Fintype.card_bool, ← this]; ring
      · ring
      · rw [show h + (kTop p ((l + 1) / p - 1) + 1) = h + 1 + kTop p ((l + 1) / p - 1) by ring]

/-! ### Theorem D_p -/

variable {p} in
/-- Dropping the level `0` factor `ℤ_[p] ⧸ p^0 = 0` (Part D of
`CSI10_theorem_Dp_and_theorem_I.md`: "for `t = 0` it is the zero module"). -/
def dropLevelZero (K : ℕ) (c c' : ℕ → ℕ) (hc : ∀ t : ℕ, c (t + 1) = c' t) :
    ((t : Fin K) → Fin (c t) → Zq p (0 + t)) ≃ₗ[ℤ_[p]]
      ((t : Fin (K - 1)) → Fin (c' t) → Zq p (t + 1)) := by
  cases K with
  | zero =>
    haveI : IsEmpty (Fin (0 - 1)) := Fin.isEmpty'
    exact LinearEquiv.ofSubsingleton _ _
  | succ K =>
    haveI : Subsingleton (Zq p (0 + ((0 : Fin (K + 1)) : ℕ))) :=
      Submodule.Quotient.subsingleton_iff.2 (by simp)
    haveI : Unique (Fin (c ((0 : Fin (K + 1)) : ℕ)) → Zq p (0 + ((0 : Fin (K + 1)) : ℕ))) :=
      uniqueOfSubsingleton 0
    exact (Fin.consLinearEquiv ℤ_[p] (fun t : Fin (K + 1) => Fin (c t) → Zq p (0 + t))).symm.trans
      ((LinearEquiv.prodCongr (LinearEquiv.refl _ _) (LinearEquiv.piCongrRight fun t : Fin K =>
        levelEquiv (m := c ((t.succ : Fin (K + 1)) : ℕ)) (n := c' t)
          (a := 0 + ((t.succ : Fin (K + 1)) : ℕ)) (b := t + 1)
          (by simpa using hc t) (by simp))).trans LinearEquiv.uniqueProd)

/-- **(D1) Theorem D_p** (Part D of `CSI10_theorem_Dp_and_theorem_I.md`): for an odd prime `p`,
`λ, i : ℕ` and `e ≥ 1`, writing `λ + 1 = Σ_{t ≤ k} d_t p^t` (`d_k ≠ 0`) and
`I = {t < k : d_t ≠ 0}`,
`Y_p(λ, i, e) ≃ₗ[ℤ_[p]]
  (Π_{t=1}^{k−1} (Fin ((p−1) d_k p^{k−t−1} 2^{|I|}) → ℤ_[p] ⧸ p^t)) ×
  (Fin ((d_k − 1) 2^{|I|}) → ℤ_[p] ⧸ p^k) ×
  ((slots → ℤ_[p]) ⧸ range (p^k • Mp p λ i e))`,
the product over `t ∈ [1, k−1]` being indexed by `t : Fin (k − 1)` (standing for `t + 1`), and
`Mp` acting on column vectors (`Matrix.mulVecLin`, CSI9 (L1)'s convention). -/
theorem theorem_Dp (hp : Odd p) (l i e : ℕ) (he : 1 ≤ e) :
    Nonempty (Yp p l i e ≃ₗ[ℤ_[p]]
      (((t : Fin (kTop p l - 1)) →
          Fin ((p - 1) * digitL p l (kTop p l) * p ^ (kTop p l - (t + 1) - 1) * 2 ^ (Iset p l).card) →
            Zq p (t + 1)) ×
        (Fin ((digitL p l (kTop p l) - 1) * 2 ^ (Iset p l).card) → Zq p (kTop p l)) ×
        ((slots p l i e → ℤ_[p]) ⧸
          LinearMap.range ((p : ℤ_[p]) ^ kTop p l • (Mp p l i e).mulVecLin)))) := by
  obtain ⟨eG⟩ := theorem_D_gen p hp l ⟨Unit, Q0 ℤ_[p] p e i⟩ 0
  have e0 : (Payment.Sys (fun _ : (danceL p l).ι => ℤ_[p]) Unit ⧸
      LinearMap.range ((p : ℤ_[p]) ^ 0 • Gp p (flL p l) (famF (danceL p l)) (Q0 ℤ_[p] p e i)))
      ≃ₗ[ℤ_[p]] Yp p l i e :=
    quotConj (sysUnitE ℤ_[p] (danceL p l).ι) _ _ (by
      rw [pow_zero, one_smul]; exact G3_operator p l e i he)
  refine ⟨e0.symm.trans (eG.trans (LinearEquiv.prodCongr ?_ (LinearEquiv.prodCongr ?_ ?_)))⟩
  · refine dropLevelZero (p := p) (kTop p l)
      (fun t => cntT p l t * Fintype.card (⟨Unit, Q0 ℤ_[p] p e i⟩ : SData ℤ_[p]).S)
      (fun t => (p - 1) * digitL p l (kTop p l) * p ^ (kTop p l - (t + 1) - 1) * 2 ^ (Iset p l).card)
      ?_
    intro t
    change cntT p l (t + 1) * Fintype.card Unit = _
    simp [cntT]
  · exact levelEquiv (p := p) (by simp [lastCnt]) (by simp)
  · exact Submodule.quotEquivOfEq _ _ (by rw [zero_add]; rfl)

end ColouredSand.OddTwist
