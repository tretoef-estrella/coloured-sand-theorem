module

public import RequestProject.DanceSmith.All
public import RequestProject.FamilyGroup.Cokernel

/-!
# `C16_the_family_group_over_Z2.md`: Setting

Encodings (namespace `FamilyGroup`):

* `A := ℤ_[2]` is Mathlib's `PadicInt 2`.
* `ds : List Bool`, `k = ds.length`, `I = Windows.Ids ds`, `m = Dance.mCount ds` (`= #I` by
  `Windows.card_Ids`), `N = 2 ^ Dance.mCount ds`, `K = 2 ^ ds.length`; `α i : ℕ`.
* `X ds α i := Dance.SysT ℤ_[2] ds (Fin 1) ⧸ LinearMap.range (Dance.sigma ℤ_[2] ds α i)`
  (the group of the tower, `X^{(α)}(ds, i)`).
* `SC ds := Π_{a : Fin k} (Fin (2^{k + m − 1 − a}) → ℤ_[2]) ⧸ (2^a • ⊤)` (the small clocks), exactly
  the first factor of `Dance.proposition_4_3`.
* `Q e := ℤ_[2] ⧸ Ideal.span {2 ^ e}` (the big clock of exponent `e`).
* The clocks of C15 are reused: `DanceSmith.Cst ds α i` (`C`), `DanceSmith.yHat ds α i` (`ŷ`),
  `DanceSmith.yHatS ds α` (`ŷ^♯`), `DanceSmith.xClk ds α i` (`x`).
* The pooled raw clocks (`α = 1`) of §1.2: `yPool ds i p = ifit N (j ↦ Rulers.clock k I i
  (dancer I j)) p` (`ŷ_i`) and `yPool0 ds q = ifit (N − 1) (j ↦ Rulers.clock k I 0
  (dancer I (j + 1))) q` (`ŷ_0`; the dancer `∅` at position `0` is not pooled).
* Exponents written as integers in the file are natural numbers `E p` with the equation
  `(E p : ℤ) = …`; products over positions are products over `Fin N` (resp. `Fin (N − 1)`), read at
  the natural number `p.val`.
-/

@[expose] public section

namespace FamilyGroup

open Windows TheoremF
open scoped Pointwise

/-- *Setting* of `C16_the_family_group_over_Z2.md` (the group of the tower):
`X^{(α)}(ds, i) := SysT A ds (Fin 1) ⧸ range (sigma A ds α i)` with `A = ℤ_[2]`. -/
abbrev X (ds : List Bool) (α i : ℕ) : Type :=
  Dance.SysT ℤ_[2] ds (Fin 1) ⧸ LinearMap.range (Dance.sigma ℤ_[2] ds α i)

/-- *Setting* of `C16_the_family_group_over_Z2.md` (small clocks, as in
`Dance.proposition_4_3`): `SC(ds) := Π_{a : Fin k} (Fin (2^{k + m − 1 − a}) → A) ⧸ (2^a • ⊤)`. -/
abbrev SC (ds : List Bool) : Type :=
  (a : Fin ds.length) → (Fin (2 ^ (ds.length + Dance.mCount ds - 1 - a)) → ℤ_[2]) ⧸
    (2 : ℤ_[2]) ^ (a : ℕ) •
      (⊤ : Submodule ℤ_[2] (Fin (2 ^ (ds.length + Dance.mCount ds - 1 - a)) → ℤ_[2]))

/-- *Setting* of `C16_the_family_group_over_Z2.md` (big clocks): `Q(e) := A ⧸ span {2^e}`. -/
abbrev Q (e : ℕ) : Type := ℤ_[2] ⧸ Ideal.span {(2 : ℤ_[2]) ^ e}

/-- *Setting* of `C16_the_family_group_over_Z2.md` (the pooled clocks, `i ≥ 1`):
`ŷ_i(p) := ifit N (j ↦ u_i(dancer I j)) p` with `u_i(D) = Rulers.clock k I i D`. -/
noncomputable def yPool (ds : List Bool) (i : ℕ) : ℕ → ℤ :=
  AntitonicFit.ifit (2 ^ Dance.mCount ds)
    (fun j => Rulers.clock ds.length (Ids ds) i (dancer (Ids ds) j))

/-- *Setting* of `C16_the_family_group_over_Z2.md` (the pooled clocks, `i = 0`):
`ŷ_0(q) := ifit (N − 1) (j ↦ u_0(dancer I (j + 1))) q`. -/
noncomputable def yPool0 (ds : List Bool) : ℕ → ℤ :=
  AntitonicFit.ifit (2 ^ Dance.mCount ds - 1)
    (fun j => Rulers.clock ds.length (Ids ds) 0 (dancer (Ids ds) (j + 1)))

end FamilyGroup
