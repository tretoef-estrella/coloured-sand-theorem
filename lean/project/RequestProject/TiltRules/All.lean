module

public import RequestProject.TiltRules.PartS
public import RequestProject.TiltRules.PartR

/-!
# `CSG4_tensor_rules.md`: the tensor rules `V ⊗ T(λ)` (index)

* `Tools.lean`, `Untw.lean`: descent of `ℚ_[p]`-isomorphisms that intertwine the divided powers
  and match the lattices to isomorphisms of DP-lattices over `ℤ_[p]` (untwisted models,
  generators of lattices).
* `GlueIso.lean`: isomorphisms between glued lattices (unit rescaling of the glue, integral
  glue `≅ Δ ⊕ Δ`, shift `0`).
* `Weyl.lean`, `Split.lean`, `Slices.lean`: the Weyl coordinates `A_i, B_i, C_j, D_j` of
  `V ⊗ (Δ(λ) ⊕ Δ(μ))` via `PsiCG` (§3, Step 1).
* `Main.lean`, `SplitZero.lean`: the splitting of `V ⊗ glueDP` into two glued lattices
  (§3, Steps 2–3), for `μ ≥ 1` and for `μ = 0`.
* `PartS.lean`: **(S0)**, **(S1)**, **(S2)**.
* `PartR.lean`: the shifted weights, **(R1)**, **(R2)**, **(R3)** (`a ≥ 1` and `a = 0`),
  **(R4)**.
-/
