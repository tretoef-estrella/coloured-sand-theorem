module

public import RequestProject.Strings.Basic
public import RequestProject.Strings.Decomposition
public import RequestProject.Strings.Bidiagonal
public import RequestProject.Strings.Global
public import RequestProject.Strings.StringCoker
public import RequestProject.Strings.TheoremE

/-!
# Strings of the Boolean lattice and Theorem E — index

Formalization of `CS1_strings_and_theorem_E.md`, namespace `ColouredSand.Strings`:

* §0, (S1), (S2): `RequestProject/Strings/Basic.lean`
  (`B`, `H`, `U`, `D`, `level`, `commutator_DU_UD`, `string_relation`).
* (S3)(a),(b),(c): `RequestProject/Strings/Decomposition.lean`
  (`Lam`, `Lam_zero`, `strings_a`, `stringMap`, `strings_b`, `stringEquiv`, `strings_c`).
* (S3), closing remark: `RequestProject/Strings/Global.lean`
  (`Lam_free_finrank` for PIDs, `Lam_free_finrank_of_isLocalRing` for local rings).
* (S4): `RequestProject/Strings/Bidiagonal.lean` (`bidiagonal_coker`).
* (S5): `RequestProject/Strings/TheoremE.lean` (`theorem_E`), using the ring-independent
  `coker_opM_equiv` of `RequestProject/Strings/StringCoker.lean`.
-/
