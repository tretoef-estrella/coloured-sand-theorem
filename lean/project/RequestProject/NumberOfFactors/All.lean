module

public import RequestProject.NumberOfFactors.Inclusion
public import RequestProject.NumberOfFactors.Abstract
public import RequestProject.NumberOfFactors.Wilson
public import RequestProject.NumberOfFactors.Diagonal
public import RequestProject.NumberOfFactors.RankModP
public import RequestProject.NumberOfFactors.TheoremD
public import RequestProject.NumberOfFactors.Checks

/-!
# `CS5_theorem_D_number_of_factors.md`: Theorem D, the number of cyclic factors

Namespace `ColouredSand.NumberOfFactors`.  Reuses `RequestProject/Strings` (`B_m`, `U`, levels,
`strMult`), `RequestProject/Splitting` (Theorem A, `X_q(m,c)`) and `RequestProject/TheoremB`
(`coker L`, the sandpile group, `coker L ≅ ℤ ⊕ K`, `p`-primary components).

* **(D1)** Wilson's diagonal form of `W_{t,t+1}`: `wilson_diagonal_form` (`Diagonal.lean`); basis
  form `wilson_bases` (`Wilson.lean`).  Auxiliary: `Inclusion.lean` (Gottlieb–Kantor injectivity
  `zeta_inj` and saturation `gsub_sat` of the row modules of inclusion matrices over `ℤ`) and
  `Abstract.lean` (an abstract diagonal-form criterion `abstract_diag`).
* **(D2)** `rank U = ρ_p(m)` on `B_m(ZMod p)`: `rank_U_zmod` (`RankModP.lean`), with `rPart`, `rho`.
* **(D3)** Theorem D: `theorem_D` and `theorem_D'` (`TheoremD.lean`), with `nFactors`.
* **(D4)** Checks: `nFactors_three`, `rho_three`, `rho_two`, `cyclic_factors_three`, `rho_of_lt`
  (`Checks.lean`).
-/
