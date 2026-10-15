# THE COLOURED SAND THEOREM — LEAN CERTIFICATE v2
## A machine-checked proof, in Lean 4 with Mathlib, of every theorem of «The Coloured Sand Theorem» (Theorems A–J), for every prime — among them the whole Sylow p-subgroup of the sandpile group of the Hamming graph H(d, q) for every prime p dividing q and every d

*Rafael Amichis Luengo (ORCID 0009-0008-6252-675X). Written by Grepy Ship (Claude), 15 October 2026. Version 2 of the certificate: it adds the three cases missing from version 1 and applies the corrections of the cold reading of version 1 (§10).*

---

## 0. Verdict

**Every theorem of «The Coloured Sand Theorem», Theorems A–J with their lemmas and corollaries, and Example 9, is proved in Lean 4 with Mathlib for every prime, with no `sorry`, no axiom beyond the three standard ones, and no `native_decide`.** The Lean project was rebuilt from its sources on GitHub's machines, on Mathlib's published build (§5.3).

- **Odd primes.** The headline is `ColouredSand.OddTwist.oddTotal_S2` (§1.1): for every odd prime `p`, every `q ≥ 2` with `p | q` and every `d`, the `p`-primary part of the sandpile group of `H(d, q)` is an explicit direct sum of cyclic groups (Theorem J).
- **The prime 2.** `ColouredSand.ThmH.T4` gives the 2-part for every even `q` and every `d` (Theorem H); `ColouredSand.TwoI.twoI_theorem_I` is Theorem I at `p = 2`; `ColouredSand.ThmGTwo.twoThmG` is Theorems F and G at `p = 2` (§1.4).
- **One environment.** The final check is six files; each imports all 36 pieces, and together they repeat every piece's hand restatements. Together they print 451 answers to `#print axioms`, each within `[propext, Classical.choice, Quot.sound]`, with no error.
- **The cone.** The union cone of the 31 headline theorems has 9 833 project declarations in 335 modules (§3.3).

## 1. The certified statements

### 1.1 The headline for odd primes, verbatim

From `RequestProject/OddTotal/Sylow.lean`, namespace `ColouredSand.OddTwist`, `p` a prime (`[Fact p.Prime]`):

```lean
theorem oddTotal_S2 (hp2 : p ≠ 2) {d q : ℕ} (hq2 : 2 ≤ q) (hq : 1 ≤ padicValNat p q) :
    Nonempty (AddCommGroup.primaryComponent (sandpile d q) p ≃+
      ((σ : Σ j : Fin (d + 1), Fin (d.choose j * (q - 2) ^ (j : ℕ))) →
        (i : Fin (oddTotalTotList p q σ.1 (d - σ.1)).length) →
          ZMod (p ^ (oddTotalTotList p q σ.1 (d - σ.1)).get i)))
```

In words: for every odd prime `p`, every `q ≥ 2` with `p | q` and every `d ≥ 0`, the `p`-primary part of the sandpile group of `H(d, q)` is isomorphic to a direct sum of cyclic groups `ℤ/p^a`, one for each entry `a` of an explicit list, repeated `C(d, j)(q − 2)^j` times for each `j = 0, …, d`.

Its companion `oddTotal_S1` (same file) gives the integral form `ℤ_p × Syl_p K ≃ ⊕ Y_p(λ, i, e)` with no hypothesis on `p | q` beyond `q ≥ 2`.

### 1.2 The definitions it uses, verbatim

```lean
-- RequestProject/Splitting/Basic.lean, namespace ColouredSand.Splitting
def hammingGraph (d q : ℕ) : SimpleGraph (Fin d → Fin q) where
  Adj x y := hammingDist x y = 1
  ...
noncomputable def laplacian (d q : ℕ) :
    ((Fin d → Fin q) → ℤ) →ₗ[ℤ] ((Fin d → Fin q) → ℤ) :=
  ((hammingGraph d q).lapMatrix ℤ).mulVecLin

-- RequestProject/TheoremB/Basic.lean, namespace ColouredSand.TheoremB
abbrev cokerL (d q : ℕ) : Type :=
  ((Fin d → Fin q) → ℤ) ⧸ LinearMap.range (ColouredSand.Splitting.laplacian d q)
noncomputable abbrev sandpile (d q : ℕ) : Submodule ℤ (cokerL d q) :=
  Submodule.torsion ℤ (cokerL d q)

-- RequestProject/OddDance/Rule.lean (the odd dance rule and its levels)
def VdotL (p : ℕ) (l : ℕ) : List ℕ :=
  if _h0 : l = 0 then [1]
  else if _h1 : l + 1 < p then [l + 1, l - 1]
  else if h2 : (l + 1) % p = 0 then [l + 1]
  else if (l + 1) % p = 1 then [l + 1, l - 1, l - 1]
  else if (l + 1) % p ≤ p - 2 then [l + 1, l - 1]
  else (l - 1) :: (VdotL p ((l + 1) / p - 1)).map (fun b' => p * b' + p - 1)
def LL (p : ℕ) : ℕ → List ℕ
  | 0 => [0]
  | m + 1 => (LL p m).flatMap (VdotL p)

-- RequestProject/OddTotal/Exponents.lean and Sylow.lean
def oddTotalSpList (l : ℕ) : List ℕ :=
  (List.ofFn fun t : Fin (kTop p l - 1) =>
      List.replicate ((p - 1) * digitL p l (kTop p l) * p ^ (kTop p l - (t + 1) - 1) *
        2 ^ (Iset p l).card) ((t : ℕ) + 1)).flatten ++
    List.replicate ((digitL p l (kTop p l) - 1) * 2 ^ (Iset p l).card) (kTop p l)
def oddTotalCList (l i e : ℕ) : List ℕ :=
  if i = 0 then
    List.ofFn fun j : Fin (2 ^ #(Iset p l) - 1) => kTop p l +
      ((e : ℤ) * (oddSmithK p l : ℤ) + oddSmithYhatSharp p l e (2 ^ #(Iset p l) - 2 - j)).toNat
  else
    List.ofFn fun j : Fin (2 ^ #(Iset p l)) => kTop p l +
      (oddSmithC p l i e + oddSmithYhat p l i e (2 ^ #(Iset p l) - 1 - j)).toNat
def oddTotalYList (l i e : ℕ) : List ℕ := oddTotalSpList p l ++ oddTotalCList p l i e
def oddTotalTotList (q c m : ℕ) : List ℕ :=
  ((LL p m).flatMap fun l => oddTotalYList p l (c + (m - l) / 2) (padicValNat p q)).filter
    (fun a => a ≠ 0)
```

`digitL p l t` is the `t`-th base-`p` digit of `l + 1` and `kTop p l` its top index (`OddTheoremI/Basic.lean`); `Iset p l` is the set of `t < k` with `d_t ≠ 0`; `oddSmithK`, `oddSmithC`, `oddSmithYhat`, `oddSmithYhatSharp` (`OddSmith/Basic.lean`) are `K = d_k p^k`, `e·K + κ_p(i−1, K)`, and the antitonic fits of the clocks (CSI18).

### 1.3 Faithfulness to the paper, line by line (odd primes)

Read against version 6 of the paper (`coloured_sand_theorem.tex`), Theorems I and J (§«The whole group»).

1. **The object.** `sandpile d q` is the torsion submodule of `ℤ^{vertices} ⧸ range L`, with `L` Mathlib's `lapMatrix ℤ` of `hammingGraph d q` (vertices `Fin d → Fin q`, adjacent iff Hamming distance 1). This is `K(H(d,q))` of the paper. `AddCommGroup.primaryComponent _ p` is `Syl_p`.
2. **The index set.** The paper sums over `j = 0, …, d`, over `C(d, j)·(q−2)^j` copies, and over `λ` with multiplicity `n_λ(d−j)`. Lean sums over `σ = (j, copy)` with `j : Fin (d+1)` and `copy : Fin (d.choose j * (q−2)^j)`, and over the list `LL p (d−j)`. In Lean the multiplicity of `λ` is, by definition, the number of times `λ` occurs in `LL p m`; `oddTotal_T1` proves `V^{⊗m} ⊗ ℤ_p ≅ ⊕_{λ ∈ LL p m} L(λ)` for every `m`. The block of `λ` carries `i = j + (d−j−λ)/2` and `e = v_p(q)`, as in the paper.
3. **The exponents.** `oddTotalSpList` is `S_p(λ)` of Theorem I, term by term: `(p−1) d_k p^{k−h−1} 2^{|I|}` copies of `ℤ/p^h` for `h = 1, …, k−1`, and `(d_k−1) 2^{|I|}` copies of `ℤ/p^k`. `oddTotalCList` gives the large summands of Theorem J.
   - For `i ≥ 1`: exponents `k + eK + κ_p(i−1, K) + ŷ_D`, since `oddSmithC p l i e = e·K + kappaP p (i−1) K`.
   - For `i = 0`: exponents `k + eK + ŷ^♯_D` for the `2^{|I|} − 1` non-empty `D`, plus one free summand. That summand is the `ℤ_p` on the left of `oddTotal_S1`, and it is absent from `oddTotal_S2`, which is stated for `Syl_p` alone.
   - `ŷ`, `ŷ^♯` are the integer antitonic fits (`ifit`) of the clocks of the paper in the o-order.
   - The list enumerates the dancers in that order; only the multiset of exponents enters a direct sum.
4. **Zero exponents.** `oddTotalTotList` filters out exponents equal to `0`. A factor `ℤ/p^0` is the trivial group, so the filter changes nothing.
5. **More general than printed.**
   - `oddTotal_S2` holds for every `d ≥ 0`; the paper says `d ≥ 1`.
   - `oddTotal_S1` needs only `q ≥ 2`, not `p | q`.
   - `theorem_I` (CSI10) is the paper's Theorem I for odd `p`; Theorem I at `p = 2` is `twoI_theorem_I` (§1.4).
6. **What the Lean statement does not contain.** The paper also describes the multiplicities `n_λ(m)` by peeling characters `ch T(λ)` off `(z+z^{-1})^m`. In Lean they are given by the recursion `LL`, which is proved to be the decomposition of `V^{⊗m}` into the lattices `L(λ)`. The character recipe itself is a computational description and is not formalized. It does not enter any statement.
7. **Theorem I** (`ColouredSand.OddTwist.theorem_I`): `Y_p(λ,i,e) ≅ S_p(λ) × C`, with `S_p(λ)` killed by `p^k`, `C` generated by `2^{|I|}` elements and `C/p^{k+1}C ≅ (ℤ/p^{k+1})^{2^{|I|}}`. That is: exactly `2^{|I|}` summands of order larger than `p^k`, counting a free summand as one, and the others form `S_p(λ)`. Here `Y_p` is the cokernel of `sigmaOp` on the dance lattice `danceL p λ`; `oddTotal_B1` proves it equal to the operator `f + p^e(D_λ + i)` of the paper, `opT`.
8. **The lattices.** In Lean, Theorem I and the block formulas of Theorem J are proved for the dance lattices `L(λ)`. Their identification with `T_{ℤ_p}(λ)` (the paper's Lemma «dance» (ii)) is not formalized, and it is not needed for the statement on `K(H(d, q))`: the sandpile group is decomposed in Lean directly into the lattices `L(λ)`.

### 1.4 The prime 2, and Theorem E for every prime

These are the three cases added in version 2 of the certificate (pieces CSX1–CSX3). Before them, the Lean statements of Theorems F and G assumed `p ≠ 2`, and that of Theorem E assumed `p | q`.

```lean
-- RequestProject/StringsAll/TheoremE.lean (CSX1): Theorem E for every prime p and every q ≠ 0
theorem strAll_theorem_E (p : ℕ) [Fact p.Prime] (q : ℤ) (hq : q ≠ 0) (c m : ℕ) (hm : m < p) :
    Nonempty ((B m ℤ_[p] ⧸ LinearMap.range
        ((q : ℤ_[p]) • ((c : ℤ_[p]) • LinearMap.id + H m ℤ_[p]) + U m ℤ_[p])) ≃ₗ[ℤ_[p]]
      ((Fin (if c = 0 then 1 else 0) → ℤ_[p]) ×
        ((t : Σ k : {k : Fin (m / 2 + 1) // (c, (k : ℕ)) ≠ (0, 0)}, Fin (strMult m k)) →
          ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ expA p q c m t.1})))

-- RequestProject/TwoTheoremI/TheoremI.lean (CSX2): Theorem I at p = 2, on the family groups of [DST]
theorem twoI_theorem_I (l i α : ℕ) (hα : 1 ≤ α) :
    Nonempty (X (Families.ds l) α i ≃ₗ[ℤ_[2]] SC (Families.ds l) × CmodTwo (Families.ds l) α i) ∧
    (∀ x : SC (Families.ds l), (2 : ℤ_[2]) ^ (Families.ds l).length • x = 0) ∧
    (∃ g : Fin (2 ^ Dance.mCount (Families.ds l)) → CmodTwo (Families.ds l) α i,
      Submodule.span ℤ_[2] (Set.range g) = ⊤) ∧
    Nonempty ((CmodTwo (Families.ds l) α i ⧸ (2 : ℤ_[2]) ^ ((Families.ds l).length + 1) •
        (⊤ : Submodule ℤ_[2] (CmodTwo (Families.ds l) α i))) ≃ₗ[ℤ_[2]]
      (Fin (2 ^ Dance.mCount (Families.ds l)) → Q ((Families.ds l).length + 1))) ∧
    Nonempty ((X (Families.ds l) α i ⧸ (2 : ℤ_[2]) ^ ((Families.ds l).length + 1) •
        (⊤ : Submodule ℤ_[2] (X (Families.ds l) α i))) ≃ₗ[ℤ_[2]]
      (SC (Families.ds l) × (Fin (2 ^ Dance.mCount (Families.ds l)) →
        Q ((Families.ds l).length + 1))))
```

- **Theorem E** (CSX1). `strAll_theorem_E` is the statement of `Strings.theorem_E` with the hypothesis `1 ≤ v_p(q)` replaced by `q ≠ 0`; the companion `strAll_theorem_E_coprime` treats `p ∤ q`, where every exponent is `Σ v_p(c+r)`, as the paper says for `e = 0`. Theorem E is stated in Lean, as in CS1, for the `ℤ_p`-module `coker(q(c+H)+U)` on `B_m(ℤ_p)`, including its free summand `ℤ_p^{[c=0]}`. The paper's form, for `Syl_p X_q(m,c)`, follows with `Corollaries.sylTorsXq_equiv` and `ThmH.freeTorsionEquiv`. The check file `checks/CheckTheoremEPaperForm.lean` states it and proves it in about 30 lines (`GrepyG4E.paperE`: every prime, every natural `q ≠ 0`; standard axioms, exit 0, 201 s, 1 308 432 KiB). That file was written by the second cold reader, and it is not one of the 36 pieces.
- **Theorem I at `p = 2`** (CSX2). At `p = 2` the block `Y_2(λ, i, e)` of the paper is, on paper, the family group `X^{(e)}(λ, i)` of [DST], which is the form in which Theorem H states the 2-part (`ColouredSand.ThmH.T4`). In Lean, `FamilyGroup.X` is the cokernel on the [DST] dance lattice `Dance.SysT ℤ_[2] (ds λ)`. Its identification with `T_{ℤ_2}(λ)` ([DST], Remark (1) after Theorem 3.6) is not formalized, exactly as for `L(λ)` at odd `p` (§1.3, point 8). `twoI_theorem_I` states Theorem I for it: `X ≅ S_2 × C`, `2^k S_2 = 0`, `C` generated by `2^{|I|}` elements, and `C/2^{k+1}C ≅ (ℤ/2^{k+1})^{2^{|I|}}`, with `k` and `|I|` read from the binary digits of `λ + 1` (`twoI_I6`).
- **Theorems F and G at `p = 2`** (CSX3). `twoThmG` (`ThmGTwo/Assembly.lean`) is the conjunction of the six statements of CSG7 (`ThmG.T1`, `T2`, `F1`, `F2`, `S1`, `S2`) at `p = 2`, with the bounds `m ≤ 5` (Theorem G) and `m ≤ 2` (Theorem F) that the paper gives for `p = 2`. The theorems `twoT1_allPrimes`, `twoT2_allPrimes`, `twoF1_allPrimes`, `twoF2_allPrimes`, `twoS1_allPrimes`, `twoS2_allPrimes` are CSG7's statements with the hypothesis `p ≠ 2` removed: for odd `p` they are CSG7's theorems, for `p = 2` those of CSX3.

## 2. What is not certified

- **Nothing of the topology.** The paper has none: the result is about a graph.
- **The character recipe for `n_λ(m)`** (§1.3, point 6), which is replaced by a proved recursion.
- **The identification of the dance lattice `L(λ)` with `T_{ℤ_p}(λ)`**, and of the number of occurrences of `λ` in `LL p m` with the multiplicity of `T(λ)` in `V^{⊗m}` (§1.3, point 8). The Lean theorems are stated for `L(λ)` and `LL`; the statement on `K(H(d, q))` does not need the identification.
- **At `p = 2`, the identification of the [DST] dance lattices**, on which `FamilyGroup.X` is defined, with `T_{ℤ_2}(λ)`, and of the multiplicities of the recursion `FamDec.L` with those of `T(λ)` in `V^{⊗m}`. Theorem I at `p = 2` and Theorem H are stated in Lean for these lattices. The statements on `K(H(d, q))` do not need the identification.
- **Theorem E in the paper's form, as one of the 36 pieces.** The pieces state it for the `ℤ_p`-cokernel (§1.4). The paper's form is checked by the separate file `checks/CheckTheoremEPaperForm.lean`.
- **Example 10** of the paper (the block `λ = 12`, `p = 3`) has no Lean statement.
- **The numerical verification record of the paper** (the cells and Smith-form computations of its §«Verification»). It is evidence, not part of the proof, and the Lean proof does not use it.

## 3. How the proof is organised in Lean

Thirty-six pieces, each written as a statement file for Harmonic's Aristotle, proved there, then certified on the author's machine. The pieces are:

- CS1–CS6 and CSG1–CSG7: the theorems of version 3 of the paper, with Lemmas 7 and 8;
- CSH1: Theorem H;
- CSI1–CSI19: Theorems I and J for odd primes, through «the odd dance»;
- CSX1–CSX3: Theorem E for every prime, Theorem I at `p = 2`, Theorems F and G at `p = 2`.

Everything lives in one Lake project, which also holds the certified Lean proof of «The Dancing Sand Theorem» [DST]. Theorem H, Theorem I at `p = 2` and the chain of `oddTotal_S2` use some of its modules. The published project (§8) contains the 438 modules imported by the final check.

The chain of the headline theorem:

1. `oddTotal_S2` rests on `corollary1_whole` (Theorem A at the valuation `v_p(q)`) and on `oddTotal_factor_tors` (CSI19), the torsion form of `oddTotal_factor`; `oddTotal_S1` is the integral form of the same `oddTotal_factor`.
2. `oddTotal_factor` rests on the block decomposition of `V^{⊗m}` (CSI6 `tpow_danceL`, CSI19 `oddTotal_T1`, `oddTotal_B1`); `oddTotal_factor_tors` also on the closed form of each block (CSI18);
3. which rests on part `I1` of `theorem_I` (CSI10) and on the Smith form of `Mp` (CSI18);
4. which rests on the windows, rulers, ceiling, houses, Theorem F at `p` and the cell floor (CSI11–CSI17);
5. which rest on the moves of the odd dance (CSI1–CSI9).

### 3.1 Two name clashes, resolved by pure renames

- **First clash.** CSI1 and CSI4 on one side, CSI11, CSI13 and CSI15 on the other, defined `D1`, `D2` (CSI1, CSI11), `two_le_p` (CSI1, CSI15) and `P1` (CSI4, CSI13). They could not be loaded together in CSI18, which imports both sides. Aristotle renamed them in CSI11, CSI13 and CSI15 and in the files of CSI16 and CSI17 that use them (14 files), on 14 October.
- **Second clash.** CSI2 (`OddTwistModP`) and CSI4 (`OddSES`) both defined `C1`, `C2`, `C3`, `S1`. On 15 October they were renamed `oddModP_*` in CSI2 only (five files). CSI2 is a leaf: no other module imports it.

Both renames were verified to be pure: undoing the substitution gives files identical byte for byte to the originals. After the renames, every affected module was rebuilt and every affected check was run again (exit 0).

### 3.2 Why the final check is six files

All 36 per-piece checks in one file run longer than the 15-minute cap of the author's machine. The final check is therefore split into six files, `CheckColouredSandFinal2A1` to `A5` (pieces 1–18 in five parts) and `CheckColouredSandFinal2B` (pieces 19–36). **Each of the six imports all 36 pieces**, so every check runs in the one environment in which every piece is loaded; only the printing is split. Each piece's check file goes, unchanged apart from its import lines, which are gathered at the top of every file, inside its own namespace `FinalCheck.<piece>`.

### 3.3 The dependency cone

From `checks/final/DepsColouredSand2.lean`: for each headline theorem, the number of project declarations in its transitive cone and the number of modules they come from.

| Theorem | Project declarations in the cone | Modules |
|---|---:|---:|
| `ColouredSand.Splitting.theorem_A` | 193 | 9 |
| `ColouredSand.TheoremB.theorem_B` | 609 | 19 |
| `ColouredSand.Exponent.theorem_C` | 437 | 20 |
| `ColouredSand.NumberOfFactors.theorem_D` | 499 | 20 |
| `ColouredSand.NumberOfFactors.wilson_diagonal_form` | 161 | 6 |
| `ColouredSand.Strings.theorem_E` | 258 | 6 |
| `ColouredSand.ThmG.F1` | 363 | 8 |
| `ColouredSand.ThmG.F2` | 2644 | 84 |
| `ColouredSand.ThmG.T1` | 2397 | 80 |
| `ColouredSand.ThmG.T2` | 2420 | 81 |
| `ColouredSand.ThmG.S1` | 2636 | 89 |
| `ColouredSand.ThmG.S2` | 2653 | 89 |
| `ColouredSand.ThmH.T4` | 2719 | 96 |
| `ColouredSand.ThmH.T5` | 2722 | 96 |
| `ColouredSand.Corollaries.corollary1_whole` | 366 | 16 |
| `ColouredSand.Corollaries.corollary6` | 359 | 16 |
| `ColouredSand.Glue.G2_glue_forced` | 334 | 9 |
| `ColouredSand.Blocks.B1` | 514 | 13 |
| `ColouredSand.OddTwist.theorem_I` | 1582 | 48 |
| `ColouredSand.OddTwist.theorem_I_invariant` | 1578 | 48 |
| `ColouredSand.OddTwist.oddTotal_S1` | 2836 | 114 |
| `ColouredSand.OddTwist.oddTotal_S2` | 5136 | 206 |
| `ColouredSand.Strings.strAll_theorem_E` | 258 | 7 |
| `ColouredSand.TwoI.twoI_theorem_I` | 485 | 35 |
| `ColouredSand.ThmGTwo.twoThmG` | 3459 | 145 |
| `ColouredSand.ThmGTwo.twoT1_allPrimes` | 4882 | 177 |
| `ColouredSand.ThmGTwo.twoT2_allPrimes` | 4905 | 177 |
| `ColouredSand.ThmGTwo.twoF1_allPrimes` | 374 | 11 |
| `ColouredSand.ThmGTwo.twoF2_allPrimes` | 5134 | 179 |
| `ColouredSand.ThmGTwo.twoS1_allPrimes` | 5097 | 184 |
| `ColouredSand.ThmGTwo.twoS2_allPrimes` | 5115 | 184 |
| **Union** | **9833** | **335** |

## 4. Trust base

- Lean 4 kernel, toolchain `leanprover/lean4:v4.28.0` (`lean-toolchain`, md5 `b8b2923c…`).
- Mathlib at commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (tag `v4.28.0`), pinned in `lake-manifest.json` (md5 `235e6523…`), with its dependencies at the commits listed there.
- The three standard axioms `propext`, `Classical.choice`, `Quot.sound`. Nine of the 451 answers use a strict subset of them (eight `[propext, Quot.sound]`, one `[propext]`).
- No `sorry`, no `axiom` declared in the project, no `native_decide` (forbidden-construct grep on every piece at certification, and on the published project).

## 5. The procedure

### 5.1 Per piece

1. Statement file, brute-force checked in Python before sending, with controls that can fail.
2. Aristotle builds and proves it.
3. Its output is downloaded, then:
   - diffed against our project (no existing file may change unless the change is declared);
   - grepped for `sorry`, `axiom`, `native_decide`;
   - built on the author's machine one module at a time under a memory and time watchdog (4.5 GiB and 15 minutes per module).
4. A check file restates the main theorems by hand and prints their axioms.
5. A faithfulness reading compares every statement with the statement file.

### 5.2 Final, on the author's machine

- **The final check**, `checks/final/CheckColouredSandFinal2A1.lean` … `A5.lean` and `CheckColouredSandFinal2B.lean`, assembled by `final/assemble_final_v2_partsA.py` and `final/assemble_final_v2_halves.py` from the 36 per-piece check files (their md5 in `final/MANIFEST_checks_md5_v2.txt`; the folder `final/` is in `lean/` of the repository and in the Zenodo record). Each run: exit 0, no error.

| File | Pieces | `#print axioms` answers | Time | Peak memory |
|---|---|---:|---:|---:|
| A1 | 1–4 | 50 | 269 s | 1 270 416 KiB |
| A2 | 5–8 | 57 | 621 s | 1 464 368 KiB |
| A3 | 9–12 | 61 | 223 s | 1 344 656 KiB |
| A4 | 13–15 | 50 | 301 s | 1 136 672 KiB |
| A5 | 16–18 | 46 | 261 s | 1 162 400 KiB |
| B | 19–36 | 187 | 365 s | 1 296 544 KiB |
| **Total** | **36** | **451** | | |

- **The cone**, `checks/final/DepsColouredSand2.lean`: exit 0, 685 s, peak 1 161 456 KiB (1.11 GiB).

### 5.3 The clean rebuild on GitHub Actions

The whole proof was rebuilt from source on GitHub's machines, from the published repository, with the workflow `.github/workflows/lean-build.yml`:

1. a clean checkout of the repository, with no `.lake` and no compiled file;
2. the same `lean-toolchain` and `lake-manifest.json` as on the author's machine;
3. `lake exe cache get` (Mathlib's compiled files), then `lake build` of the 438 modules;
4. the six files of the final check and the cone, run in CI;
5. a step that fails on `sorryAx`, on any error, on any axiom outside the three standard ones, on a number of axiom lines other than 50, 57, 61, 50, 46, 187, or on a missing union line of the cone. This step was tested beforehand on the author's logs: it passes on them and fails on two damaged copies (one with `sorryAx` inserted, one with `Lean.ofReduceBool` inserted).

**The run.** GitHub Actions run 38724562833 (job 116387109221) of https://github.com/tretoef-estrella/coloured-sand-theorem, workflow «Lean build», at commit `51c25f0`, on a GitHub-hosted runner `ubuntu-latest`, 15 October 2026, 11:03:02–11:52:20 UTC: **success**.

| Step | Time |
|---|---:|
| Mathlib's compiled files (`lake exe cache get`) | 1 min 29 s |
| `lake build` of the 438 modules | 33 min 16 s |
| Final check, parts A1–A5 | 3 min 52 s |
| Final check, half B | 2 min 51 s |
| The cone | 7 min 44 s |
| The checking step | passed |

Its logs (artifact `Final_check_actions_logs`, zip md5 `f301083f2c3770791fd24ad2db515fba`) are in the folder `lean/actions/` of the repository and in the Zenodo record, with GitHub's SHA-256 digest of the zip, `b15a709827b7f7f72372f649fde82cd75f5c5300b65bd97c68cfc0a6c20ffb72`. GitHub itself keeps the artifact until 13 January 2027. Their axiom lines are identical, line for line, to those of the runs on the author's machine (§5.2), and the cone's output is identical as well: `UNION: project decls in cone: 9833; modules: 335`.

## 6. Data per piece

Counts measured on the project on 15 October 2026 (`final/per_piece.tsv`). «Lines» are newlines, as counted by `wc -l`. «`theorem`/`lemma` lines» are lines that begin, after spaces, with `theorem` or `lemma`.

| Piece | Content | Lean folder | Files | Lines | `theorem`/`lemma` lines | `#print axioms` in its check |
|---|---|---|---:|---:|---:|---:|
| CS1 | Strings of the Boolean lattice; Theorem E | `Strings` | 7 | 1693 | 84 | 12 |
| CS2 | Theorem A (JNR Thm 13): the splitting | `Splitting` | 9 | 1309 | 76 | 13 |
| CS3 | Theorem B (primes p > d) | `TheoremB` | 9 | 1269 | 52 | 15 |
| CS4 | Theorem C (the exponent) | `Exponent` | 7 | 1196 | 50 | 10 |
| CS5 | Theorem D (number of factors), Wilson diagonal form | `NumberOfFactors` | 8 | 1924 | 68 | 11 |
| CS6 | Corollaries 1 and 6 | `Corollaries` | 5 | 760 | 48 | 9 |
| CSG1 | Lemma 8 (the blocks) | `Blocks` | 14 | 2809 | 104 | 19 |
| CSG2 | Lemma 7 (the glue) | `Glue` | 11 | 1907 | 111 | 18 |
| CSH1 | Theorem H (the prime 2) | `ThmH` | 5 | 789 | 35 | 13 |
| CSG3 | Tilting lattices, Clebsch–Gordan lattice | `TiltP` | 9 | 1998 | 133 | 20 |
| CSG4 | Tensor rules V ⊗ T(λ) | `TiltRules` | 11 | 2310 | 135 | 14 |
| CSG5 | Tensor powers of V as sums of tilting lattices, n ≤ p²+p−1 | `TiltDec` | 4 | 1062 | 72 | 14 |
| CSG6 | The operator on the blocks | `BlockOp` | 4 | 585 | 22 | 15 |
| CSG7 | Theorems F, G; Example 9 | `ThmG` | 7 | 1154 | 42 | 19 |
| CSI1 | The odd twist Φ at p | `OddTwist` | 10 | 1863 | 123 | 16 |
| CSI2 | Reduction mod p (Prop. 1.2(c)) | `OddTwistModP` | 5 | 1268 | 64 | 12 |
| CSI3 | The split (Ψ at r) | `OddSplit` | 11 | 2472 | 178 | 16 |
| CSI4 | Casimir, short exact sequences | `OddSES` | 18 | 2687 | 179 | 18 |
| CSI5 | The splitting (Cayley–Hamilton), tensor decompositions | `OddSplitting` | 5 | 581 | 24 | 13 |
| CSI6 | Dance lattices L(λ); tensor powers of V for every m | `OddDance` | 7 | 1061 | 52 | 12 |
| CSI7 | The odd twist move (Theorem A at p) | `OddPayment` | 5 | 923 | 39 | 8 |
| CSI8 | The odd split move (Prop. 2.2) | `OddSplitMove` | 5 | 938 | 30 | 7 |
| CSI9 | Last level, floors (Prop. 2.3) | `OddLevels` | 5 | 1033 | 49 | 12 |
| CSI10 | Theorem D at p, and Theorem I | `OddTheoremI` | 6 | 977 | 46 | 9 |
| CSI11 | Odd deficit law (Lemma 4.2) | `OddDeficit` | 7 | 996 | 56 | 9 |
| CSI12 | Odd windows (Thm 4.1) | `OddWindows` | 7 | 1263 | 55 | 10 |
| CSI13 | Odd cost form (Prop. 4.3) | `OddRulers` | 5 | 1003 | 50 | 9 |
| CSI14 | The ceiling at p (Thm 6.5) | `OddCeiling` | 6 | 1145 | 45 | 8 |
| CSI15 | Houses at p (Lemmas 7.5–7.7 at p) | `OddHouses` | 5 | 1147 | 62 | 8 |
| CSI16 | Theorem F at p | `OddPotential` | 7 | 1773 | 59 | 11 |
| CSI17 | Integrality and cell floor at p | `OddCellFloor` | 4 | 575 | 19 | 10 |
| CSI18 | Smith form of Mp (Thm 4.4); the groups Y | `OddSmith` | 7 | 1402 | 60 | 15 |
| CSI19 | Theorem TOTAL (Theorem J) | `OddTotal` | 7 | 900 | 36 | 8 |
| CSX1 | Theorem E for every prime | `StringsAll` | 2 | 203 | 6 | 8 |
| CSX2 | Theorem I at p = 2 | `TwoTheoremI` | 4 | 627 | 32 | 15 |
| CSX3 | Theorems F, G at p = 2; forms for every prime | `ThmGTwo` | 6 | 1185 | 74 | 15 |
| **Total** | | 36 folders | **254** | **46787** | **2370** | **451** |

The table above is the file `final/per_piece.tsv`, in the folder `lean/final/` of the repository and in the Zenodo record. Aristotle's task numbers and the certification log of every piece are in the author's working notes, which are not published. Nothing in this certificate depends on them: every count of the table can be measured on the published project, as the start of this section says, and every axiom line of the final check is in the logs of the GitHub Actions run (§5.3) and is reproduced by the commands of §8.

## 7. Totals

**36 pieces, 254 files, 46 787 lines, 2 370 `theorem`/`lemma` lines, 0 `sorry`.**

## 8. Reproducibility

From the folder `lean/project` of the repository https://github.com/tretoef-estrella/coloured-sand-theorem, with Lean and Mathlib as in §4:

```
lake exe cache get
lake build
lake env lean checks/final/CheckColouredSandFinal2A1.lean
lake env lean checks/final/CheckColouredSandFinal2A2.lean
lake env lean checks/final/CheckColouredSandFinal2A3.lean
lake env lean checks/final/CheckColouredSandFinal2A4.lean
lake env lean checks/final/CheckColouredSandFinal2A5.lean
lake env lean checks/final/CheckColouredSandFinal2B.lean
lake env lean checks/final/DepsColouredSand2.lean
```

`lake build` builds the 438 modules of `RequestProject`, which are exactly the modules imported, directly or not, by the seven files. Expected: no error; 50, 57, 61, 50, 46 and 187 lines `depends on axioms`, each within `[propext, Classical.choice, Quot.sound]`; and the union line `UNION: project decls in cone: 9833; modules: 335`. The 36 per-piece check files are in `checks/pieces/`.

## 9. What this certificate claims, in one paragraph

Lean 4 (v4.28.0) with Mathlib checks every theorem of «The Coloured Sand Theorem» for every prime: Theorems A–H with Lemmas 2–5, 7 and 8, Corollaries 1 and 6 and Example 9; Theorem I; and Theorem J — for every odd prime `p`, every `q ≥ 2` with `p | q` and every `d`, the `p`-primary part of the sandpile group of `H(d, q)` is the direct sum of cyclic groups of §1.1, with exponents given by explicit finite formulas in the base-`p` digits — together with Theorem H, which gives the 2-part for every even `q`. Theorem I and the block formulas of Theorem J are proved for explicit dance lattices: `L(λ)` for odd `p` and the lattices of [DST] for `p = 2` (§1.3, point 8; §1.4); Theorem E is stated for the `ℤ_p`-cokernel, and its form for `Syl_p X_q(m,c)` is checked by a separate file (§1.4). It uses only the three standard axioms. The proof was produced piece by piece by Aristotle, certified piece by piece on the author's machine, checked in one environment, and rebuilt from its sources on GitHub Actions, on Mathlib's published build.

## 10. Changes from version 1

Version 1 of this certificate (15 October 2026) was read cold by an independent reader («Grepy el Lacre»), who found no fatal error and three overclaims. Version 2:

- **Adds the three missing cases** (§1.4): Theorem E for every prime (CSX1), Theorem I at `p = 2` (CSX2), Theorems F and G at `p = 2` (CSX3). Version 1 claimed Theorems A–J «in Lean» while the Lean statements of F and G assumed `p ≠ 2`, that of E assumed `p | q`, and Theorem I at `p = 2` had no Lean statement.
- **States the lattice point** (§1.3, point 8; §2): Theorem I and the block formulas of Theorem J are proved for `L(λ)`, not for `T_{ℤ_p}(λ)`.
- **Corrects** the ORCID iD; the description of the first name clash (§3.1); the chain of the headline theorem (§3); the memory unit (KiB); the Lean folder of CSG2 (`Glue`); the references, which now give each concept DOI and each version DOI, labelled.
- **Updates** every count and the cone (31 headline theorems; 9 833 declarations in 335 modules), §1.3 points 2 and 5, the title («for every prime»), and gives the reproduction from the published repository (§8); version 1 was a draft.
- **Replaces** the single final check by six files, each loading all 36 pieces (§3.2), and records the clean rebuild on GitHub Actions (§5.3), which version 1 listed as owed.

After this list was written, the changes of version 2 and of paper version 6 were read cold by a second reader («Grepy Cartas Largas»). That reader found no error in the Lean statements and no fatal finding. Its corrections of wording are applied in this version, with the check file of §1.4 and the items added to §2.

## References

- R. Amichis Luengo, *The Coloured Sand Theorem*, Zenodo, concept DOI 10.5281/zenodo.23327608 (all versions); version 4: 10.5281/zenodo.23364147. This certificate is deposited with version 6 of the paper, in the same Zenodo record.
- R. Amichis Luengo, *The Dancing Sand Theorem* [DST], Zenodo, concept DOI 10.5281/zenodo.23188298 (all versions); version 11: 10.5281/zenodo.23356712; Hexagon hexagon:2610.00205. Its Lean certificate: Zenodo 10.5281/zenodo.23298436.
- B. Jacobson, A. Niedermaier, V. Reiner, *Critical groups for complete multipartite graphs and Cartesian products of complete graphs*, J. Graph Theory 44 (2003) 231–250.
- The Lean 4 theorem prover, https://lean-lang.org; the Mathlib community, *Mathlib*, https://github.com/leanprover-community/mathlib4.
- Harmonic, *Aristotle*, https://aristotle.harmonic.fun.
