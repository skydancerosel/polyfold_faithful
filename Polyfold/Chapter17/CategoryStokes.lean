import Polyfold.Chapter17.CategoryForms
import Polyfold.Chapter17.BranchedSubcategory
import Polyfold.Chapter17.ModelProperties
import Polyfold.Chapter16.StokesWithoutPartitions
import Polyfold.Chapter11.BoundaryMeasureTextHypotheses
import Polyfold.Chapter11.BoundaryMeasureGeneralizedIsoDimOne
import Polyfold.Chapter11.BranchedEquivalenceTangent

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.6 "Sc-Differential Forms and Stokes" (pp. 820–824): the branched integral (17.89) and
**Theorem 17.6.4**, the boundary **Definition 17.6.5**, **Theorem 17.6.6**, **Theorem 17.6.7
(Stokes)**, the effective integral (17.91) and **Theorem 17.6.8**, **Theorem 17.6.9** and
**Theorem 17.6.10 (effective Stokes)**.  Numbers and pages are the 2021 text's.

# Branched integration and Stokes on a polyfold `C = (C, F, M)`

## The text, paraphrased

(pp. 820–821) For `[ω] ∈ Ω∞ᵏ(C)` and `Θ̂ : C → ℚ⁺` tame, oriented, branched, with `|supp Θ|`
compact, and a covering set `Ψ` with model `Γ : X → C`, `Θ̂_Ψ = (Θ ∘ Γ, Γ^*T̂_Θ)` and
`[ω_Ψ] = [Γ^*ω]`.  (**Theorem 17.6.4**) `∫_{Θ̂_Ψ} [ω_Ψ]` does not depend on `Ψ`, so
`∫_Θ̂ [ω] := ∫_{Θ̂_Ψ} [ω_Ψ]` (17.89): for `f : X → X'`, `f^*Θ̂_{Γ'} = Θ̂_Γ`, `f^*[ω_{Ψ'}] = [ω_Ψ]`,
and Theorem 11.4.1 with `K = |supp Θ|`.  (p. 822, **Definition 17.6.5**) `∂Θ := Γ_*(∂(Γ^*Θ))`,
independent of `Ψ` by Theorem 11.3.8.  (**Theorem 17.6.6**) For `Θ̂` oriented, tame, compact of
dimension `n` and `[ω] ∈ Ω∞ⁿ⁻¹(C)`, `∫_{∂Θ̂} [ω] := ∫_{∂(Γ^*Θ̂)} [ω_Ψ]` does not depend on `Ψ`.
(**Theorem 17.6.7, Stokes**) `∫_Θ̂ d[ω] = ∫_{∂Θ̂} [ω]` (17.90); "the proof is immediate since the
statement is equivalent to the ep-groupoid version".  (p. 823) With (LUC),
`∮_Θ̂ [ω] := ∮_{Θ̂_Ψ} [ω_Ψ]` (17.91); (**Theorem 17.6.8**) it does not depend on `Ψ`;
(**Theorem 17.6.9**) neither does `∮_{∂Θ̂} [ω] := ∮_{∂(Γ^*Θ̂)} [ω_Ψ]`; (**Theorem 17.6.10,
effective Stokes**) `∮_Θ̂ d[ω] = ∮_{∂Θ̂} [ω]` (17.92).

## What is formalized

* On ep-groupoids (namespace `EPLocalization.EPLoc`): `orbitSupp_boundaryTheta_eq_image_pullTheta`,
  `preimage_image_univ_boundaryTheta`, and the boundary integrals invariant under `f^*`:
  `boundaryMeasure_pull_univ`, `boundaryMeasureEff_pull_univ`,
  `boundaryBranchedMeasureDim1_pull_univ`, `boundaryBranchedMeasureEffDim1_pull_univ`
  (Theorems 11.4.4, 11.4.5 with `K` the whole support).
* `OrientedSubcategory` (`Θ̂ = (Θ, T̂_Θ)`), `toOriented` (`Θ̂_Ψ`), `pull_toOriented`
  (`f^*Θ̂_{Ψ'} = Θ̂_Ψ`), `isCompactBranched_toOriented`, `IsTameOrientedVia`; `ofModel` (from an
  orientation on one model) with `ofModel_T_self`.
* `integralVia` (17.89) and **`theorem_17_6_4`**; `integralEffVia` (17.91) and
  **`theorem_17_6_8`**; `isLUC_model`.
* `boundaryVia` (`∂Θ`), **`definition_17_6_5`**, `modelPull_boundaryVia` (`Γ^*∂Θ = ∂Γ^*Θ`),
  `isFunctorial_boundaryVia`.
* `boundaryIntegralVia`, **`theorem_17_6_6`**, `boundaryIntegralDim1Via`, `theorem_17_6_6_dim1`;
  `boundaryIntegralEffVia`, **`theorem_17_6_9`**, `boundaryIntegralEffDim1Via`,
  `theorem_17_6_9_dim1`.
* **Stokes**: `theorem_17_6_7_of_epStokes`, `theorem_17_6_7_dim1_of_epStokes`,
  `theorem_17_6_7_of_epStokes_of_family`, `theorem_17_6_10_of_epStokes`,
  `theorem_17_6_10_dim1_of_epStokes` (from Stokes on the ep-groupoid level for the model,
  `EP.StokesWithoutPartitions`, the assertion of Remark 9.5.19); `theorem_17_6_7_hyp`,
  `theorem_17_6_7_dim1_hyp`, `theorem_17_6_10_hyp`, `theorem_17_6_10_dim1_hyp` (the extra
  hypothesis that the model admits sc-smooth partitions of unity); witnesses in
  `CategoryStokesExamples.lean`.

## Readings

* The orientation `T̂_Θ : C∞ → Gr(Ĉ)` is read through the models: an orientation `Γ_Ψ^*T̂_Θ` of
  `Θ ∘ Γ_Ψ` on every model, the family compatible with `f_{Ψ,Ψ'}^*` (`OrientedSubcategory`);
  `Θ̂_Ψ` of the text is `toOriented`.  The Grassmannian functor of `TC` is not built; `ofModel`
  produces such a family from one model.
* Forms are the classes of `Ω∞*(C)` (`catFormsInfty`, `CategoryForms.lean`), `[ω_Ψ]` the component
  on `X_Ψ`.
* "Tame, oriented, of dimension `n`" is read in the form of Chapter 9 on the model used
  (`IsTameOrientedVia`, as `OrientedRep.IsTameOriented` in Chapter 16); the independence theorems
  assume it on both covering families.  "`supp(Θ)` has a compact orbit space" is
  `C.IsCompactBranched Θ` (Definition 17.5.3 (1)), which gives compactness on every model.
* The theorems of the text with `[ω] ∈ Ω∞ⁿ⁻¹(C)` and `n ≥ 2` are stated for `m = n - 1 ≥ 1`
  (`hm : 0 < m`); `n = 1` uses the boundary measures of Theorem 9.5.15 for `n = 1` (`_dim1`).
* `∂Θ̂` in Theorems 17.6.6, 17.6.9 carries the induced orientation of `∂(Γ^*Θ̂)` on the model; the
  boundary integrals are the measures of Theorems 9.5.15, 9.5.16 on the whole support.
* Theorems 17.6.7 and 17.6.10 rest, as Theorem 16.4.6 does, on Stokes on the ep-groupoid level
  (Theorems 9.5.17, 9.5.18), which assume sc-smooth partitions of unity; Remark 9.5.19 leaves their
  removal open.  As in `Chapter16/StokesWithoutPartitions.lean` the theorems are stated from the
  ep-level assertion `EP.StokesWithoutPartitions` for the model (`_of_epStokes`), and with the
  extra hypothesis that the model admits sc-smooth partitions of unity (`_hyp`).  The ep-level
  assertion holds for every ep-groupoid (`EP.stokesWithoutPartitions_all`), so the theorems hold as
  printed: `Chapter16/StokesUnconditional.lean` (`theorem_17_6_7_all`, `theorem_17_6_10_all`, …).
* (LUC) for `C` is Definition 17.1.22 (`S.IsLUC`), which gives (LUC) on every model.
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

namespace EPLocalization.EPLoc

variable {X Y : EP.{u}} {m : ℕ}

/-- `|supp ∂Θ'| = |f|(|supp ∂(f^*Θ')|)` for a generalized isomorphism `f` (Theorem 11.3.8). -/
theorem orbitSupp_boundaryTheta_eq_image_pullTheta {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {Θ' : Y.Obj → ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') :
    Y.X.orbitSupp (Y.X.boundaryTheta Θ') =
      orbitMap f '' X.X.orbitSupp (X.X.boundaryTheta (pullTheta f Θ')) := by
  have hb := Y.X.isFunctorial_boundaryTheta hΘ' (hasIndependentTangentSums (X := Y.X) Θ')
  rw [← theorem_11_3_8_pull hf hΘ' (hasIndependentTangentSums (X := Y.X) Θ'),
    ← orbitSupp_pushTheta hf (isFunctorial_pullTheta f hb), pushTheta_pullTheta hf hb]

/-- `|f|` maps all of `|supp ∂(f^*Θ')|` onto all of `|supp ∂Θ'|`. -/
theorem preimage_image_univ_boundaryTheta {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    {Θ' : Y.Obj → ℚ} (hΘ' : Y.X.IsBranchedEpSubgroupoid Θ') :
    (Subtype.val ⁻¹' (orbitMap f '' (Subtype.val ''
      (univ : Set (X.X.orbitSupp (X.X.boundaryTheta (pullTheta f Θ')))))) :
        Set (Y.X.orbitSupp (Y.X.boundaryTheta Θ'))) = univ := by
  rw [image_univ, Subtype.range_coe, ← orbitSupp_boundaryTheta_eq_image_pullTheta hf hΘ',
    Subtype.coe_preimage_self]

/-- **The boundary integral is invariant under pull-back** (Theorem 11.4.4 with
`K = |supp ∂f^*Θ'|`): `∫_{∂f^*Θ̂'} f^*ω' = ∫_{∂Θ̂'} ω'`, for `A = f^*B`, dimension `m + 1 ≥ 2`. -/
theorem boundaryMeasure_pull_univ {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hm : 0 < m)
    (A : OrientedBranched X) (B : OrientedBranched Y) (hAB : OrientedBranched.pull hf B = A)
    (hcptA : X.X.IsCompactBranched A.Θ)
    (hlocA : ∀ x ∈ supp A.Θ, ∃ C : X.X.OrientedTameStructure (m + 1) A.Θ x, C.Represents A.T)
    (hcptB : Y.X.IsCompactBranched B.Θ)
    (hlocB : ∀ y ∈ supp B.Θ, ∃ C : Y.X.OrientedTameStructure (m + 1) B.Θ y, C.Represents B.T)
    (ω' : Y.epFormsInfty m) :
    X.boundaryMeasure hm A.isBranchedEpSubgroupoid hcptA A.isOrientation hlocA
        (formsPullback f m ω') univ =
      Y.boundaryMeasure hm B.isBranchedEpSubgroupoid hcptB B.isOrientation hlocB ω' univ := by
  subst hAB
  have h := (theorem_11_4_4_pull_loc hf hm B.isBranchedEpSubgroupoid hcptB B.isOrientation hlocB
    ω' (K := univ) MeasurableSet.univ).2
  rw [preimage_image_univ_boundaryTheta hf B.isBranchedEpSubgroupoid] at h
  exact h

/-- **The effective boundary integral is invariant under pull-back** (Theorem 11.4.5 with
`K = |supp ∂f^*Θ'|`), for ep-groupoids with (LUC). -/
theorem boundaryMeasureEff_pull_univ {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (hm : 0 < m)
    (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC)
    (A : OrientedBranched X) (B : OrientedBranched Y) (hAB : OrientedBranched.pull hf B = A)
    (hcptA : X.X.IsCompactBranched A.Θ)
    (hlocA : ∀ x ∈ supp A.Θ, ∃ C : X.X.OrientedTameStructure (m + 1) A.Θ x, C.Represents A.T)
    (hcptB : Y.X.IsCompactBranched B.Θ)
    (hlocB : ∀ y ∈ supp B.Θ, ∃ C : Y.X.OrientedTameStructure (m + 1) B.Θ y, C.Represents B.T)
    (ω' : Y.epFormsInfty m) :
    X.boundaryMeasureEff hm hLX A.isBranchedEpSubgroupoid hcptA A.isOrientation hlocA
        (formsPullback f m ω') univ =
      Y.boundaryMeasureEff hm hLY B.isBranchedEpSubgroupoid hcptB B.isOrientation hlocB ω'
        univ := by
  subst hAB
  have h := (theorem_11_4_5_pull_loc hf hm hLX hLY B.isBranchedEpSubgroupoid hcptB B.isOrientation
    hlocB ω' (K := univ) MeasurableSet.univ).2
  rw [preimage_image_univ_boundaryTheta hf B.isBranchedEpSubgroupoid] at h
  exact h

/-- **The boundary integral for dimension `1` is invariant under pull-back** (Theorem 11.4.4
for `n = 1`, `K = |supp ∂f^*Θ'|`). -/
theorem boundaryBranchedMeasureDim1_pull_univ {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    (A : OrientedBranched X) (B : OrientedBranched Y) (hAB : OrientedBranched.pull hf B = A)
    (hcptA : X.X.IsCompactBranched A.Θ)
    (hlocA : ∀ x ∈ supp A.Θ, ∃ C : X.X.OrientedTameStructure (0 + 1) A.Θ x, C.Represents A.T)
    (hcptB : Y.X.IsCompactBranched B.Θ)
    (hlocB : ∀ y ∈ supp B.Θ, ∃ C : Y.X.OrientedTameStructure (0 + 1) B.Θ y, C.Represents B.T)
    (ω' : Y.epFormsInfty 0) :
    X.boundaryBranchedMeasureDim1 A.isBranchedEpSubgroupoid hcptA A.isOrientation hlocA
        (formsPullback f 0 ω') univ =
      Y.boundaryBranchedMeasureDim1 B.isBranchedEpSubgroupoid hcptB B.isOrientation hlocB ω'
        univ := by
  subst hAB
  have h := (theorem_11_4_4_pull_dim1 hf B.isBranchedEpSubgroupoid hcptB B.isOrientation hlocB
    ω' (K := univ) MeasurableSet.univ).2
  rw [preimage_image_univ_boundaryTheta hf B.isBranchedEpSubgroupoid] at h
  exact h

/-- **The effective boundary integral for dimension `1` is invariant under pull-back**
(Theorem 11.4.5 for `n = 1`), for ep-groupoids with (LUC). -/
theorem boundaryBranchedMeasureEffDim1_pull_univ {f : of X ⟶ of Y} (hf : IsGeneralizedIso f)
    (hLX : X.X.IsLUC) (hLY : Y.X.IsLUC)
    (A : OrientedBranched X) (B : OrientedBranched Y) (hAB : OrientedBranched.pull hf B = A)
    (hcptA : X.X.IsCompactBranched A.Θ)
    (hlocA : ∀ x ∈ supp A.Θ, ∃ C : X.X.OrientedTameStructure (0 + 1) A.Θ x, C.Represents A.T)
    (hcptB : Y.X.IsCompactBranched B.Θ)
    (hlocB : ∀ y ∈ supp B.Θ, ∃ C : Y.X.OrientedTameStructure (0 + 1) B.Θ y, C.Represents B.T)
    (ω' : Y.epFormsInfty 0) :
    X.boundaryBranchedMeasureEffDim1 A.isBranchedEpSubgroupoid hcptA A.isOrientation
        (X.hloc_hasLUC_dim1 hLX hlocA) (formsPullback f 0 ω') univ =
      Y.boundaryBranchedMeasureEffDim1 B.isBranchedEpSubgroupoid hcptB B.isOrientation
        (Y.hloc_hasLUC_dim1 hLY hlocB) ω' univ := by
  subst hAB
  have h := (theorem_11_4_5_pull_dim1 hf hLX hLY B.isBranchedEpSubgroupoid hcptB B.isOrientation
    hlocB ω' (K := univ) MeasurableSet.univ).2
  rw [preimage_image_univ_boundaryTheta hf B.isBranchedEpSubgroupoid] at h
  exact h

end EPLocalization.EPLoc

namespace GCT.PolyfoldConstruction

open EPLocalization EPLocalization.EPLoc

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {n m : ℕ}

variable (S) in
/-- **An oriented branched ep⁺-subcategory `Θ̂ = (Θ, T̂_Θ)` of `C`** (2021 pp. 820–821), read
through the sc-smooth models: a branched ep⁺-subcategory `Θ` (Definition 17.5.1) with an
orientation `Γ^*T̂_Θ` of `Γ^*Θ = Θ ∘ Γ` on every model `X_Ψ` (Definition 9.3.4), the family
compatible with the canonical generalized isomorphisms: `f_{Ψ,Ψ'}^*(Γ'^*T̂_Θ) = Γ^*T̂_Θ`. -/
structure OrientedSubcategory where
  /-- The branched ep⁺-subcategory `Θ : C → ℚ⁺`. -/
  Θ : C.Obj → ℚ
  isBranched : S.IsBranchedSubcategory Θ
  /-- `Γ_Ψ^*T̂_Θ` on the model of the covering family `Ψ`. -/
  T : ∀ c : S.CoveringFamily, (S.modelEP c.Ψ).Obj → (S.modelEP c.Ψ).X.PObj.OrTangent →₀ ℚ
  isOrientation : ∀ c, (S.modelEP c.Ψ).X.IsOrientation (S.modelPull c.Ψ Θ) (T c)
  pullSection_comparison : ∀ c c', pullSection (S.comparison c c') (T c') = T c

namespace OrientedSubcategory

variable (A : S.OrientedSubcategory)

/-- **`Θ̂_Ψ = (Θ ∘ Γ, Γ^*T̂_Θ)`** (2021 p. 821), the oriented branched ep⁺-subgroupoid of the model
`X_Ψ` (Proposition 17.5.2). -/
def toOriented (c : S.CoveringFamily) : OrientedBranched (S.modelEP c.Ψ) where
  Θ := S.modelPull c.Ψ A.Θ
  T := A.T c
  isBranchedEpSubgroupoid := proposition_17_5_2_two A.isBranched
  hasIndependentTangentSums := hasIndependentTangentSums (X := (S.modelEP c.Ψ).X) _
  isOrientation := A.isOrientation c

/-- **`f^*Θ̂_{Ψ'} = Θ̂_Ψ`** (2021 p. 821, proof of Theorem 17.6.4) for `f = f_{Ψ,Ψ'}`. -/
theorem pull_toOriented (c c' : S.CoveringFamily) :
    OrientedBranched.pull (S.isGeneralizedIso_comparison c c') (A.toOriented c') =
      A.toOriented c :=
  OrientedBranched.ext' (pullTheta_comparison_modelPull (c := c) (c' := c')
    A.isBranched.isFunctorial) (A.pullSection_comparison c c')

/-- `|supp Θ|` compact (Definition 17.5.3 (1)) gives `|supp Θ_Ψ|` compact. -/
theorem isCompactBranched_toOriented (hcpt : C.IsCompactBranched A.Θ) (c : S.CoveringFamily) :
    (S.modelEP c.Ψ).X.IsCompactBranched (A.toOriented c).Θ :=
  (isCompactBranched_iff_model c A.isBranched.isFunctorial).1 hcpt

/-- `Θ̂` is tame and oriented of dimension `n` on the model `X_Ψ`, in the form of Chapter 9
(oriented tame structures describing `Γ^*T̂_Θ` at every point of `supp(Θ ∘ Γ)`). -/
def IsTameOrientedVia (c : S.CoveringFamily) (n : ℕ) : Prop :=
  ∀ x ∈ supp (A.toOriented c).Θ, ∃ D : (S.modelEP c.Ψ).X.OrientedTameStructure n
    (A.toOriented c).Θ x, D.Represents (A.toOriented c).T

/-- **`∫_Θ̂ [ω] := ∫_{Θ̂_Ψ} [ω_Ψ]`** (17.89), computed on the covering family `Ψ`. -/
def integralVia (c : S.CoveringFamily) (hn : 0 < n) (hcpt : C.IsCompactBranched A.Θ)
    (hloc : A.IsTameOrientedVia c n) (ω : S.catFormsInfty n) : ℝ :=
  ((S.modelEP c.Ψ).epFormsInftyEval n).tameBranchedIntegral hn
    (A.toOriented c).isBranchedEpSubgroupoid (A.isCompactBranched_toOriented hcpt c)
    (A.toOriented c).isOrientation hloc (ω.1 c)

/-- **Theorem 17.6.4** (2021 p. 821): `∫_{Θ̂_Ψ} [ω_Ψ]` does not depend on the covering family
`Ψ`, so `∫_Θ̂ [ω]` (17.89) is well defined: `f^*Θ̂_{Ψ'} = Θ̂_Ψ`, `f^*[ω_{Ψ'}] = [ω_Ψ]`, and
Theorem 11.4.1 with `K = |supp Θ|`. -/
theorem theorem_17_6_4 (c c' : S.CoveringFamily) (hn : 0 < n) (hcpt : C.IsCompactBranched A.Θ)
    (hloc : A.IsTameOrientedVia c n) (hloc' : A.IsTameOrientedVia c' n) (ω : S.catFormsInfty n) :
    A.integralVia c hn hcpt hloc ω = A.integralVia c' hn hcpt hloc' ω := by
  unfold integralVia
  rw [← ω.2 c c']
  exact tameBranchedIntegral_pull (S.isGeneralizedIso_comparison c c') hn (A.toOriented c)
    (A.toOriented c') (A.pull_toOriented c c') _ hloc _ hloc' (ω.1 c')

/-- (LUC) for `C` (Definition 17.1.22) gives (LUC) for every model. -/
theorem isLUC_model (hL : S.IsLUC) (c : S.CoveringFamily) : (S.modelEP c.Ψ).X.IsLUC :=
  hL.forall isGenIsoInvariant_isLUC c

/-- **`∮_Θ̂ [ω] := ∮_{Θ̂_Ψ} [ω_Ψ]`** (17.91), for `C` with (LUC). -/
def integralEffVia (hL : S.IsLUC) (c : S.CoveringFamily) (hn : 0 < n)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c n) (ω : S.catFormsInfty n) :
    ℝ :=
  ((S.modelEP c.Ψ).epFormsInftyEval n).tameBranchedIntegralEff hn
    (A.toOriented c).isBranchedEpSubgroupoid (A.isCompactBranched_toOriented hcpt c)
    (A.toOriented c).isOrientation ((S.modelEP c.Ψ).hloc_hasLUC (isLUC_model hL c) hloc) (ω.1 c)

/-- **Theorem 17.6.8** (2021 p. 823): for `C` with (LUC), `∮_{Θ̂_Ψ} [ω_Ψ]` does not depend on the
covering family `Ψ`, so `∮_Θ̂ [ω]` (17.91) is well defined (Theorem 11.4.2). -/
theorem theorem_17_6_8 (hL : S.IsLUC) (c c' : S.CoveringFamily) (hn : 0 < n)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c n)
    (hloc' : A.IsTameOrientedVia c' n) (ω : S.catFormsInfty n) :
    A.integralEffVia hL c hn hcpt hloc ω = A.integralEffVia hL c' hn hcpt hloc' ω := by
  unfold integralEffVia
  rw [← ω.2 c c']
  exact tameBranchedIntegralEff_pull (S.isGeneralizedIso_comparison c c') hn (isLUC_model hL c)
    (isLUC_model hL c') (A.toOriented c) (A.toOriented c') (A.pull_toOriented c c') _ hloc _
    hloc' (ω.1 c')

/-! ### Definition 17.6.5: the boundary `∂Θ` -/

theorem isFunctorial_boundaryTheta_toOriented (c : S.CoveringFamily) :
    (S.modelEP c.Ψ).X.IsFunctorial ((S.modelEP c.Ψ).X.boundaryTheta (A.toOriented c).Θ) :=
  (S.modelEP c.Ψ).X.isFunctorial_boundaryTheta (A.toOriented c).isBranchedEpSubgroupoid
    (A.toOriented c).hasIndependentTangentSums

/-- **`∂Θ := Γ_*(∂(Γ^*Θ))`** (2021 p. 822), computed on the covering family `Ψ`. -/
def boundaryVia (c : S.CoveringFamily) : C.Obj → ℚ :=
  S.modelPush c.Ψ ((S.modelEP c.Ψ).X.boundaryTheta (A.toOriented c).Θ)

/-- **Definition 17.6.5** (2021 p. 822): `∂Θ = Γ_*(∂(Γ^*Θ))` does not depend on the covering
family: `Γ_*(∂Γ^*Θ) = Γ'_* f_*(∂Γ^*Θ) = Γ'_*(∂ f_*Γ^*Θ) = Γ'_*(∂Γ'^*Θ)` (Theorem 11.3.8). -/
theorem definition_17_6_5 (c c' : S.CoveringFamily) : A.boundaryVia c = A.boundaryVia c' := by
  unfold boundaryVia
  rw [modelPush_pushTheta_comparison (c := c) (c' := c')
      (A.isFunctorial_boundaryTheta_toOriented c),
    theorem_11_3_8_push (S.isGeneralizedIso_comparison c c')
      (A.toOriented c).isBranchedEpSubgroupoid (A.toOriented c).hasIndependentTangentSums]
  exact congrArg (fun Θ => S.modelPush c'.Ψ ((S.modelEP c'.Ψ).X.boundaryTheta Θ))
    (pushTheta_comparison_modelPull (c := c) (c' := c') A.isBranched.isFunctorial)

/-- `Γ^*(∂Θ) = ∂(Γ^*Θ)`: the boundary integrals of Theorems 17.6.6 and 17.6.9 are over
`∂(Γ^*Θ̂)`. -/
theorem modelPull_boundaryVia (c : S.CoveringFamily) :
    S.modelPull c.Ψ (A.boundaryVia c) = (S.modelEP c.Ψ).X.boundaryTheta (A.toOriented c).Θ :=
  modelPull_modelPush (A.isFunctorial_boundaryTheta_toOriented c)

/-- `∂Θ` is a functor `C → ℚ⁺`. -/
theorem isFunctorial_boundaryVia (c : S.CoveringFamily) :
    C.toGroupoidStr.IsFunctorial (A.boundaryVia c) :=
  isFunctorial_modelPush (A.isFunctorial_boundaryTheta_toOriented c)

/-! ### Theorems 17.6.6 and 17.6.9: the boundary integrals -/

/-- **`∫_{∂Θ̂} [ω] := ∫_{∂(Γ^*Θ̂)} [ω_Ψ]`** (Theorem 17.6.6), `[ω]` of degree `m ≥ 1`, `Θ̂` of
dimension `m + 1`. -/
def boundaryIntegralVia (c : S.CoveringFamily) (hm : 0 < m) (hcpt : C.IsCompactBranched A.Θ)
    (hloc : A.IsTameOrientedVia c (m + 1)) (ω : S.catFormsInfty m) : ℝ :=
  (S.modelEP c.Ψ).boundaryMeasure hm (A.toOriented c).isBranchedEpSubgroupoid
    (A.isCompactBranched_toOriented hcpt c) (A.toOriented c).isOrientation hloc (ω.1 c) univ

/-- **Theorem 17.6.6** (2021 p. 822): `∫_{∂(Γ^*Θ̂)} [ω_Ψ]` does not depend on the covering
family (Theorem 11.4.4 with `K = |supp ∂Θ|`). -/
theorem theorem_17_6_6 (c c' : S.CoveringFamily) (hm : 0 < m) (hcpt : C.IsCompactBranched A.Θ)
    (hloc : A.IsTameOrientedVia c (m + 1)) (hloc' : A.IsTameOrientedVia c' (m + 1))
    (ω : S.catFormsInfty m) :
    A.boundaryIntegralVia c hm hcpt hloc ω = A.boundaryIntegralVia c' hm hcpt hloc' ω := by
  unfold boundaryIntegralVia
  rw [← ω.2 c c']
  exact boundaryMeasure_pull_univ (S.isGeneralizedIso_comparison c c') hm (A.toOriented c)
    (A.toOriented c') (A.pull_toOriented c c') _ hloc _ hloc' (ω.1 c')

/-- The boundary integral for `Θ̂` of dimension `1` (Theorem 17.6.6 for `n = 1`). -/
def boundaryIntegralDim1Via (c : S.CoveringFamily) (hcpt : C.IsCompactBranched A.Θ)
    (hloc : A.IsTameOrientedVia c (0 + 1)) (ω : S.catFormsInfty 0) : ℝ :=
  (S.modelEP c.Ψ).boundaryBranchedMeasureDim1 (A.toOriented c).isBranchedEpSubgroupoid
    (A.isCompactBranched_toOriented hcpt c) (A.toOriented c).isOrientation hloc (ω.1 c) univ

/-- **Theorem 17.6.6 for `n = 1`**: the boundary integral does not depend on the covering
family. -/
theorem theorem_17_6_6_dim1 (c c' : S.CoveringFamily) (hcpt : C.IsCompactBranched A.Θ)
    (hloc : A.IsTameOrientedVia c (0 + 1)) (hloc' : A.IsTameOrientedVia c' (0 + 1))
    (ω : S.catFormsInfty 0) :
    A.boundaryIntegralDim1Via c hcpt hloc ω = A.boundaryIntegralDim1Via c' hcpt hloc' ω := by
  unfold boundaryIntegralDim1Via
  rw [← ω.2 c c']
  exact boundaryBranchedMeasureDim1_pull_univ (S.isGeneralizedIso_comparison c c')
    (A.toOriented c) (A.toOriented c') (A.pull_toOriented c c') _ hloc _ hloc' (ω.1 c')

/-- **`∮_{∂Θ̂} [ω] := ∮_{∂(Γ^*Θ̂)} [ω_Ψ]`** (Theorem 17.6.9), for `C` with (LUC). -/
def boundaryIntegralEffVia (hL : S.IsLUC) (c : S.CoveringFamily) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c (m + 1))
    (ω : S.catFormsInfty m) : ℝ :=
  (S.modelEP c.Ψ).boundaryMeasureEff hm (isLUC_model hL c) (A.toOriented c).isBranchedEpSubgroupoid
    (A.isCompactBranched_toOriented hcpt c) (A.toOriented c).isOrientation hloc (ω.1 c) univ

/-- **Theorem 17.6.9** (2021 p. 824): for `C` with (LUC), `∮_{∂(Γ^*Θ̂)} [ω_Ψ]` does not depend on
the covering family (Theorem 11.4.5). -/
theorem theorem_17_6_9 (hL : S.IsLUC) (c c' : S.CoveringFamily) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c (m + 1))
    (hloc' : A.IsTameOrientedVia c' (m + 1)) (ω : S.catFormsInfty m) :
    A.boundaryIntegralEffVia hL c hm hcpt hloc ω =
      A.boundaryIntegralEffVia hL c' hm hcpt hloc' ω := by
  unfold boundaryIntegralEffVia
  rw [← ω.2 c c']
  exact boundaryMeasureEff_pull_univ (S.isGeneralizedIso_comparison c c') hm (isLUC_model hL c)
    (isLUC_model hL c') (A.toOriented c) (A.toOriented c') (A.pull_toOriented c c') _ hloc _
    hloc' (ω.1 c')

/-- The effective boundary integral for `Θ̂` of dimension `1` (Theorem 17.6.9 for `n = 1`). -/
def boundaryIntegralEffDim1Via (hL : S.IsLUC) (c : S.CoveringFamily)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c (0 + 1))
    (ω : S.catFormsInfty 0) : ℝ :=
  (S.modelEP c.Ψ).boundaryBranchedMeasureEffDim1 (A.toOriented c).isBranchedEpSubgroupoid
    (A.isCompactBranched_toOriented hcpt c) (A.toOriented c).isOrientation
    ((S.modelEP c.Ψ).hloc_hasLUC_dim1 (isLUC_model hL c) hloc) (ω.1 c) univ

/-- **Theorem 17.6.9 for `n = 1`**. -/
theorem theorem_17_6_9_dim1 (hL : S.IsLUC) (c c' : S.CoveringFamily)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c (0 + 1))
    (hloc' : A.IsTameOrientedVia c' (0 + 1)) (ω : S.catFormsInfty 0) :
    A.boundaryIntegralEffDim1Via hL c hcpt hloc ω =
      A.boundaryIntegralEffDim1Via hL c' hcpt hloc' ω := by
  unfold boundaryIntegralEffDim1Via
  rw [← ω.2 c c']
  exact boundaryBranchedMeasureEffDim1_pull_univ (S.isGeneralizedIso_comparison c c')
    (isLUC_model hL c) (isLUC_model hL c') (A.toOriented c) (A.toOriented c')
    (A.pull_toOriented c c') _ hloc _ hloc' (ω.1 c')

/-! ### Theorems 17.6.7 and 17.6.10: Stokes -/

/-- **Theorem 17.6.7 (Stokes)** (2021 p. 823), `[ω]` of degree `m ≥ 1`, from Stokes on the
ep-groupoid level for the model `X_Ψ` (`EP.StokesWithoutPartitions`, the assertion of
Remark 9.5.19): `∫_Θ̂ d[ω] = ∫_{∂Θ̂} [ω]` ("the statement is equivalent to the ep-groupoid
version"). -/
theorem theorem_17_6_7_of_epStokes (c : S.CoveringFamily)
    (hS : (S.modelEP c.Ψ).StokesWithoutPartitions) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c (m + 1))
    (ω : S.catFormsInfty m) :
    A.integralVia c (Nat.succ_pos m) hcpt hloc (S.catFormsInftyD m ω) =
      A.boundaryIntegralVia c hm hcpt hloc ω :=
  hS.stokes hm _ _ _ hloc (ω.1 c)

/-- **Theorem 17.6.7 (Stokes)**, `m ≥ 1`, with the extra hypothesis `_hyp` that the model `X_Ψ`
admits sc-smooth partitions of unity (Definition 7.5.5; Theorem 9.5.17 assumes them).  Witness:
`z3Model_hasScPartitionsOfUnity` (`CategoryStokesExamples.lean`). -/
theorem theorem_17_6_7_hyp (c : S.CoveringFamily)
    (hPU : (S.modelEP c.Ψ).X.HasScPartitionsOfUnity) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c (m + 1))
    (ω : S.catFormsInfty m) :
    A.integralVia c (Nat.succ_pos m) hcpt hloc (S.catFormsInftyD m ω) =
      A.boundaryIntegralVia c hm hcpt hloc ω :=
  A.theorem_17_6_7_of_epStokes c ((S.modelEP c.Ψ).stokesWithoutPartitions_of_hasScPartitionsOfUnity
    hPU) hm hcpt hloc ω

/-- **Theorem 17.6.7 (Stokes) for `n = 1`**, from Stokes on the ep-groupoid level. -/
theorem theorem_17_6_7_dim1_of_epStokes (c : S.CoveringFamily)
    (hS : (S.modelEP c.Ψ).StokesWithoutPartitions) (hcpt : C.IsCompactBranched A.Θ)
    (hloc : A.IsTameOrientedVia c (0 + 1)) (ω : S.catFormsInfty 0) :
    A.integralVia c (Nat.succ_pos 0) hcpt hloc (S.catFormsInftyD 0 ω) =
      A.boundaryIntegralDim1Via c hcpt hloc ω :=
  hS.stokesDim1 _ _ _ hloc (ω.1 c)

/-- **Theorem 17.6.7 (Stokes) for `n = 1`**, with the extra hypothesis `_hyp` (partitions of unity
on the model). -/
theorem theorem_17_6_7_dim1_hyp (c : S.CoveringFamily)
    (hPU : (S.modelEP c.Ψ).X.HasScPartitionsOfUnity) (hcpt : C.IsCompactBranched A.Θ)
    (hloc : A.IsTameOrientedVia c (0 + 1)) (ω : S.catFormsInfty 0) :
    A.integralVia c (Nat.succ_pos 0) hcpt hloc (S.catFormsInftyD 0 ω) =
      A.boundaryIntegralDim1Via c hcpt hloc ω :=
  A.theorem_17_6_7_dim1_of_epStokes c
    ((S.modelEP c.Ψ).stokesWithoutPartitions_of_hasScPartitionsOfUnity hPU) hcpt hloc ω

/-- **Theorem 17.6.7 on every covering family**: Stokes on the ep-groupoid level for one model
`X_{Ψ₀}` on which `Θ̂` is tame and oriented gives `∫_Θ̂ d[ω] = ∫_{∂Θ̂} [ω]` computed on any `Ψ`
(Theorems 17.6.4 and 17.6.6). -/
theorem theorem_17_6_7_of_epStokes_of_family (c₀ c : S.CoveringFamily)
    (hS : (S.modelEP c₀.Ψ).StokesWithoutPartitions) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (hloc₀ : A.IsTameOrientedVia c₀ (m + 1))
    (hloc : A.IsTameOrientedVia c (m + 1)) (ω : S.catFormsInfty m) :
    A.integralVia c (Nat.succ_pos m) hcpt hloc (S.catFormsInftyD m ω) =
      A.boundaryIntegralVia c hm hcpt hloc ω :=
  (A.theorem_17_6_4 c c₀ _ hcpt hloc hloc₀ _).trans
    ((A.theorem_17_6_7_of_epStokes c₀ hS hm hcpt hloc₀ ω).trans
      (A.theorem_17_6_6 c₀ c hm hcpt hloc₀ hloc ω))

/-- **Theorem 17.6.10 (effective Stokes)** (2021 p. 824), `m ≥ 1`, for `C` with (LUC), from Stokes
on the ep-groupoid level for `X_Ψ`: `∮_Θ̂ d[ω] = ∮_{∂Θ̂} [ω]`. -/
theorem theorem_17_6_10_of_epStokes (hL : S.IsLUC) (c : S.CoveringFamily)
    (hS : (S.modelEP c.Ψ).StokesWithoutPartitions) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c (m + 1))
    (ω : S.catFormsInfty m) :
    A.integralEffVia hL c (Nat.succ_pos m) hcpt hloc (S.catFormsInftyD m ω) =
      A.boundaryIntegralEffVia hL c hm hcpt hloc ω :=
  hS.stokesEff hm (isLUC_model hL c) _ _ _ hloc (ω.1 c)

/-- **Theorem 17.6.10 (effective Stokes)**, `m ≥ 1`, with the extra hypothesis `_hyp`
(partitions of unity on the model). -/
theorem theorem_17_6_10_hyp (hL : S.IsLUC) (c : S.CoveringFamily)
    (hPU : (S.modelEP c.Ψ).X.HasScPartitionsOfUnity) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c (m + 1))
    (ω : S.catFormsInfty m) :
    A.integralEffVia hL c (Nat.succ_pos m) hcpt hloc (S.catFormsInftyD m ω) =
      A.boundaryIntegralEffVia hL c hm hcpt hloc ω :=
  A.theorem_17_6_10_of_epStokes hL c
    ((S.modelEP c.Ψ).stokesWithoutPartitions_of_hasScPartitionsOfUnity hPU) hm hcpt hloc ω

/-- **Theorem 17.6.10 (effective Stokes) for `n = 1`**, from Stokes on the ep-groupoid level. -/
theorem theorem_17_6_10_dim1_of_epStokes (hL : S.IsLUC) (c : S.CoveringFamily)
    (hS : (S.modelEP c.Ψ).StokesWithoutPartitions) (hcpt : C.IsCompactBranched A.Θ)
    (hloc : A.IsTameOrientedVia c (0 + 1)) (ω : S.catFormsInfty 0) :
    A.integralEffVia hL c (Nat.succ_pos 0) hcpt hloc (S.catFormsInftyD 0 ω) =
      A.boundaryIntegralEffDim1Via hL c hcpt hloc ω :=
  hS.stokesEffDim1 _ _ _ _ (ω.1 c)

/-- **Theorem 17.6.10 (effective Stokes) for `n = 1`**, with the extra hypothesis `_hyp`
(partitions of unity on the model). -/
theorem theorem_17_6_10_dim1_hyp (hL : S.IsLUC) (c : S.CoveringFamily)
    (hPU : (S.modelEP c.Ψ).X.HasScPartitionsOfUnity) (hcpt : C.IsCompactBranched A.Θ)
    (hloc : A.IsTameOrientedVia c (0 + 1)) (ω : S.catFormsInfty 0) :
    A.integralEffVia hL c (Nat.succ_pos 0) hcpt hloc (S.catFormsInftyD 0 ω) =
      A.boundaryIntegralEffDim1Via hL c hcpt hloc ω :=
  A.theorem_17_6_10_dim1_of_epStokes hL c
    ((S.modelEP c.Ψ).stokesWithoutPartitions_of_hasScPartitionsOfUnity hPU) hcpt hloc ω

/-! ### Oriented subcategories from one model -/

variable (S) in
/-- **An oriented branched ep⁺-subcategory from an orientation on one model** `X_{Ψ₀}`:
`Γ_Ψ^*T̂_Θ := f_{Ψ,Ψ₀}^* T̂₀` (Theorem 11.3.5). -/
def ofModel (c₀ : S.CoveringFamily) (Θ : C.Obj → ℚ) (hΘ : S.IsBranchedSubcategory Θ)
    (T₀ : (S.modelEP c₀.Ψ).Obj → (S.modelEP c₀.Ψ).X.PObj.OrTangent →₀ ℚ)
    (hT₀ : (S.modelEP c₀.Ψ).X.IsOrientation (S.modelPull c₀.Ψ Θ) T₀) : S.OrientedSubcategory where
  Θ := Θ
  isBranched := hΘ
  T c := pullSection (S.comparison c c₀) T₀
  isOrientation c := by
    have h := theorem_11_3_5_pull (S.isGeneralizedIso_comparison c c₀)
      (proposition_17_5_2_two hΘ) (hasIndependentTangentSums (X := (S.modelEP c₀.Ψ).X) _) hT₀
    rwa [pullTheta_comparison_modelPull (c := c) (c' := c₀) hΘ.isFunctorial] at h
  pullSection_comparison c c' :=
    (pullSection_comp (S.isGeneralizedIso_comparison c c') (S.isGeneralizedIso_comparison c' c₀)
      hT₀.isGrHatSection).symm.trans
      (congrArg (fun f => pullSection f T₀) (S.comparison_comp c c' c₀))

/-- On `X_{Ψ₀}` the orientation of `ofModel` is `T̂₀` (for `T̂₀` vanishing off `X_∞`). -/
theorem ofModel_T_self (c₀ : S.CoveringFamily) (Θ : C.Obj → ℚ) (hΘ : S.IsBranchedSubcategory Θ)
    (T₀ : (S.modelEP c₀.Ψ).Obj → (S.modelEP c₀.Ψ).X.PObj.OrTangent →₀ ℚ)
    (hT₀ : (S.modelEP c₀.Ψ).X.IsOrientation (S.modelPull c₀.Ψ Θ) T₀)
    (hmem : T₀ ∈ (S.modelEP c₀.Ψ).X.GrHatSections) :
    (ofModel S c₀ Θ hΘ T₀ hT₀).T c₀ = T₀ :=
  (congrArg (fun f => pullSection f T₀) (S.comparison_self c₀)).trans (pullSection_id_of_mem hmem)

end OrientedSubcategory

end GCT.PolyfoldConstruction

end Polyfold
