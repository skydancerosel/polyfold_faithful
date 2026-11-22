import Polyfold.Chapter17.CategoryStokes
import Polyfold.Chapter11.MeasureGeneralizedIso
import Polyfold.Chapter9.TameOpen

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.6 (pp. 820–824): "tame, oriented" for an oriented branched ep⁺-subcategory does not depend on
the covering family, and **Theorems 17.6.4, 17.6.6–17.6.10** with that hypothesis on one family
only.  Numbers and pages are the 2021 text's.

# Tame, oriented `Θ̂` on a polyfold `C`

## The text, paraphrased

(pp. 820–821) The integrals of §17.6 are defined for `Θ̂ = (Θ, T̂_Θ)` "tame, oriented" with
`|supp Θ|` compact, a property of `Θ̂` on `C` (tameness of `Θ` is Definition 17.5.3 (2): `Γ^*Θ`
tame for a suitable covering family, and then for every one).  The integral is computed on any
covering family `Ψ` through the model `Γ_Ψ : X_Ψ → C`.

## What is formalized

* `OrientedBranched.exists_tame_pull` (ep-groupoids): for a generalized isomorphism `f : X → Y`,
  oriented tame structures describing `T̂'` at every point of `supp Θ'` give such structures for
  `f^*Θ̂'` (the structures of the proof of Theorem 11.4.1, `hcov_pullTheta`).
* `OrientedSubcategory.isTameOrientedVia_of_family`, **`isTameOrientedVia_iff`**: `Θ̂` is tame and
  oriented of dimension `n` on the model of one covering family iff on the model of every one
  (`f_{Ψ,Ψ'}^*Θ̂_{Ψ'} = Θ̂_Ψ`).
* `OrientedSubcategory.IsTameOriented` (`Θ̂` tame, oriented, of dimension `n`: on the model of some
  covering family), `isTameOriented_iff_forall`, `IsTameOriented.via`.
* `ofModel_isTameOrientedVia`: an oriented subcategory built from one model (`ofModel`) is tame and
  oriented on every family as soon as the orientation on that model is.
* The integrals on `C`, independent of any choice: `integral` ((17.89)), `boundaryIntegral`,
  `boundaryIntegralDim1` (Theorem 17.6.6), `integralEff` ((17.91)), `boundaryIntegralEff`,
  `boundaryIntegralEffDim1` (Theorem 17.6.9), each equal to the integral on any covering family
  (`integral_eq_integralVia`, …).
* The theorems with the hypothesis on one family: **`theorem_17_6_4_book`**,
  **`theorem_17_6_6_book`**, `theorem_17_6_6_dim1_book`, **`theorem_17_6_8_book`**,
  **`theorem_17_6_9_book`**, `theorem_17_6_9_dim1_book` (the integrals on two covering families
  agree when `Θ̂` is tame and oriented on the first); Stokes **`theorem_17_6_7_book`**,
  `theorem_17_6_7_dim1_book`, **`theorem_17_6_10_book`**, `theorem_17_6_10_dim1_book` for the
  integrals on `C`, from the ep-level Stokes assertion `EP.StokesWithoutPartitions` on the model
  of one covering family, and `theorem_17_6_7_book_hyp`, `theorem_17_6_10_book_hyp` from sc-smooth
  partitions of unity on that model.

## Readings

* "Tame, oriented, of dimension `n`" for `Θ̂` on `C` is read as: on the model of a covering family
  every point of `supp(Γ^*Θ)` has an oriented tame structure of dimension `n` describing `Γ^*T̂_Θ`
  (`IsTameOriented`); `isTameOriented_iff_forall` shows that "some family" and "every family"
  agree, as for Definition 17.5.3 (2).
* The integrals on `C` are those on a covering family chosen by `IsTameOriented` (the choice does
  not matter, Theorems 17.6.4, 17.6.6, 17.6.8, 17.6.9).
* The Stokes theorems keep the hypotheses of `CategoryStokes.lean` (ep-level Stokes on one model,
  or sc-smooth partitions of unity on it, Remark 9.5.19).
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory CategoryTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold EPLocalization EPLocalization.EPLoc

namespace EPLocalization.OrientedBranched

variable {X Y : EP.{u}} {n : ℕ}

/-- **Oriented tame structures pass to `f^*Θ̂'`** (2021 pp. 543–544, proof of Theorem 11.4.1): for a
generalized isomorphism `f : X → Y`, if every point of `supp Θ'` has an oriented tame structure of
dimension `n` describing `T̂'`, so does every point of `supp f^*Θ'` for `f^*T̂'`. -/
theorem exists_tame_pull {f : of X ⟶ of Y} (hf : IsGeneralizedIso f) (B : OrientedBranched Y)
    (hB : ∀ y ∈ supp B.Θ, ∃ D : Y.X.OrientedTameStructure n B.Θ y, D.Represents B.T) :
    ∀ x ∈ supp (pull hf B).Θ, ∃ C : X.X.OrientedTameStructure n (pull hf B).Θ x,
      C.Represents (pull hf B).T := fun x hx => by
  obtain ⟨C, -, hC⟩ := (rep f).hcov_pullTheta (isEquivalence_rep_Φ hf)
    (EP.epFormsInftyEval_isPullback (rep f).isEquivalence_F n)
    (EP.epFormsInftyEval_isPullback (isEquivalence_rep_Φ hf) n) B.isBranchedEpSubgroupoid
    B.hasIndependentTangentSums B.isOrientation
    (FormEval.hcov_of_tameOpen (FormEval.tameOpen Y.X) hB) x hx
  exact ⟨C, hC⟩

end EPLocalization.OrientedBranched

namespace GCT.PolyfoldConstruction.OrientedSubcategory

variable {C : GCT.{u}} {S : C.PolyfoldConstruction} {n m : ℕ} (A : S.OrientedSubcategory)

/-! ### Independence of the covering family -/

/-- **"Tame, oriented" passes from one covering family to another**: `Θ̂_Ψ = f_{Ψ,Ψ'}^*Θ̂_{Ψ'}`
(`pull_toOriented`) and oriented tame structures pass to pull-backs. -/
theorem isTameOrientedVia_of_family (c c' : S.CoveringFamily) (h : A.IsTameOrientedVia c' n) :
    A.IsTameOrientedVia c n := by
  have key := OrientedBranched.exists_tame_pull (S.isGeneralizedIso_comparison c c')
    (A.toOriented c') h
  rw [A.pull_toOriented c c'] at key
  exact key

/-- **`Θ̂` is tame and oriented of dimension `n` on one model iff on every model.** -/
theorem isTameOrientedVia_iff (c c' : S.CoveringFamily) :
    A.IsTameOrientedVia c n ↔ A.IsTameOrientedVia c' n :=
  ⟨A.isTameOrientedVia_of_family c' c, A.isTameOrientedVia_of_family c c'⟩

/-- **`Θ̂` is tame, oriented, of dimension `n`** (2021 pp. 820–821): on the model of some covering
family (equivalently of every one, `isTameOriented_iff_forall`). -/
def IsTameOriented (n : ℕ) : Prop := ∃ c : S.CoveringFamily, A.IsTameOrientedVia c n

theorem isTameOriented_iff_forall [Nonempty S.CoveringFamily] :
    A.IsTameOriented n ↔ ∀ c : S.CoveringFamily, A.IsTameOrientedVia c n :=
  ⟨fun ⟨c', h⟩ c => A.isTameOrientedVia_of_family c c' h,
    fun h => ⟨Classical.arbitrary _, h _⟩⟩

variable {A} in
/-- A tame oriented `Θ̂` is tame and oriented on the model of every covering family. -/
theorem IsTameOriented.via (h : A.IsTameOriented n) (c : S.CoveringFamily) :
    A.IsTameOrientedVia c n :=
  A.isTameOrientedVia_of_family c h.choose h.choose_spec

/-- **An oriented subcategory built from one model is tame and oriented on every model** as soon
as the orientation `T̂₀` on that model is described by oriented tame structures of dimension
`n`. -/
theorem ofModel_isTameOrientedVia (c₀ : S.CoveringFamily) (Θ : C.Obj → ℚ)
    (hΘ : S.IsBranchedSubcategory Θ)
    (T₀ : (S.modelEP c₀.Ψ).Obj → (S.modelEP c₀.Ψ).X.PObj.OrTangent →₀ ℚ)
    (hT₀ : (S.modelEP c₀.Ψ).X.IsOrientation (S.modelPull c₀.Ψ Θ) T₀)
    (hloc : ∀ x ∈ supp (S.modelPull c₀.Ψ Θ), ∃ D : (S.modelEP c₀.Ψ).X.OrientedTameStructure n
      (S.modelPull c₀.Ψ Θ) x, D.Represents T₀) (c : S.CoveringFamily) :
    (ofModel S c₀ Θ hΘ T₀ hT₀).IsTameOrientedVia c n := by
  let B : OrientedBranched (S.modelEP c₀.Ψ) :=
    { Θ := S.modelPull c₀.Ψ Θ
      T := T₀
      isBranchedEpSubgroupoid := proposition_17_5_2_two hΘ
      hasIndependentTangentSums := hasIndependentTangentSums (X := (S.modelEP c₀.Ψ).X) _
      isOrientation := hT₀ }
  have hpull : OrientedBranched.pull (S.isGeneralizedIso_comparison c c₀) B =
      (ofModel S c₀ Θ hΘ T₀ hT₀).toOriented c :=
    OrientedBranched.ext' (pullTheta_comparison_modelPull (c := c) (c' := c₀) hΘ.isFunctorial)
      rfl
  have key := OrientedBranched.exists_tame_pull (S.isGeneralizedIso_comparison c c₀) B hloc
  rw [hpull] at key
  exact key

/-- `ofModel` is tame and oriented of dimension `n` (on some, hence every, covering family). -/
theorem ofModel_isTameOriented (c₀ : S.CoveringFamily) (Θ : C.Obj → ℚ)
    (hΘ : S.IsBranchedSubcategory Θ)
    (T₀ : (S.modelEP c₀.Ψ).Obj → (S.modelEP c₀.Ψ).X.PObj.OrTangent →₀ ℚ)
    (hT₀ : (S.modelEP c₀.Ψ).X.IsOrientation (S.modelPull c₀.Ψ Θ) T₀)
    (hloc : ∀ x ∈ supp (S.modelPull c₀.Ψ Θ), ∃ D : (S.modelEP c₀.Ψ).X.OrientedTameStructure n
      (S.modelPull c₀.Ψ Θ) x, D.Represents T₀) :
    (ofModel S c₀ Θ hΘ T₀ hT₀).IsTameOriented n :=
  ⟨c₀, ofModel_isTameOrientedVia c₀ Θ hΘ T₀ hT₀ hloc c₀⟩

/-! ### Theorems 17.6.4, 17.6.6, 17.6.8, 17.6.9 with the hypothesis on one family -/

/-- **Theorem 17.6.4** (2021 p. 821) with the text's hypothesis: for `Θ̂` tame and oriented (on the
model of `Ψ`, hence on every model), `∫_{Θ̂_Ψ} [ω_Ψ] = ∫_{Θ̂_{Ψ'}} [ω_{Ψ'}]`. -/
theorem theorem_17_6_4_book (c c' : S.CoveringFamily) (hn : 0 < n)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c n) (ω : S.catFormsInfty n) :
    A.integralVia c hn hcpt hloc ω =
      A.integralVia c' hn hcpt (A.isTameOrientedVia_of_family c' c hloc) ω :=
  A.theorem_17_6_4 c c' hn hcpt hloc _ ω

/-- **Theorem 17.6.6** (2021 p. 822) with the hypothesis on one family. -/
theorem theorem_17_6_6_book (c c' : S.CoveringFamily) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c (m + 1))
    (ω : S.catFormsInfty m) :
    A.boundaryIntegralVia c hm hcpt hloc ω =
      A.boundaryIntegralVia c' hm hcpt (A.isTameOrientedVia_of_family c' c hloc) ω :=
  A.theorem_17_6_6 c c' hm hcpt hloc _ ω

/-- **Theorem 17.6.6 for `n = 1`** with the hypothesis on one family. -/
theorem theorem_17_6_6_dim1_book (c c' : S.CoveringFamily) (hcpt : C.IsCompactBranched A.Θ)
    (hloc : A.IsTameOrientedVia c (0 + 1)) (ω : S.catFormsInfty 0) :
    A.boundaryIntegralDim1Via c hcpt hloc ω =
      A.boundaryIntegralDim1Via c' hcpt (A.isTameOrientedVia_of_family c' c hloc) ω :=
  A.theorem_17_6_6_dim1 c c' hcpt hloc _ ω

/-- **Theorem 17.6.8** (2021 p. 823) with the hypothesis on one family. -/
theorem theorem_17_6_8_book (hL : S.IsLUC) (c c' : S.CoveringFamily) (hn : 0 < n)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c n) (ω : S.catFormsInfty n) :
    A.integralEffVia hL c hn hcpt hloc ω =
      A.integralEffVia hL c' hn hcpt (A.isTameOrientedVia_of_family c' c hloc) ω :=
  A.theorem_17_6_8 hL c c' hn hcpt hloc _ ω

/-- **Theorem 17.6.9** (2021 p. 824) with the hypothesis on one family. -/
theorem theorem_17_6_9_book (hL : S.IsLUC) (c c' : S.CoveringFamily) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c (m + 1))
    (ω : S.catFormsInfty m) :
    A.boundaryIntegralEffVia hL c hm hcpt hloc ω =
      A.boundaryIntegralEffVia hL c' hm hcpt (A.isTameOrientedVia_of_family c' c hloc) ω :=
  A.theorem_17_6_9 hL c c' hm hcpt hloc _ ω

/-- **Theorem 17.6.9 for `n = 1`** with the hypothesis on one family. -/
theorem theorem_17_6_9_dim1_book (hL : S.IsLUC) (c c' : S.CoveringFamily)
    (hcpt : C.IsCompactBranched A.Θ) (hloc : A.IsTameOrientedVia c (0 + 1))
    (ω : S.catFormsInfty 0) :
    A.boundaryIntegralEffDim1Via hL c hcpt hloc ω =
      A.boundaryIntegralEffDim1Via hL c' hcpt (A.isTameOrientedVia_of_family c' c hloc) ω :=
  A.theorem_17_6_9_dim1 hL c c' hcpt hloc _ ω

/-! ### The integrals on `C` -/

/-- **`∫_Θ̂ [ω]`** (17.89) for `Θ̂` tame, oriented, of dimension `n ≥ 1`, with `|supp Θ|` compact:
the integral on the model of a covering family (any one, `integral_eq_integralVia`). -/
def integral (hn : 0 < n) (hcpt : C.IsCompactBranched A.Θ) (h : A.IsTameOriented n)
    (ω : S.catFormsInfty n) : ℝ :=
  A.integralVia h.choose hn hcpt h.choose_spec ω

theorem integral_eq_integralVia (hn : 0 < n) (hcpt : C.IsCompactBranched A.Θ)
    (h : A.IsTameOriented n) (c : S.CoveringFamily) (hloc : A.IsTameOrientedVia c n)
    (ω : S.catFormsInfty n) : A.integral hn hcpt h ω = A.integralVia c hn hcpt hloc ω :=
  A.theorem_17_6_4 _ c hn hcpt _ hloc ω

/-- **`∫_{∂Θ̂} [ω]`** (Theorem 17.6.6), `[ω]` of degree `m ≥ 1`. -/
def boundaryIntegral (hm : 0 < m) (hcpt : C.IsCompactBranched A.Θ)
    (h : A.IsTameOriented (m + 1)) (ω : S.catFormsInfty m) : ℝ :=
  A.boundaryIntegralVia h.choose hm hcpt h.choose_spec ω

theorem boundaryIntegral_eq_boundaryIntegralVia (hm : 0 < m) (hcpt : C.IsCompactBranched A.Θ)
    (h : A.IsTameOriented (m + 1)) (c : S.CoveringFamily) (hloc : A.IsTameOrientedVia c (m + 1))
    (ω : S.catFormsInfty m) :
    A.boundaryIntegral hm hcpt h ω = A.boundaryIntegralVia c hm hcpt hloc ω :=
  A.theorem_17_6_6 _ c hm hcpt _ hloc ω

/-- **`∫_{∂Θ̂} [ω]` for `Θ̂` of dimension `1`** (Theorem 17.6.6, `n = 1`). -/
def boundaryIntegralDim1 (hcpt : C.IsCompactBranched A.Θ) (h : A.IsTameOriented (0 + 1))
    (ω : S.catFormsInfty 0) : ℝ :=
  A.boundaryIntegralDim1Via h.choose hcpt h.choose_spec ω

theorem boundaryIntegralDim1_eq_boundaryIntegralDim1Via (hcpt : C.IsCompactBranched A.Θ)
    (h : A.IsTameOriented (0 + 1)) (c : S.CoveringFamily) (hloc : A.IsTameOrientedVia c (0 + 1))
    (ω : S.catFormsInfty 0) :
    A.boundaryIntegralDim1 hcpt h ω = A.boundaryIntegralDim1Via c hcpt hloc ω :=
  A.theorem_17_6_6_dim1 _ c hcpt _ hloc ω

/-- **`∮_Θ̂ [ω]`** (17.91), for `C` with (LUC). -/
def integralEff (hL : S.IsLUC) (hn : 0 < n) (hcpt : C.IsCompactBranched A.Θ)
    (h : A.IsTameOriented n) (ω : S.catFormsInfty n) : ℝ :=
  A.integralEffVia hL h.choose hn hcpt h.choose_spec ω

theorem integralEff_eq_integralEffVia (hL : S.IsLUC) (hn : 0 < n)
    (hcpt : C.IsCompactBranched A.Θ) (h : A.IsTameOriented n) (c : S.CoveringFamily)
    (hloc : A.IsTameOrientedVia c n) (ω : S.catFormsInfty n) :
    A.integralEff hL hn hcpt h ω = A.integralEffVia hL c hn hcpt hloc ω :=
  A.theorem_17_6_8 hL _ c hn hcpt _ hloc ω

/-- **`∮_{∂Θ̂} [ω]`** (Theorem 17.6.9), `[ω]` of degree `m ≥ 1`, for `C` with (LUC). -/
def boundaryIntegralEff (hL : S.IsLUC) (hm : 0 < m) (hcpt : C.IsCompactBranched A.Θ)
    (h : A.IsTameOriented (m + 1)) (ω : S.catFormsInfty m) : ℝ :=
  A.boundaryIntegralEffVia hL h.choose hm hcpt h.choose_spec ω

theorem boundaryIntegralEff_eq_boundaryIntegralEffVia (hL : S.IsLUC) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (h : A.IsTameOriented (m + 1)) (c : S.CoveringFamily)
    (hloc : A.IsTameOrientedVia c (m + 1)) (ω : S.catFormsInfty m) :
    A.boundaryIntegralEff hL hm hcpt h ω = A.boundaryIntegralEffVia hL c hm hcpt hloc ω :=
  A.theorem_17_6_9 hL _ c hm hcpt _ hloc ω

/-- **`∮_{∂Θ̂} [ω]` for `Θ̂` of dimension `1`** (Theorem 17.6.9, `n = 1`). -/
def boundaryIntegralEffDim1 (hL : S.IsLUC) (hcpt : C.IsCompactBranched A.Θ)
    (h : A.IsTameOriented (0 + 1)) (ω : S.catFormsInfty 0) : ℝ :=
  A.boundaryIntegralEffDim1Via hL h.choose hcpt h.choose_spec ω

theorem boundaryIntegralEffDim1_eq_boundaryIntegralEffDim1Via (hL : S.IsLUC)
    (hcpt : C.IsCompactBranched A.Θ) (h : A.IsTameOriented (0 + 1)) (c : S.CoveringFamily)
    (hloc : A.IsTameOrientedVia c (0 + 1)) (ω : S.catFormsInfty 0) :
    A.boundaryIntegralEffDim1 hL hcpt h ω = A.boundaryIntegralEffDim1Via hL c hcpt hloc ω :=
  A.theorem_17_6_9_dim1 hL _ c hcpt _ hloc ω

/-! ### Stokes for the integrals on `C` -/

/-- **Theorem 17.6.7 (Stokes)** (2021 p. 823) for the integrals on `C`, `[ω]` of degree `m ≥ 1`:
`∫_Θ̂ d[ω] = ∫_{∂Θ̂} [ω]`, from Stokes on the ep-groupoid level for the model of one covering
family `Ψ₀` (`EP.StokesWithoutPartitions`, Remark 9.5.19). -/
theorem theorem_17_6_7_book (c₀ : S.CoveringFamily)
    (hS : (S.modelEP c₀.Ψ).StokesWithoutPartitions) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (h : A.IsTameOriented (m + 1)) (ω : S.catFormsInfty m) :
    A.integral (Nat.succ_pos m) hcpt h (S.catFormsInftyD m ω) =
      A.boundaryIntegral hm hcpt h ω := by
  rw [A.integral_eq_integralVia _ hcpt h c₀ (h.via c₀),
    A.boundaryIntegral_eq_boundaryIntegralVia hm hcpt h c₀ (h.via c₀)]
  exact A.theorem_17_6_7_of_epStokes c₀ hS hm hcpt (h.via c₀) ω

/-- **Theorem 17.6.7 (Stokes)** for the integrals on `C`, with the extra hypothesis `_hyp` that the
model of one covering family admits sc-smooth partitions of unity. -/
theorem theorem_17_6_7_book_hyp (c₀ : S.CoveringFamily)
    (hPU : (S.modelEP c₀.Ψ).X.HasScPartitionsOfUnity) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (h : A.IsTameOriented (m + 1)) (ω : S.catFormsInfty m) :
    A.integral (Nat.succ_pos m) hcpt h (S.catFormsInftyD m ω) =
      A.boundaryIntegral hm hcpt h ω :=
  A.theorem_17_6_7_book c₀
    ((S.modelEP c₀.Ψ).stokesWithoutPartitions_of_hasScPartitionsOfUnity hPU) hm hcpt h ω

/-- **Theorem 17.6.7 (Stokes) for `n = 1`** for the integrals on `C`. -/
theorem theorem_17_6_7_dim1_book (c₀ : S.CoveringFamily)
    (hS : (S.modelEP c₀.Ψ).StokesWithoutPartitions) (hcpt : C.IsCompactBranched A.Θ)
    (h : A.IsTameOriented (0 + 1)) (ω : S.catFormsInfty 0) :
    A.integral (Nat.succ_pos 0) hcpt h (S.catFormsInftyD 0 ω) =
      A.boundaryIntegralDim1 hcpt h ω := by
  rw [A.integral_eq_integralVia _ hcpt h c₀ (h.via c₀),
    A.boundaryIntegralDim1_eq_boundaryIntegralDim1Via hcpt h c₀ (h.via c₀)]
  exact A.theorem_17_6_7_dim1_of_epStokes c₀ hS hcpt (h.via c₀) ω

/-- **Theorem 17.6.10 (effective Stokes)** (2021 p. 824) for the integrals on `C` with (LUC),
`[ω]` of degree `m ≥ 1`, from Stokes on the ep-groupoid level for the model of one covering
family. -/
theorem theorem_17_6_10_book (hL : S.IsLUC) (c₀ : S.CoveringFamily)
    (hS : (S.modelEP c₀.Ψ).StokesWithoutPartitions) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (h : A.IsTameOriented (m + 1)) (ω : S.catFormsInfty m) :
    A.integralEff hL (Nat.succ_pos m) hcpt h (S.catFormsInftyD m ω) =
      A.boundaryIntegralEff hL hm hcpt h ω := by
  rw [A.integralEff_eq_integralEffVia hL _ hcpt h c₀ (h.via c₀),
    A.boundaryIntegralEff_eq_boundaryIntegralEffVia hL hm hcpt h c₀ (h.via c₀)]
  exact A.theorem_17_6_10_of_epStokes hL c₀ hS hm hcpt (h.via c₀) ω

/-- **Theorem 17.6.10 (effective Stokes)** for the integrals on `C`, with the extra hypothesis
`_hyp` (partitions of unity on the model of one covering family). -/
theorem theorem_17_6_10_book_hyp (hL : S.IsLUC) (c₀ : S.CoveringFamily)
    (hPU : (S.modelEP c₀.Ψ).X.HasScPartitionsOfUnity) (hm : 0 < m)
    (hcpt : C.IsCompactBranched A.Θ) (h : A.IsTameOriented (m + 1)) (ω : S.catFormsInfty m) :
    A.integralEff hL (Nat.succ_pos m) hcpt h (S.catFormsInftyD m ω) =
      A.boundaryIntegralEff hL hm hcpt h ω :=
  A.theorem_17_6_10_book hL c₀
    ((S.modelEP c₀.Ψ).stokesWithoutPartitions_of_hasScPartitionsOfUnity hPU) hm hcpt h ω

/-- **Theorem 17.6.10 (effective Stokes) for `n = 1`** for the integrals on `C`. -/
theorem theorem_17_6_10_dim1_book (hL : S.IsLUC) (c₀ : S.CoveringFamily)
    (hS : (S.modelEP c₀.Ψ).StokesWithoutPartitions) (hcpt : C.IsCompactBranched A.Θ)
    (h : A.IsTameOriented (0 + 1)) (ω : S.catFormsInfty 0) :
    A.integralEff hL (Nat.succ_pos 0) hcpt h (S.catFormsInftyD 0 ω) =
      A.boundaryIntegralEffDim1 hL hcpt h ω := by
  rw [A.integralEff_eq_integralEffVia hL _ hcpt h c₀ (h.via c₀),
    A.boundaryIntegralEffDim1_eq_boundaryIntegralEffDim1Via hL hcpt h c₀ (h.via c₀)]
  exact A.theorem_17_6_10_dim1_of_epStokes hL c₀ hS hcpt (h.via c₀) ω

end GCT.PolyfoldConstruction.OrientedSubcategory

end Polyfold
