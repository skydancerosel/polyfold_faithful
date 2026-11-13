import Polyfold.Chapter11.OrientedStructurePairs

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.4 "Equivalences and Integration", **Theorem 11.4.1** (p. 543; 2017:
Theorem 11.8, p. 396), gap G.131.  Numbers and pages are the 2021 text's.

# The canonical measures along an equivalence

## The text, paraphrased

(Theorem 11.4.1) Let `f : X → Y` be a generalized isomorphism, `Θ̂` on `X` and `Θ̂'` on `Y`
oriented, tame, compact branched ep⁺-subgroupoids of dimension `n`, `ω`, `ω'` sc-differential
`n`-forms.  Then `µ^Θ̂_ω(K) = µ^{f_*Θ̂}_{f_*ω}(|f|(K))` and
`µ^{f^*Θ̂'}_{f^*ω'}(K) = µ^Θ̂'_{ω'}(|f|(K))` for `K ∈ L(|supp Θ|)` resp. `K ∈ L(|supp f^*Θ'|)`.
The proof takes an equivalence `F : X → Y`, open neighbourhoods `U(x)`, `U(F(x))` on which `F` is an
sc-diffeomorphism, both with the properness property and the natural actions, moves the local
branching structure by `F` and compares (11.12) with (11.13); then `G_*F^*` for `X ←F A →G Y`.

## What is formalized

For an equivalence `Φ : X → Y`, evaluations `FX`, `FY` of the forms `Ω`, `Ω'` with
`FX.IsPullback FY Φ P` (`FormEvalPullback.lean`), the measures `µ` of Theorem 9.5.4 for the
integrals `FX.sheetIntegration hn`, `FY.sheetIntegration hn` (`SheetIntegrationConcrete.lean`):

* `move_isNull`, `isMeasureZeroSupp_image`, `isMeasureZeroSupp_preimage`: `|Φ|` and `|Φ|⁻¹` map sets
  of measure zero (Definition 9.5.1) to sets of measure zero; `measurable_suppInv`,
  `measurable_suppMap`: `|Φ| : |supp Φ^*Θ'| → |supp Θ'|` is an isomorphism of the σ-algebras `L`.
* `hcov_pull`, `hcov_push`: the structures describing `Φ^*T̂'`, `Φ_*T̂` with sheets in the class
  (the text's "`F^*Θ̂'`, `F_*Θ̂` are oriented and tame").
* **`measure_pull_core`**: `µ^Θ̂_{Pω'}(K) = µ^Θ̂'_{ω'}(|Φ|(K))` whenever `Θ = Φ^*Θ'` and `T̂'` is
  `T̂` moved by the transport charts (`IsTransported`).
* **`theorem_11_4_1_pull_equiv`**, **`theorem_11_4_1_push_equiv`**: the two identities of
  Theorem 11.4.1 for an equivalence (`Φ_*ω` is any `ω'` with `Φ^*ω' = ω`); and the integrals
  `integral_pull_equiv`, `integral_push_equiv` (`K = |supp|`).
-/

set_option maxSynthPendingDepth 3

open Set Function MeasureTheory

noncomputable section

namespace Polyfold

universe u

open EpGroupoid MPolyfold

/-! ### Null preimages of a moved structure -/

namespace EpGroupoid.OrientedTameStructure

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {n : ℕ}
  {ΩS ΩT : Type*} [AddCommGroup ΩS] [Module ℝ ΩS] [AddCommGroup ΩT] [Module ℝ ΩT]
  {FS : X.FormEval n ΩS} {FT : Y.FormEval n ΩT}
  {Θ : Obj → ℚ} {Θ' : Obj' → ℚ} {x : Obj} {f : Obj → Obj'} {g : Obj' → Obj}
  {W : Set Obj} {W' : Set Obj'}

/-- **A moved structure has null preimages** of `A'` if the original one has null preimages of
`A` and `|f(u)| ∈ A'` implies `|u| ∈ A` on `U(x)`. -/
theorem move_isNull (C : X.OrientedTameStructure n Θ x)
    (hf : X.PObj.IsScDiffeoOn Y.PObj f g W W') (hUW : C.U ⊆ W) {y : Obj'} (hxy : f x = y)
    (hΘ : ∀ u ∈ W, Θ' (f u) = Θ u) (R' : Y.NaturalRep y) (hR' : R'.U = f '' C.U)
    (hP : Y.HasPropernessProperty (f '' C.U)) {A : Set X.OrbitSpace} {A' : Set Y.OrbitSpace}
    (hA : ∀ i, FS.sheetNull.IsNull (C.M i) (C.M i ∩ X.π ⁻¹' A))
    (hAA' : ∀ u ∈ C.U, Y.π (f u) ∈ A' → X.π u ∈ A) (i : C.ι) :
    FT.sheetNull.IsNull ((C.move hf hUW hxy hΘ R' hR' hP).M i)
      ((C.move hf hUW hxy hΘ R' hR' hP).M i ∩ Y.π ⁻¹' A') := by
  rw [FormEval.sheetNull_isNull_iff, move_M_eq]
  have h := (FormEval.sheetNull_isNull_iff.1 (hA i)).image_of_isScDiffeoOn_cross hf
    (fun u hu => hUW (C.subset_U i hu.2))
  refine h.mono ?_
  rintro _ ⟨⟨⟨u, hu, rfl⟩, hπ⟩, -⟩
  exact mem_image_of_mem _ ⟨⟨hu, hAA' u (C.subset_U i hu) hπ⟩, hu⟩

end EpGroupoid.OrientedTameStructure

namespace EpFunctor

variable {Obj Mor Obj' Mor' : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {Φ : EpFunctor X Y} {n : ℕ}
  {Ω Ω' : Type*} [AddCommGroup Ω] [Module ℝ Ω] [AddCommGroup Ω'] [Module ℝ Ω']
  {FX : X.FormEval n Ω} {FY : Y.FormEval n Ω'} {P : Ω' →ₗ[ℝ] Ω}
  {Θ' : Obj' → ℚ} {T : Obj → X.PObj.OrTangent →₀ ℚ} {T' : Obj' → Y.PObj.OrTangent →₀ ℚ}

open OrientedTameStructure

/-! ### Transport charts at the points of the support -/

/-- Every `y ∈ supp Θ'` has a transport chart from some `x ∈ supp Φ^*Θ'`. -/
theorem exists_transportChart_of_mem_supp (hΦ : Φ.IsEquivalence) (hΘ' : Y.IsFunctorial Θ')
    {y : Obj'} (hy : y ∈ supp Θ') :
    ∃ x, x ∈ supp (Φ.pullbackTheta Θ') ∧ Nonempty (Φ.TransportChart x y) := by
  obtain ⟨q, hq⟩ := hΦ.isHomeomorph_orbitMap.surjective (Y.π y)
  obtain ⟨x, rfl⟩ := X.surjective_π q
  rw [Φ.orbitMap_π] at hq
  obtain ⟨φ, hs, ht⟩ := Y.π_eq_π_iff.1 hq
  obtain ⟨Tc, -⟩ := exists_transportChart hΦ.isLocalScDiffeo_obj hs ht
  refine ⟨x, ?_, ⟨Tc⟩⟩
  change 0 < Θ' (Φ.obj x)
  rw [← hs, hΘ' φ, ht]
  exact hy

/-- **`T̂'` is `T̂` moved by the transport charts**: `T̂'(Q u) = TQ_* T̂(u)` on `W ∩ X_∞` for every
transport chart `Q : W → W'` of `Φ`.  Instances: `(Φ^*T̂', T̂')` (`isTransported_pull`) and
`(T̂, Φ_*T̂)` (`isTransported_push`). -/
def IsTransported (Φ : EpFunctor X Y) (T : Obj → X.PObj.OrTangent →₀ ℚ)
    (T' : Obj' → Y.PObj.OrTangent →₀ ℚ) : Prop :=
  ∀ {x : Obj} {y : Obj'} (Tc : Φ.TransportChart x y), ∀ u ∈ Tc.W, u ∈ X.PObj.smoothSet →
    T' (Tc.Q u) = (T u).mapDomain (OrTangent.map (tangentMapOn Tc.isScDiffeoOn_Q.isScSmoothOn))

theorem isTransported_pull (hΦ : Φ.IsEquivalence) (hT' : Y.IsGrHatSection T') :
    Φ.IsTransported (Φ.pullSection T') T' := fun Tc =>
  Tc.pullSection_Q hΦ.isLocalScDiffeo_obj hT'

theorem isTransported_push (hΦ : Φ.IsEquivalence) (hT : X.IsGrHatSection T) :
    Φ.IsTransported T (Φ.pushSection T) := fun Tc => Tc.pushSection_Q hΦ hT

/-- **The pulled-back structures**: a structure at `y` restricted to `Q(U(x))` and moved to `x`,
with all its data. -/
def IsPulled (FY : Y.FormEval n Ω') (Φ : EpFunctor X Y) (hΘ' : Y.IsFunctorial Θ')
    (T' : Obj' → Y.PObj.OrTangent →₀ ℚ) {x : Obj}
    (C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x) : Prop :=
  ∃ (y : Obj') (Tc : Φ.TransportChart x y) (D : Y.OrientedTameStructure n Θ' y)
    (_ : ∀ i, D.M i ∈ FY.sheets) (_ : D.Represents T') (R : X.NaturalRep x) (R' : Y.NaturalRep y)
    (h1 : R'.U ⊆ D.U) (h2 : R.U ⊆ Tc.W) (h3 : R'.U = Tc.Q '' R.U)
    (h4 : X.HasPropernessProperty R.U),
    C = pullStructure Tc (Tc.pullbackTheta_Q hΘ') D R R' h1 h2 h3 h4

/-- Every point of `supp Φ^*Θ'` carries a pulled-back structure. -/
theorem exists_isPulled (hΦ : Φ.IsEquivalence) (hΘ' : Y.IsFunctorial Θ')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T')
    {x : Obj} (hx : x ∈ supp (Φ.pullbackTheta Θ')) :
    ∃ C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x, IsPulled FY Φ hΘ' T' C := by
  obtain ⟨Tc⟩ := TransportChart.nonempty hΦ x
  obtain ⟨D, hDS, hDT⟩ := hcov' _ hx
  obtain ⟨R, R', h1, h2, h3, h4⟩ := exists_pullData hΦ Tc D
  exact ⟨_, _, Tc, D, hDS, hDT, R, R', h1, h2, h3, h4, rfl⟩

theorem IsPulled.mem_sheets (hP : FX.IsPullback FY Φ P) {hΘ' : Y.IsFunctorial Θ'} {x : Obj}
    {C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x} (hC : IsPulled FY Φ hΘ' T' C) :
    ∀ i, C.M i ∈ FX.sheets := by
  obtain ⟨y, Tc, D, hDS, hDT, R, R', h1, h2, h3, h4, rfl⟩ := hC
  exact pullStructure_mem_sheets Tc _ D R R' h1 h2 h3 h4 hP hDS

theorem IsPulled.represents (hΦ : Φ.IsEquivalence) {hΘ' : Y.IsFunctorial Θ'} {x : Obj}
    (hT : X.IsGrHatSection T) (hTT : Φ.IsTransported T T')
    {C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x} (hC : IsPulled FY Φ hΘ' T' C) :
    C.Represents T := by
  obtain ⟨y, Tc, D, hDS, hDT, R, R', h1, h2, h3, h4, rfl⟩ := hC
  exact represents_pullStructure Tc _ D R R' h1 h2 h3 h4 hΦ hT (hTT Tc) hDT

/-- **`Φ^*Θ̂'` is oriented and tame with sheets in the class** (the covering hypothesis of
Theorem 9.5.4 for `Φ^*Θ̂'`). -/
theorem hcov_pull (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P) (hΘ' : Y.IsFunctorial Θ')
    (hT : X.IsGrHatSection T) (hTT : Φ.IsTransported T T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T') :
    ∀ x ∈ supp (Φ.pullbackTheta Θ'), ∃ C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T := fun x hx => by
  obtain ⟨C, hC⟩ := exists_isPulled hΦ hΘ' hcov' hx
  exact ⟨C, hC.mem_sheets hP, hC.represents hΦ hT hTT⟩

/-- **`Φ_*Θ̂` is oriented and tame with sheets in the class** (the covering hypothesis of
Theorem 9.5.4 for `Φ_*Θ̂`). -/
theorem hcov_push (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P) {Θ : Obj → ℚ}
    (hΘ : X.IsFunctorial Θ) (hTT : Φ.IsTransported T T')
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T) :
    ∀ y ∈ supp (Φ.pushforwardTheta Θ), ∃ D : Y.OrientedTameStructure n (Φ.pushforwardTheta Θ) y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T' := fun y hy => by
  have hΘ' := isFunctorial_pushforwardTheta hΦ.full hΘ
  have he := pullbackTheta_pushforwardTheta hΦ.full hΘ
  obtain ⟨x, hx, ⟨Tc⟩⟩ := exists_transportChart_of_mem_supp hΦ hΘ' hy
  rw [he] at hx
  obtain ⟨C, hCS, hCT⟩ := hcov x hx
  have hΘQ : ∀ u ∈ Tc.W, Φ.pushforwardTheta Θ (Tc.Q u) = Θ u := fun u hu => by
    rw [Tc.pullbackTheta_Q hΘ' u hu, he]
  exact exists_push_structure hΦ hP Tc hΘQ (hTT Tc) C hCS hCT

/-! ### `|Φ|` and the sets of measure zero -/

theorem hasTameSheetsIn_of_hcov {Z ZM : Type u} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] [TopologicalSpace ZM] [T2Space ZM] [ParacompactSpace ZM]
    {E : EpGroupoid Z ZM} {S : Set (Set Z)} {Θ : Z → ℚ} {TE : Z → E.PObj.OrTangent →₀ ℚ}
    (hcov : ∀ x ∈ supp Θ, ∃ C : E.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ S) ∧ C.Represents TE) : E.HasTameSheetsIn S Θ := fun x hx => by
  obtain ⟨C, hC, -⟩ := hcov x hx
  exact ⟨C.toTameBranchingStructure, hC⟩

/-- **`|Φ|` maps sets of measure zero to sets of measure zero** (Definition 9.5.1). -/
theorem isMeasureZeroSupp_image (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hΘ' : Y.IsFunctorial Θ') (hTSX : X.HasTameSheetsIn FX.sheets (Φ.pullbackTheta Θ'))
    (hTSY : Y.HasTameSheetsIn FY.sheets Θ')
    (hcovX : ∀ x ∈ supp (Φ.pullbackTheta Θ'),
      ∃ C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x, ∀ i, C.M i ∈ FX.sheets)
    {N : Set X.OrbitSpace} (hN : X.IsMeasureZeroSupp FX.sheetNull (Φ.pullbackTheta Θ') N) :
    Y.IsMeasureZeroSupp FY.sheetNull Θ' (Φ.orbitMap '' N) := by
  refine ((lemma_9_5_2 FY.sheetNull hTSY _).1).2 fun y hy => ?_
  have hall := (lemma_9_5_2 FX.sheetNull hTSX N).2.1 ((lemma_9_5_2 FX.sheetNull hTSX N).1.1 hN)
  obtain ⟨x, hx, ⟨Tc⟩⟩ := exists_transportChart_of_mem_supp hΦ hΘ' hy
  obtain ⟨C, hCS⟩ := hcovX x hx
  obtain ⟨V', hyV', hV'P⟩ := Y.exists_hasPropernessProperty y
  obtain ⟨R, R', hRC, hRW, hRV', hR'⟩ := Tc.exists_rep_push hΦ C.rep hV'P.1 hyV'
  have hRU : R.U ⊆ C.U := C.U_eq ▸ hRC
  set C₁ := C.restrictRep R hRU
  have hP' : Y.HasPropernessProperty (Tc.Q '' C₁.U) := hV'P.mono (hR' ▸ R'.isOpen_U) hRV'
  have hΘQ := Tc.pullbackTheta_Q hΘ'
  refine ⟨(C₁.move Tc.isScDiffeoOn_Q hRW Tc.Q_self hΘQ R' hR' hP').toLocalBranchingStructure,
    fun i => ?_, fun i => ?_⟩
  · exact FormEval.image_mem_sheets_cross Tc.isScDiffeoOn_Q
      (FormEval.inter_mem_sheets (C.restrictRep_mem_sheets R hRU hCS i) Tc.isOpen_W)
      inter_subset_right fun ω' => ⟨P ω', Tc.evCompatOn_Q hP ω'
        ((C₁.isSmoothSubmanifold i).inter_isOpen Tc.isOpen_W) inter_subset_right⟩
  · refine C₁.move_isNull Tc.isScDiffeoOn_Q hRW Tc.Q_self hΘQ R' hR' hP'
      (fun i => hall x hx C₁.toLocalBranchingStructure (C.restrictRep_mem_sheets R hRU hCS) i)
      ?_ i
    rintro u hu ⟨q, hq, he⟩
    rw [Tc.π_Q (hRW hu), ← Φ.orbitMap_π] at he
    rw [← Φ.injective_orbitMap_of_full hΦ.full he]
    exact hq

/-- **`|Φ|⁻¹` maps sets of measure zero to sets of measure zero** (Definition 9.5.1). -/
theorem isMeasureZeroSupp_preimage (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hΘ' : Y.IsFunctorial Θ') (hTSX : X.HasTameSheetsIn FX.sheets (Φ.pullbackTheta Θ'))
    (hTSY : Y.HasTameSheetsIn FY.sheets Θ')
    (hcovY : ∀ y ∈ supp Θ', ∃ D : Y.OrientedTameStructure n Θ' y, ∀ i, D.M i ∈ FY.sheets)
    {N' : Set Y.OrbitSpace} (hN : Y.IsMeasureZeroSupp FY.sheetNull Θ' N') :
    X.IsMeasureZeroSupp FX.sheetNull (Φ.pullbackTheta Θ') (Φ.orbitMap ⁻¹' N') := by
  refine ((lemma_9_5_2 FX.sheetNull hTSX _).1).2 fun x hx => ?_
  have hall := (lemma_9_5_2 FY.sheetNull hTSY N').2.1 ((lemma_9_5_2 FY.sheetNull hTSY N').1.1 hN)
  obtain ⟨Tc⟩ := TransportChart.nonempty hΦ x
  obtain ⟨D, hDS⟩ := hcovY _ hx
  obtain ⟨R, R', h1, h2, h3, h4⟩ := exists_pullData hΦ Tc D
  have hΘQ := Tc.pullbackTheta_Q hΘ'
  refine ⟨(pullStructure Tc hΘQ D R R' h1 h2 h3 h4).toLocalBranchingStructure,
    pullStructure_mem_sheets Tc hΘQ D R R' h1 h2 h3 h4 hP hDS, fun i => ?_⟩
  refine (D.restrictRep R' h1).move_isNull Tc.isScDiffeoOn_Q.symm _ _ _ _ _ _
    (fun i => hall _ hx _ (D.restrictRep_mem_sheets R' h1 hDS) i) ?_ i
  intro z hz h
  have hzW' := restrictRep_U_subset_W' Tc D R R' h1 h2 h3 hz
  have hgz := Tc.isScDiffeoOn_Q.mapsTo_inv hzW'
  rw [mem_preimage, Φ.orbitMap_π, ← Tc.π_Q hgz, Tc.isScDiffeoOn_Q.right_inv z hzW'] at h
  exact h

/-! ### `|Φ|` on the supports and the σ-algebras `L` -/

/-- `|Φ|` maps `|supp Φ^*Θ'|` onto `|supp Θ'|`. -/
theorem orbitMap_mem_orbitSupp (hΘ' : Y.IsFunctorial Θ') {p : X.OrbitSpace}
    (hp : p ∈ X.orbitSupp (Φ.pullbackTheta Θ')) : Φ.orbitMap p ∈ Y.orbitSupp Θ' := by
  rw [orbitSupp_pullbackTheta Φ hΘ'] at hp
  exact hp

/-- **`|Φ| : |supp Φ^*Θ'| → |supp Θ'|`.** -/
def suppMap (hΘ' : Y.IsFunctorial Θ') :
    X.orbitSupp (Φ.pullbackTheta Θ') → Y.orbitSupp Θ' :=
  fun q => ⟨Φ.orbitMap q.1, orbitMap_mem_orbitSupp hΘ' q.2⟩

/-- **`|Φ|⁻¹ : |supp Θ'| → |supp Φ^*Θ'|`.** -/
def suppInv (hΦ : Φ.IsEquivalence) (hΘ' : Y.IsFunctorial Θ') :
    Y.orbitSupp Θ' → X.orbitSupp (Φ.pullbackTheta Θ') :=
  fun q' => ⟨(IsHomeomorph.homeomorph _ hΦ.isHomeomorph_orbitMap).symm q'.1, by
    rw [orbitSupp_pullbackTheta Φ hΘ', mem_preimage]
    have h : Φ.orbitMap ((IsHomeomorph.homeomorph _ hΦ.isHomeomorph_orbitMap).symm q'.1) = q'.1 :=
      (IsHomeomorph.homeomorph _ hΦ.isHomeomorph_orbitMap).apply_symm_apply q'.1
    rw [h]; exact q'.2⟩

theorem orbitMap_suppInv (hΦ : Φ.IsEquivalence) (hΘ' : Y.IsFunctorial Θ')
    (q' : Y.orbitSupp Θ') : Φ.orbitMap (suppInv hΦ hΘ' q').1 = q'.1 :=
  (IsHomeomorph.homeomorph _ hΦ.isHomeomorph_orbitMap).apply_symm_apply q'.1

theorem suppInv_eq_iff (hΦ : Φ.IsEquivalence) (hΘ' : Y.IsFunctorial Θ')
    (q' : Y.orbitSupp Θ') (q : X.orbitSupp (Φ.pullbackTheta Θ')) :
    suppInv hΦ hΘ' q' = q ↔ Φ.orbitMap q.1 = q'.1 := by
  constructor
  · rintro rfl; exact orbitMap_suppInv hΦ hΘ' q'
  · intro h
    apply Subtype.ext
    exact (IsHomeomorph.homeomorph _ hΦ.isHomeomorph_orbitMap).symm_apply_eq.2 h.symm

/-- **`|Φ|(K)`** for `K ⊆ |supp Φ^*Θ'|`, as a subset of `|supp Θ'|`. -/
theorem val_image_preimage {Θ : Obj → ℚ} (hΘ : X.orbitSupp Θ ⊆ Φ.orbitMap ⁻¹' Y.orbitSupp Θ')
    (K : Set (X.orbitSupp Θ)) :
    Subtype.val '' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K)) : Set (Y.orbitSupp Θ')) =
      Φ.orbitMap '' (Subtype.val '' K) := by
  refine image_preimage_eq_of_subset ?_
  rintro _ ⟨p, ⟨q, -, rfl⟩, rfl⟩
  exact ⟨⟨_, hΘ q.2⟩, rfl⟩

theorem preimage_suppInv (hΦ : Φ.IsEquivalence) (hΘ' : Y.IsFunctorial Θ')
    (K : Set (X.orbitSupp (Φ.pullbackTheta Θ'))) :
    suppInv hΦ hΘ' ⁻¹' K = Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K)) := by
  ext q'
  constructor
  · intro h
    exact ⟨_, ⟨_, h, rfl⟩, orbitMap_suppInv hΦ hΘ' q'⟩
  · rintro ⟨p, ⟨q, hq, rfl⟩, he⟩
    rw [mem_preimage, (suppInv_eq_iff hΦ hΘ' q' q).2 he]
    exact hq

theorem continuous_suppInv (hΦ : Φ.IsEquivalence) (hΘ' : Y.IsFunctorial Θ') :
    Continuous (suppInv hΦ hΘ') :=
  ((IsHomeomorph.homeomorph _ hΦ.isHomeomorph_orbitMap).symm.continuous.comp
    continuous_subtype_val).subtype_mk _

theorem continuous_suppMap (hΘ' : Y.IsFunctorial Θ') : Continuous (suppMap (Φ := Φ) hΘ') :=
  (Φ.continuous_orbitMap.comp continuous_subtype_val).subtype_mk _

/-- **`|Φ|⁻¹` is measurable for the σ-algebras `L`** (Definition 9.5.3): `|Φ|` maps `L(S)` into
`L(S')`. -/
theorem measurable_suppInv (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hΘ' : Y.IsFunctorial Θ') (hTSX : X.HasTameSheetsIn FX.sheets (Φ.pullbackTheta Θ'))
    (hTSY : Y.HasTameSheetsIn FY.sheets Θ')
    (hcovX : ∀ x ∈ supp (Φ.pullbackTheta Θ'),
      ∃ C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x, ∀ i, C.M i ∈ FX.sheets) :
    @Measurable _ _ (Y.lebesgueSigma FY.sheetNull Θ')
      (X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ')) (suppInv hΦ hΘ') := by
  let _ : MeasurableSpace (Y.orbitSupp Θ') := Y.lebesgueSigma FY.sheetNull Θ'
  refine measurable_generateFrom fun t ht => ?_
  rcases ht with ht | ht
  · exact borel_le_borelNullSigma _ _ ((continuous_suppInv hΦ hΘ').borel_measurable ht)
  · refine measurableSet_borelNullSigma_of_mem ?_
    change Y.IsMeasureZeroSupp FY.sheetNull Θ' _
    rw [preimage_suppInv, val_image_preimage (fun p hp => orbitMap_mem_orbitSupp hΘ' hp)]
    exact isMeasureZeroSupp_image hΦ hP hΘ' hTSX hTSY hcovX ht

theorem preimage_suppMap (hΘ' : Y.IsFunctorial Θ') (t : Set (Y.orbitSupp Θ')) :
    Subtype.val '' (suppMap (Φ := Φ) hΘ' ⁻¹' t) = Φ.orbitMap ⁻¹' (Subtype.val '' t) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨_, hq, rfl⟩
  · rintro ⟨q', hq', he⟩
    have hp : p ∈ X.orbitSupp (Φ.pullbackTheta Θ') := by
      rw [orbitSupp_pullbackTheta Φ hΘ', mem_preimage, ← he]; exact q'.2
    refine ⟨⟨p, hp⟩, ?_, rfl⟩
    change (⟨Φ.orbitMap p, _⟩ : Y.orbitSupp Θ') ∈ t
    convert hq' using 1
    exact Subtype.ext he.symm

/-- **`|Φ|` is measurable for the σ-algebras `L`** (Definition 9.5.3). -/
theorem measurable_suppMap (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hΘ' : Y.IsFunctorial Θ') (hTSX : X.HasTameSheetsIn FX.sheets (Φ.pullbackTheta Θ'))
    (hTSY : Y.HasTameSheetsIn FY.sheets Θ')
    (hcovY : ∀ y ∈ supp Θ', ∃ D : Y.OrientedTameStructure n Θ' y, ∀ i, D.M i ∈ FY.sheets) :
    @Measurable _ _ (X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ'))
      (Y.lebesgueSigma FY.sheetNull Θ') (suppMap (Φ := Φ) hΘ') := by
  let _ : MeasurableSpace (X.orbitSupp (Φ.pullbackTheta Θ')) :=
    X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ')
  refine measurable_generateFrom fun t ht => ?_
  rcases ht with ht | ht
  · exact borel_le_borelNullSigma _ _ ((continuous_suppMap hΘ').borel_measurable ht)
  · refine measurableSet_borelNullSigma_of_mem ?_
    change X.IsMeasureZeroSupp FX.sheetNull _ _
    rw [preimage_suppMap]
    exact isMeasureZeroSupp_preimage hΦ hP hΘ' hTSX hTSY hcovY ht

/-! ### Theorem 11.4.1 for an equivalence -/

/-- `|Φ|(|supp Φ^*Θ'|) = |supp Θ'|`. -/
theorem image_univ_eq_univ (hΦ : Φ.IsEquivalence) (hΘ' : Y.IsFunctorial Θ') {Θ : Obj → ℚ}
    (hΘeq : Φ.pullbackTheta Θ' = Θ) :
    (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' (univ : Set (X.orbitSupp Θ)))) :
      Set (Y.orbitSupp Θ')) = univ := by
  subst hΘeq
  refine eq_univ_of_forall fun q' => ?_
  obtain ⟨p, hp⟩ := hΦ.isHomeomorph_orbitMap.surjective q'.1
  have hps : p ∈ X.orbitSupp (Φ.pullbackTheta Θ') := by
    rw [orbitSupp_pullbackTheta Φ hΘ', mem_preimage, hp]; exact q'.2
  exact ⟨p, ⟨⟨p, hps⟩, mem_univ _, rfl⟩, hp⟩

/-- **The core of Theorem 11.4.1, 2021 p. 543 (2017: Theorem 11.8)**: for an equivalence `Φ`,
`Θ = Φ^*Θ'`, `T̂'` the orientation `T̂` moved by the transport charts, and the pull-back `P` of
the forms, `|Φ|` maps `L(|supp Θ|)` into `L(|supp Θ'|)` and
`µ^Θ̂_{Pω'}(K) = µ^Θ̂'_{ω'}(|Φ|(K))`. -/
theorem measure_pull_core (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P) (hn : 0 < n)
    (hΘ' : Y.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.IsCompactBranched Θ')
    (hT' : Y.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T')
    {Θ : Obj → ℚ} (hΘeq : Φ.pullbackTheta Θ' = Θ) (hΘ : X.IsBranchedEpSubgroupoid Θ)
    (hcpt : X.IsCompactBranched Θ) (hT : X.IsOrientation Θ T) (hTT : Φ.IsTransported T T')
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T)
    (ω' : Ω') {K : Set (X.orbitSupp Θ)} (hK : MeasurableSet[X.lebesgueSigma FX.sheetNull Θ] K) :
    MeasurableSet[Y.lebesgueSigma FY.sheetNull Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      branchedMeasure (FX.sheetIntegration hn) hΘ hcpt hT hcov (P ω') K =
        branchedMeasure (FY.sheetIntegration hn) hΘ' hcpt' hT' hcov' ω'
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := by
  subst hΘeq
  have hΘf := hΘ'.isFunctorial
  have hTSX : X.HasTameSheetsIn FX.sheets (Φ.pullbackTheta Θ') := hasTameSheetsIn_of_hcov hcov
  have hTSY : Y.HasTameSheetsIn FY.sheets Θ' := hasTameSheetsIn_of_hcov hcov'
  have hcovX : ∀ x ∈ supp (Φ.pullbackTheta Θ'),
      ∃ C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x, ∀ i, C.M i ∈ FX.sheets :=
    fun x hx => let ⟨C, hC, _⟩ := hcov x hx; ⟨C, hC⟩
  have hm := measurable_suppInv hΦ hP hΘf hTSX hTSY hcovX
  have hmeas : ∀ K : Set (X.orbitSupp (Φ.pullbackTheta Θ')),
      MeasurableSet[X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ')] K →
      MeasurableSet[Y.lebesgueSigma FY.sheetNull Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := fun K hK => by
    rw [← preimage_suppInv hΦ hΘf K]; exact hm hK
  refine ⟨hmeas K hK, ?_⟩
  let _ : MeasurableSpace (X.orbitSupp (Φ.pullbackTheta Θ')) :=
    X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ')
  let _ : MeasurableSpace (Y.orbitSupp Θ') := Y.lebesgueSigma FY.sheetNull Θ'
  have : CompactSpace (X.orbitSupp (Φ.pullbackTheta Θ')) := isCompact_iff_compactSpace.1 hcpt
  set μ₁ := branchedMeasure (FX.sheetIntegration hn) hΘ hcpt hT hcov (P ω')
  set μY := branchedMeasure (FY.sheetIntegration hn) hΘ' hcpt' hT' hcov' ω'
  set μ₂ : SignedMeasure (X.orbitSupp (Φ.pullbackTheta Θ')) := μY.map (suppInv hΦ hΘf)
  have hμ₂ : ∀ K, MeasurableSet K →
      μ₂ K = μY (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := fun K hK => by
    rw [VectorMeasure.map_apply _ hm hK, preimage_suppInv]
  -- the local agreement on a pulled-back structure: (11.12) = (11.13)
  have hloc : ∀ {x : Obj} (C : X.OrientedTameStructure n (Φ.pullbackTheta Θ') x),
      IsPulled FY Φ hΘf T' C → ∀ K, MeasurableSet K → Subtype.val '' K ⊆ X.π '' C.U →
      μ₂ K = μ₁ K := by
    intro x C hC K hK hKU
    have hS := hC.mem_sheets hP
    have hR := hC.represents hΦ hT.isGrHatSection hTT
    obtain ⟨y, Tc, D, hDS, hDT, R, R', h1, h2, h3, h4, rfl⟩ := hC
    have hval := val_image_preimage (Θ' := Θ') (Φ := Φ)
      (fun p hp => orbitMap_mem_orbitSupp hΘf hp) K
    have hD'S := D.restrictRep_mem_sheets R' h1 hDS
    have hK' := hmeas K hK
    have hKU' : Subtype.val '' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K)) :
        Set (Y.orbitSupp Θ')) ⊆ Y.π '' (D.restrictRep R' h1).U := by
      rw [hval, restrictRep_U, h3]
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨u, hu, hπ⟩ := hKU hp
      rw [pullStructure_U] at hu
      exact ⟨Tc.Q u, mem_image_of_mem _ hu, by rw [Tc.π_Q (h2 hu), ← Φ.orbitMap_π, hπ]⟩
    have hW' : ∀ {z}, z ∈ (D.restrictRep R' h1).U → z ∈ Tc.W' := fun hz =>
      restrictRep_U_subset_W' Tc D R R' h1 h2 h3 hz
    have hA := (D.restrictRep R' h1).isMeas_preimage hTSY hD'S hK'
    have hB : ∀ i, X.π ⁻¹' (Subtype.val '' K) ∩ Tc.Qinv '' (D.restrictRep R' h1).M i =
        Tc.Qinv '' (Y.π ⁻¹' (Subtype.val '' (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K)) :
          Set (Y.orbitSupp Θ'))) ∩ (D.restrictRep R' h1).M i) := by
      intro i
      ext u
      constructor
      · rintro ⟨hu, z, hz, rfl⟩
        have hzW' := hW' ((D.restrictRep R' h1).subset_U i hz)
        refine ⟨z, ⟨?_, hz⟩, rfl⟩
        rw [mem_preimage, hval]
        refine ⟨_, hu, ?_⟩
        rw [Φ.orbitMap_π, ← Tc.π_Q (Tc.isScDiffeoOn_Q.mapsTo_inv hzW'),
          Tc.isScDiffeoOn_Q.right_inv z hzW']
      · rintro ⟨z, ⟨hzA, hz⟩, rfl⟩
        have hzW' := hW' ((D.restrictRep R' h1).subset_U i hz)
        refine ⟨?_, z, hz, rfl⟩
        rw [mem_preimage, hval] at hzA
        obtain ⟨p, hp, he⟩ := hzA
        rw [← Tc.isScDiffeoOn_Q.right_inv z hzW', Tc.π_Q (Tc.isScDiffeoOn_Q.mapsTo_inv hzW'),
          ← Φ.orbitMap_π] at he
        rw [mem_preimage, ← Φ.injective_orbitMap_of_full hΦ.full he]
        exact hp
    have e := (D.restrictRep R' h1).sheetSum_move (FS := FY) (FT := FX) hn
      Tc.isScDiffeoOn_Q.symm _ _ _ R _ _ hD'S hS
      (fun i => Tc.evCompatOn_Qinv hP ω'
        (((D.restrictRep R' h1).isSmoothSubmanifold i).inter_isOpen Tc.isOpen_W')
        inter_subset_right) hA hB
    have hcard : (Nat.card (Y.Isotropy y) : ℝ) = Nat.card (X.Isotropy x) := by
      exact_mod_cast (Nat.card_congr (Equiv.ofBijective _ (Tc.bijective_conj hΦ))).symm
    rw [hμ₂ K hK, branchedMeasure_apply _ hΘ' hcpt' hT' hcov' ω' (D.restrictRep R' h1) hD'S
      (D.represents_restrictRep R' h1 hDT) hK' hKU',
      branchedMeasure_apply _ hΘ hcpt hT hcov (P ω') _ hS hR hK hKU, localMeasure, localMeasure,
      hcard]
    exact congrArg _ e.symm
  -- gluing (Theorem 9.5.4's uniqueness) over the pulled-back structures
  let J := {j : Σ x, X.OrientedTameStructure n (Φ.pullbackTheta Θ') x //
    IsPulled FY Φ hΘf T' j.2}
  let O : J → Set (X.orbitSupp (Φ.pullbackTheta Θ')) := fun j => Subtype.val ⁻¹' (X.π '' j.1.2.U)
  have hO : ∀ j, IsOpen (O j) := fun j =>
    (X.proposition_7_1_8 _ j.1.2.isOpen_U).preimage continuous_subtype_val
  have hcovO : ⋃ j, O j = univ := eq_univ_of_forall fun q => by
    obtain ⟨x, hx, hxq⟩ := q.2
    obtain ⟨C, hC⟩ := exists_isPulled hΦ hΘf hcov' hx
    exact mem_iUnion.2 ⟨⟨⟨x, C⟩, hC⟩, x, C.mem_U, hxq⟩
  obtain ⟨Ψ, -, huniq⟩ := existsUnique_linearMap_signedMeasure_of_openCover (V := ℝ)
    (borel_le_borelNullSigma _) O hO hcovO (fun _ => LinearMap.toSpanSingleton ℝ _ μ₁)
    (fun _ _ _ _ _ _ => rfl)
  have e1 := huniq (LinearMap.toSpanSingleton ℝ _ μ₁) fun _ _ _ _ _ => rfl
  have e2 := huniq (LinearMap.toSpanSingleton ℝ _ μ₂) fun j t K hK hKO => by
    change (t • μ₂) K = (t • μ₁) K
    change t • μ₂ K = t • μ₁ K
    rw [hloc j.1.2 j.2 K hK (by rintro _ ⟨q, hq, rfl⟩; exact hKO hq)]
  have e3 := congrArg (fun L : ℝ →ₗ[ℝ] SignedMeasure (X.orbitSupp (Φ.pullbackTheta Θ')) => L 1)
    (e2.trans e1.symm)
  simp only [LinearMap.toSpanSingleton_apply, one_smul] at e3
  rw [← hμ₂ K hK, e3]

/-- **Theorem 11.4.1, 2021 p. 543 (2017: Theorem 11.8, p. 396), second identity, for an
equivalence `Φ : X → Y`**: for `Θ̂'` on `Y` oriented, tame (with sheets in the class), compact,
of dimension `n`, and `K ∈ L(|supp Φ^*Θ|)`, `|Φ|(K) ∈ L(|supp Θ'|)` and
`µ^{Φ^*Θ̂'}_{Φ^*ω'}(K) = µ^Θ̂'_{ω'}(|Φ|(K))`.  (`Φ^*Θ̂' = (Φ^*Θ', Φ^*T̂')` is oriented by
Theorem 11.3.5, which asks for `HasIndependentTangentSums`.) -/
theorem theorem_11_4_1_pull_equiv (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hn : 0 < n) (hΘ' : Y.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.IsCompactBranched Θ')
    (hind' : Y.HasIndependentTangentSums Θ') (hT' : Y.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T')
    (ω' : Ω') {K : Set (X.orbitSupp (Φ.pullbackTheta Θ'))}
    (hK : MeasurableSet[X.lebesgueSigma FX.sheetNull (Φ.pullbackTheta Θ')] K) :
    MeasurableSet[Y.lebesgueSigma FY.sheetNull Θ']
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      branchedMeasure (FX.sheetIntegration hn) (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
        (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
        (isOrientation_pullSection hΦ hind' hT')
        (hcov_pull hΦ hP hΘ'.isFunctorial (isOrientation_pullSection hΦ hind' hT').isGrHatSection
          (isTransported_pull hΦ hT'.isGrHatSection) hcov') (P ω') K =
        branchedMeasure (FY.sheetIntegration hn) hΘ' hcpt' hT' hcov' ω'
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) :=
  measure_pull_core hΦ hP hn hΘ' hcpt' hT' hcov' rfl _ _ _
    (isTransported_pull hΦ hT'.isGrHatSection) _ ω' hK

/-- **Theorem 11.4.1, 2021 p. 543 (2017: Theorem 11.8, p. 396), first identity, for an
equivalence `Φ : X → Y`**: for `Θ̂` on `X` oriented, tame (with sheets in the class), compact, of
dimension `n`, `K ∈ L(|supp Θ|)` and `Φ_*ω = ω'` (the form with `Φ^*ω' = ω`), `|Φ|(K) ∈
L(|supp Φ_*Θ|)` and `µ^Θ̂_ω(K) = µ^{Φ_*Θ̂}_{Φ_*ω}(|Φ|(K))`. -/
theorem theorem_11_4_1_push_equiv (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hn : 0 < n) {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    (hind : X.HasIndependentTangentSums Θ) (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T)
    {ω : Ω} {ω' : Ω'} (hω : P ω' = ω) {K : Set (X.orbitSupp Θ)}
    (hK : MeasurableSet[X.lebesgueSigma FX.sheetNull Θ] K) :
    MeasurableSet[Y.lebesgueSigma FY.sheetNull (Φ.pushforwardTheta Θ)]
        (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) ∧
      branchedMeasure (FX.sheetIntegration hn) hΘ hcpt hT hcov ω K =
        branchedMeasure (FY.sheetIntegration hn) (isBranchedEpSubgroupoid_pushforwardTheta hΦ hΘ)
          (isCompactBranched_pushforwardTheta Φ hΦ.full hΘ.isFunctorial hcpt)
          (isOrientation_pushSection hΦ hΘ hind hT)
          (hcov_push hΦ hP hΘ.isFunctorial (isTransported_push hΦ hT.isGrHatSection) hcov) ω'
          (Subtype.val ⁻¹' (Φ.orbitMap '' (Subtype.val '' K))) := by
  subst hω
  exact measure_pull_core hΦ hP hn _ _ _ _ (pullbackTheta_pushforwardTheta hΦ.full hΘ.isFunctorial)
    hΘ hcpt hT (isTransported_push hΦ hT.isGrHatSection) hcov ω' hK

/-- **Theorem 11.4.1 for the integrals** (`K = |supp|`, Definition 9.5.6):
`∫_{Φ^*Θ̂'} Φ^*ω' = ∫_{Θ̂'} ω'`. -/
theorem integral_pull_equiv (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hn : 0 < n) (hΘ' : Y.IsBranchedEpSubgroupoid Θ') (hcpt' : Y.IsCompactBranched Θ')
    (hind' : Y.HasIndependentTangentSums Θ') (hT' : Y.IsOrientation Θ' T')
    (hcov' : ∀ y ∈ supp Θ', ∃ D : Y.OrientedTameStructure n Θ' y,
      (∀ i, D.M i ∈ FY.sheets) ∧ D.Represents T') (ω' : Ω') :
    branchedIntegral (FX.sheetIntegration hn) (isBranchedEpSubgroupoid_pullbackTheta hΦ hΘ')
        (isCompactBranched_pullbackTheta hΦ hΘ'.isFunctorial hcpt')
        (isOrientation_pullSection hΦ hind' hT')
        (hcov_pull hΦ hP hΘ'.isFunctorial (isOrientation_pullSection hΦ hind' hT').isGrHatSection
          (isTransported_pull hΦ hT'.isGrHatSection) hcov') (P ω') =
      branchedIntegral (FY.sheetIntegration hn) hΘ' hcpt' hT' hcov' ω' := by
  have h := (theorem_11_4_1_pull_equiv hΦ hP hn hΘ' hcpt' hind' hT' hcov' ω'
    MeasurableSet.univ).2
  rw [image_univ_eq_univ hΦ hΘ'.isFunctorial rfl] at h
  exact h

/-- **Theorem 11.4.1 for the integrals** (`K = |supp|`, Definition 9.5.6):
`∫_Θ̂ ω = ∫_{Φ_*Θ̂} Φ_*ω`. -/
theorem integral_push_equiv (hΦ : Φ.IsEquivalence) (hP : FX.IsPullback FY Φ P)
    (hn : 0 < n) {Θ : Obj → ℚ} (hΘ : X.IsBranchedEpSubgroupoid Θ) (hcpt : X.IsCompactBranched Θ)
    (hind : X.HasIndependentTangentSums Θ) (hT : X.IsOrientation Θ T)
    (hcov : ∀ x ∈ supp Θ, ∃ C : X.OrientedTameStructure n Θ x,
      (∀ i, C.M i ∈ FX.sheets) ∧ C.Represents T)
    {ω : Ω} {ω' : Ω'} (hω : P ω' = ω) :
    branchedIntegral (FX.sheetIntegration hn) hΘ hcpt hT hcov ω =
      branchedIntegral (FY.sheetIntegration hn) (isBranchedEpSubgroupoid_pushforwardTheta hΦ hΘ)
        (isCompactBranched_pushforwardTheta Φ hΦ.full hΘ.isFunctorial hcpt)
        (isOrientation_pushSection hΦ hΘ hind hT)
        (hcov_push hΦ hP hΘ.isFunctorial (isTransported_push hΦ hT.isGrHatSection) hcov) ω' := by
  have h := (theorem_11_4_1_push_equiv hΦ hP hn hΘ hcpt hind hT hcov hω MeasurableSet.univ).2
  rw [image_univ_eq_univ hΦ (isFunctorial_pushforwardTheta hΦ.full hΘ.isFunctorial)
    (pullbackTheta_pushforwardTheta hΦ.full hΘ.isFunctorial)] at h
  exact h

end EpFunctor

end Polyfold
