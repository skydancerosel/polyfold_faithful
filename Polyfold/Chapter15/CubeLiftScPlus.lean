import Polyfold.Chapter15.GlueStructurable
import Polyfold.Chapter14.LocalScPlus

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Corollary 15.3.10 (3)**, pp. 699–700: the lifts `(t, y) ↦ ((t, y), sᵢ(y))` of the sections of
the structures of `Λⁱ` satisfy (1) of Definition 14.1.3 on `∂([0, 1] × X)`.

# Lifted sc⁺-sections on the faces of the cylinder

## The text, paraphrased

The proof of (3) treats the multisection that is `Λⁱ` over `{i} × X` as structurable over
`∂([0, 1] × X)` because the `Λⁱ` are structurable.  For the lifted symmetric structures this
needs that the lifted sections are sc⁺ on the local faces of `[0, 1] × X`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `isFaceScPlusSectionOn_of_isScPlusSectionOn_open`: a local sc⁺-section on an open `U`
  (Definition 13.2.1) satisfies (1) of Definition 14.1.3 on every `D ⊆ U`.  In a tame strong
  bundle chart `c` the chart restricted to `U ∩ dom φ` is a chart of the atlas's structure
  (`StrongBundleChart.restrict`), the representative is sc-smooth on `φ(U ∩ dom φ) = O ∩ W`
  (`IsScPlusSectionOn.isScSmoothRetractMap_localRepOne_of_isChart`), and the local face germ
  `O ∩ V ∩ {tᵢ = 0}` of `corner_retraction`, cut down to `V ∩ W`, is a sub-retract of it.
* `isScPlusSectionOn_cubeLiftSec`: the lift `(q, y) ↦ ((q, y), s(y))` of an sc⁺-section on `U`
  is an sc⁺-section of `W̃ → [0, 1] × X` on `[0, 1] × U`: in a pulled-back chart
  `(w, h) ↦ …` over `ψ` its representative is `w ↦ (w, ŝ₁(g(w)))` with `g = φ ∘ pr ∘ ψ⁻¹`
  (the level-one form of Part I's `StrongBundle.IsScSmoothSection.pullback`).
* **`cubeLiftFace_holds`**: `CubeLiftFace A` for every `A`; so the hypothesis `hF` of
  `isBoundaryStructurable_of_sides` and of the results built on it is a theorem.
* **`isBoundaryStructurable_cubeGlue`**, **`corollary_15_3_10_3_of_rel_struct`**: the gluing
  results with `hF` discharged.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold EpGroupoid SEP

variable {A : SEP.{u}}

/-! ### Local sc⁺-sections on the local faces -/

/-- The first component of the representative of a section on `U` at a point of
`φ(U ∩ dom φ)`. -/
theorem localRepOne_fst_of_mem {s : A.Obj → A.W} {U : Set A.Obj}
    (hsec : ∀ y ∈ U, A.P (s y) = y) {c : StrongBundleChart A.X.PObj A.P} {z : c.φ.model.E 0}
    (hz : z ∈ c.φ '' (U ∩ c.φ.source)) : (localRepOne c s z).1 = z := by
  obtain ⟨y, hy, rfl⟩ := hz
  change (c (s (c.φ.symm (c.φ y)))).1 = c.φ y
  rw [c.φ.symm_apply_apply hy.2]
  have hys : s y ∈ c.toPartialEquiv.source := by
    rw [c.source_eq, mem_preimage, hsec y hy.1]; exact hy.2
  rw [c.covers _ hys, hsec y hy.1]

/-- **A local sc⁺-section on an open `U` is sc⁺ on the local faces** ((1) of Definition 14.1.3 on
every `D ⊆ U`). -/
theorem isFaceScPlusSectionOn_of_isScPlusSectionOn_open {s : A.Obj → A.W} {U : Set A.Obj}
    (hs : IsScPlusSectionOn A s U) (hU : IsOpen U) {D : Set A.Obj} (hD : D ⊆ U) :
    IsFaceScPlusSectionOn A s D := by
  refine ⟨fun x hx => ⟨hs.1 x (hD hx), hs.mem_oneSet (hD hx)⟩, ?_⟩
  intro c hc n W T hT x hx i hi
  have hts : U ∩ c.φ.source ⊆ c.φ.source := inter_subset_right
  have hto : IsOpen (U ∩ c.φ.source) := hU.inter c.φ.isOpen_source
  have hc' : A.B.IsChart (c.restrict hts hto) := fun c₂ hc₂ => (hc.1 c₂ hc₂).restrict_left hts hto
  have hmap := hs.isScSmoothRetractMap_localRepOne_of_isChart hU hc' inter_subset_left
  have hO := c.base_retract
  have ho : c.φ x ∈ (c.isRetraction.baseRetraction c.relOpen).retract := by
    rw [hO]; exact c.φ.mapsTo_model x hx.2
  have hσ : ∀ j ∈ ({i} : Finset (Fin n)), (T 0 (c.φ x)).1 j = 0 := fun j hj => by
    rw [Finset.mem_singleton.1 hj]; exact (mem_zeroSet T).1 hi
  obtain ⟨-, -, -, V, hV, hxV, S, -, -, hSret, -⟩ := corner_retraction {i} hT (hc.2 n W T hT) ho hσ
  have hQ : S.retract = c.φ.model.O ∩ V ∩ coordHyper T i := by
    rw [hSret, hO]; ext z; simp [coordHyper]
  have hWt := c.image_eq_restrictOpen hts hto
  have hWo := c.isOpen_restrictOpen hts hto
  have hxW : c.φ x ∈ c.restrictOpen hts hto := by
    have : c.φ x ∈ c.φ '' (U ∩ c.φ.source) := ⟨x, ⟨hD hx.1, hx.2⟩, rfl⟩
    rw [hWt] at this; exact this.2
  have hsub : c.φ.model.O ∩ (V ∩ c.restrictOpen hts hto) ∩ coordHyper T i ⊆
      c.φ '' (U ∩ c.φ.source) := fun z hz => by
    rw [hWt]; exact ⟨hz.1.1, hz.1.2.2⟩
  have hret : IsScRetract c.φ.model.E c.φ.model.C
      (c.φ.model.O ∩ (V ∩ c.restrictOpen hts hto) ∩ coordHyper T i) := by
    have h := proposition_2_3_1_one ⟨S, hQ⟩ hWo
    have e : c.φ.model.O ∩ V ∩ coordHyper T i ∩ c.restrictOpen hts hto =
        c.φ.model.O ∩ (V ∩ c.restrictOpen hts hto) ∩ coordHyper T i := by
      ext z; simp only [mem_inter_iff]; tauto
    rwa [e] at h
  have hKsub : MapsTo (localRepOne c s) (c.φ '' (U ∩ c.φ.source)) (strongShiftOne c.K) :=
    fun z hz => by
      have := hmap.mapsTo hz
      change ((localRepOne c s z).1, c.F.toBase 1 (localRepOne c s z).2) ∈
        (c.restrict hts hto).K at this
      rw [c.restrict_K] at this
      exact this.1
  have hmap' := hmap.mono_target hKsub
  exact ⟨V ∩ c.restrictOpen hts hto, hV.inter hWo, ⟨hxV, hxW⟩, hret,
    fun z hz => localRepOne_fst_of_mem hs.1 (hsub hz),
    hmap'.mono_source (c.φ.isScRetract_image hts hto) hsub⟩

/-! ### The lift of a local sc⁺-section to the cylinder -/

/-- **The lift of an sc⁺-section on `U` is an sc⁺-section on `[0, 1] × U`**: in the pulled-back
chart over `ψ` and the strong bundle chart `c` of `W`, the representative of
`(q, y) ↦ ((q, y), s(y))` is `w ↦ (w, ŝ₁(g(w)))`, `g = φ ∘ pr ∘ ψ⁻¹`. -/
theorem isScPlusSectionOn_cubeLiftSec {s : A.Obj → A.W} {U : Set A.Obj}
    (hs : IsScPlusSectionOn A s U) (hU : IsOpen U) :
    IsScPlusSectionOn (A.cubeSEP 1) (cubeLiftSec s) {p | p.2 ∈ U} := by
  have hUt : IsOpen {p : (A.cubeSEP 1).Obj | p.2 ∈ U} := hU.preimage continuous_snd
  refine isScPlusSectionOn_of_localRepOne hUt (fun p _ => P_cubeLiftSec s p) fun p hp => ?_
  obtain ⟨c, hc, hpc⟩ := exists_chart_mem_source A p.2
  have hπ := (A.X.cubeProj 1).isScSmoothMap_obj
  obtain ⟨d, rfl, hpd⟩ := exists_pullbackChartData hπ c hpc
  set q₀ := cubeLiftSec s p
  set e := d.toChart q₀ with he
  have hmem : e ∈ (A.cubeSEP 1).B.atlas.charts := ⟨d, q₀, hc, rfl⟩
  have hval : ∀ y : (A.cubeSEP 1).Obj, y.2 ∈ U → (cubeLiftSec s y).1.2 = s y.2 := fun y hy =>
    fixSec_of (hs.1 _ hy)
  refine ⟨e, hmem, hpd, fun y hy => ?_, ?_⟩
  · change (d.c (cubeLiftSec s y).1.2).2 ∈ range (d.c.F.toBase 1)
    rw [hval y hy.1]
    exact hs.mem_range hc ⟨hy.1, d.mapsTo hy.2⟩
  -- the pieces of the representative
  set Ot : Set (d.ψ.model.E 0) := d.ψ '' ({p : (A.cubeSEP 1).Obj | p.2 ∈ U} ∩ d.ψ.source)
  set Oc : Set (d.c.φ.model.E 0) := d.c.φ '' (U ∩ d.c.φ.source)
  have hL := hs.isScSmoothRetractMap_localRepOne hU hc p.2
  have hretc : IsScRetract d.c.φ.model.E d.c.φ.model.C Oc :=
    d.c.φ.isScRetract_image inter_subset_right (hU.inter d.c.φ.isOpen_source)
  have hgmaps : MapsTo d.g Ot Oc := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, ⟨hy.1, d.mapsTo hy.2⟩, ?_⟩
    change d.c.φ y.2 = d.c.φ (Prod.snd (d.ψ.symm (d.ψ y)))
    rw [d.ψ.symm_apply_apply hy.2]
  have hg : IsScSmoothRetractMap d.ψ.model.E d.ψ.model.C Ot d.c.φ.model.E d.c.φ.model.C Oc d.g :=
    (d.smooth.mono_source d.ψ.model.isScRetract
      (d.ψ.image_subset_model inter_subset_right)).mono_target hgmaps
  have h1 := hL.comp hg hretc
  have hsnd : IsScSmoothRetractMap (d.c.φ.model.E.prod d.c.F.shift) (d.c.φ.model.C ×ˢ univ)
      (strongShiftOne d.c.K) d.c.F.shift univ univ Prod.snd :=
    (d.c.φ.model.E.prodSndOp d.c.F.shift).isScSmoothRetractMap d.c.isScRetract_one
      (mapsTo_univ _ _)
  have h2 := hsnd.comp h1 d.c.isScRetract_one
  have hid := isScSmoothRetractMap_id (C := d.ψ.model.C) Ot
  have h3 := IsScSmoothRetractMap.scPair hid h2 (C' := d.ψ.model.C ×ˢ univ)
    (O' := strongShiftOne e.K) fun w hw => by
      have hk := h1.mapsTo hw
      have hfst : (localRepOne d.c s (d.g w)).1 = d.g w :=
        localRepOne_fst_of_mem hs.1 (hgmaps hw)
      change (w, d.c.F.toBase 1 (localRepOne d.c s (d.g w)).2) ∈ e.K
      change (pullbackRetraction d.c.R d.RZ d.g '' (d.RZ.U ×ˢ univ)) _
      rw [d.image_eq_Kg]
      refine ⟨by rw [d.RZ_retract]; exact d.ψ.image_subset_model inter_subset_right hw, ?_⟩
      change ((localRepOne d.c s (d.g w)).1, d.c.F.toBase 1 (localRepOne d.c s (d.g w)).2) ∈
        d.c.K at hk
      rw [hfst] at hk
      exact hk
  refine h3.congr ?_
  rintro _ ⟨y, hy, rfl⟩
  have hyc : y.2 ∈ d.c.φ.source := d.mapsTo hy.2
  change (d.ψ y, (localRepOne d.c s (d.c.φ (Prod.snd (d.ψ.symm (d.ψ y))))).2) =
    ((d.ψ (d.ψ.symm (d.ψ y))), Function.invFun (d.c.F.toBase 1)
      (d.c (cubeLiftSec s (d.ψ.symm (d.ψ y))).1.2).2)
  rw [d.ψ.symm_apply_apply hy.2, hval y hy.1]
  change (d.ψ y, Function.invFun (d.c.F.toBase 1) (d.c (s (d.c.φ.symm (d.c.φ y.2)))).2) = _
  rw [d.c.φ.symm_apply_apply hyc]

/-! ### `CubeLiftFace` -/

/-- **`CubeLiftFace A` holds**: the lift of an sc⁺-section on an open `U ⊆ X` is sc⁺ on the
local faces of `[0, 1] × X` over `U`. -/
theorem cubeLiftFace_holds : CubeLiftFace A := fun _ _ hU hs =>
  isFaceScPlusSectionOn_of_isScPlusSectionOn_open (isScPlusSectionOn_cubeLiftSec hs hU)
    (hU.preimage continuous_snd) inter_subset_left

/-! ### Consequences -/

/-- **The glued multisection of Corollary 15.3.10 (3) is structurable over the boundary**:
`cubeGlue Λ₀ Λ₁` for structurable `Λ₀`, `Λ₁`, `d_X ≡ 0` and paracompact `|X|`, with no added
hypothesis (`X` is tame as `d_X ≡ 0`, and `CubeLiftFace A` holds). -/
theorem isBoundaryStructurable_cubeGlue (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hpara : A.X.HasParacompactOrbitSpace) {Λ₀ Λ₁ : A.W → ℚ≥0} (h₀ : IsStructurable A Λ₀)
    (h₁ : IsStructurable A Λ₁) : IsBoundaryStructurable (A.cubeSEP 1) (cubeGlue Λ₀ Λ₁) :=
  isBoundaryStructurable_cubeGlue_of_cubeLiftFace (A.X.isTame_of_degIndex_eq_zero hd) hd hpara
    cubeLiftFace_holds h₀ h₁

/-- **Corollary 15.3.10 (3), p. 699, for two structurable regular perturbations**, from the
relative step on `[0, 1] × X` (`hrelC`) and the face condition of the glued data (`hbonto`):
`corollary_15_3_10_3_of_rel` with `CubeLiftFace A` proved.  The added hypotheses are
`hrelC`, `hbonto` and sc-smooth partitions of unity on `X` (`hPU`). -/
theorem corollary_15_3_10_3_of_rel_onto
    (hrelC : theorem_15_3_7_relative_statement (A.cubeSEP 1))
    (hd : ∀ x, A.X.PObj.degIndex x = 0) (hpara : A.X.HasParacompactOrbitSpace)
    (hPU : A.X.PObj.AdmitsScPartitionsOfUnity) {f : A.Obj → A.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hS : A.E.HasCompactSolutionSetEp f) {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj}
    {Λ₀ Λ₁ : A.W → ℚ≥0} (hr₀ : IsRegularPerturbation A f N₀ U₀ Λ₀)
    (hr₁ : IsRegularPerturbation A f N₁ U₁ Λ₁)
    (hbonto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁)) :
    ∃ Λ' : (A.cubeSEP 1).W → ℚ≥0,
      IsRegularPerturbation (A.cubeSEP 1) (cubeLiftEp (n := 1) f hf.1.1.1)
        (interpAuxNorm A N₀ N₁) (interpSet A U₀ U₁) Λ' ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2) ∧
      (∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2) ∧
      (A.cubeSEP 1).X.IsBranchedEpSubgroupoid
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) ∧
      (A.cubeSEP 1).X.IsCompactBranched
        (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)) :=
  corollary_15_3_10_3_of_rel hrelC cubeLiftFace_holds hd hpara hPU hf hft hS hr₀ hr₁ hbonto

end SBLocalization

end Polyfold
