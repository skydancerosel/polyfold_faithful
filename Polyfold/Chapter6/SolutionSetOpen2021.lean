import Polyfold.Chapter6.SolutionSetOrientation

/-!
# The natural orientation of an open part of the solution set (2021 Theorem 6.6.18)

Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), **Theorem 6.6.18**
(p. 275; preprint Theorem 6.41), for an open part `S ∩ V` of `S = f⁻¹(0)` and without
properness. `theorem_6_6_18_oriented` (`SolutionSetOrientation.lean`) treats the whole compact
`S` with general position and index `d` at every zero. The proof of Theorem 6.7.1 (p. 278) needs
the orientation of solution sets that are not compact (the cobordism `S_F` over `ℝ¹ × X`) and of
the parts of `S` of one index. Here:

* `isSubmanifoldOfDim_inter_open`, `isGoodPositionAt_inter_open`: for `V` open such that every
  zero in `V` is in general position with index `d`, `S ∩ V` is a `d`-dimensional submanifold in
  good position (Theorem 3.6.8 (2), (3), p. 136; Lemma 4.2.8, p. 166; no compactness).
* `solOrOpen`: the orientation of `T_x(S ∩ V)` read from `o_x` (the construction of
  `SolutionSetOrientation.lean`, with `A = S ∩ V` for `A = S`); `isContinuous_solOr_open`: it is
  continuous; `solOr_spec_open`: it is `o_x` on `ker f'(x)`. The continuity uses the continuity of
  `o` along paths of zeros in general position
  (`isLineOrientation_tangentOr_of_isSectionOrientation`),
  which holds without properness.
* `theorem_6_6_18_oriented_open`: `S ∩ V` is a Mathlib manifold `IsManifold (𝓠 d) ∞` with a
  continuous tangent orientation which is `o_x` at every `x`; it is Hausdorff, and σ-compact when
  `S ∩ V` is.
* `isClopen_index_part`, `exists_isOpen_inter_eq_index`: for `f` in general position at every
  zero, the part `S_k` of `S` where `f'(x)` has index `k` is clopen in `S`, and `S_k = S ∩ V_k`
  for an open `V_k` (the index is locally constant, `theorem_3_6_8_index_locally_constant`).

The sections `SolutionSet` and `Orient` below are those of `SolutionSetOrientation.lean` with
`solutionSet P f` replaced by `solutionSet P f ∩ Ω`; the generic parts (the tangent map of the
inclusion, the chart changes, segments in corner coordinates) are reused from there.
-/

open Set Filter Topology Manifold Module Bundle WithLp
open scoped ContDiff

noncomputable section

namespace Polyfold

universe u v

/-! ### The tangent spaces of `S ∩ Ω` -/

section SolutionSet

open MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {Ω : Set X} [ParacompactSpace ↥(solutionSet P f ∩ Ω)]
  {hY : PX.IsSubMPolyfold (solutionSet P f ∩ Ω)} {n : ℕ} (κ : CornerCoords (subPolyfold hY) n)

omit [ParacompactSpace ↥(solutionSet P f ∩ Ω)] in
/-- **The tangent space of `S ∩ Ω` in an induced chart is the kernel**
(`tangentSpace_subChart_overlap` for `S ∩ Ω`; the tangent space of `φ(G ∩ S)` is `ker Lin(w)` for
`G` inside `W ∩ Ω`, `tangentSpace_solutionSet_eq_linKer`). -/
theorem tangentSpace_subChart_overlap_open (hΩ : IsOpen Ω) (hft : B.IsScFredholmSectionTame f)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (d : PX.SubData (solutionSet P f ∩ Ω))
    (a₀ : ↥(solutionSet P f ∩ Ω)) (χ : MChart ↥(solutionSet P f ∩ Ω))
    {x : ↥(solutionSet P f ∩ Ω)}
    (hxσ : x ∈ (subChart d c.isChart a₀).source) (hxχ : x ∈ χ.source)
    (hgp : B.IsGeneralPositionGerm f x.1) {w : c.φ.model.E 1}
    (hw : c.φ.model.E.toBase 1 w = c.φ x.1) :
    tangentSpace c.φ.model.E c.φ.model.C ((subChart d c.isChart a₀).overlap χ) w =
      c.linKer f w := by
  obtain ⟨W₀, hW₀o, hxW₀, hW⟩ :=
    tangentSpace_solutionSet_eq_linKer hft hgp (show IsZeroAt P f x.1 from x.2.1)
  set W := W₀ ∩ Ω with hWdef
  have hWo : IsOpen W := hW₀o.inter hΩ
  have hxW : x.1 ∈ W := ⟨hxW₀, x.2.2⟩
  have hxs : x.1 ∈ d.shrink c.φ := hxσ
  have hxG : x.1 ∈ d.shrink c.φ ∩ W := ⟨hxs, hxW⟩
  have hGS : c.φ '' ((d.shrink c.φ ∩ W) ∩ solutionSet P f) =
      (subChart d c.isChart a₀) '' ((subChart d c.isChart a₀).source ∩ Subtype.val ⁻¹' W) := by
    ext u
    constructor
    · rintro ⟨y, ⟨⟨hy, hyW⟩, hyS⟩, rfl⟩
      exact ⟨⟨y, hyS, hyW.2⟩, ⟨hy, hyW⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hyW⟩, rfl⟩
      exact ⟨y.1, ⟨⟨hy, hyW⟩, y.2.1⟩, rfl⟩
  have hs : (subChart d c.isChart a₀).source ∩ Subtype.val ⁻¹' W ⊆
      (subChart d c.isChart a₀).source := inter_subset_left
  have hso : IsOpen ((subChart d c.isChart a₀).source ∩ Subtype.val ⁻¹' W) :=
    (subChart d c.isChart a₀).isOpen_source.inter (hWo.preimage continuous_subtype_val)
  have hQ : IsScRetract c.φ.model.E c.φ.model.C
      (c.φ '' ((d.shrink c.φ ∩ W) ∩ solutionSet P f)) := by
    rw [hGS]; exact (subChart d c.isChart a₀).isScRetract_image hs hso
  have hker := hW c hc (d.shrink_subset_source c.φ hxs) (d.shrink c.φ ∩ W)
    ((d.isOpen_shrink c.φ).inter hWo) (inter_subset_left.trans (d.shrink_subset_source c.φ))
    (inter_subset_right.trans inter_subset_left) hxG hQ w hw
  obtain ⟨W₁, hW₁, hW₁eq⟩ := (subChart d c.isChart a₀).exists_isOpen_image_eq
    (s := (subChart d c.isChart a₀).source ∩ χ.source) inter_subset_left
    ((subChart d c.isChart a₀).isOpen_source.inter χ.isOpen_source)
  obtain ⟨W₂, hW₂, hW₂eq⟩ := (subChart d c.isChart a₀).exists_isOpen_image_eq hs hso
  have hwσ : c.φ.model.E.toBase 1 w = subChart d c.isChart a₀ x := hw
  have hO := (subChart d c.isChart a₀).model.isScRetract
  have hm₁ : (subChart d c.isChart a₀).model.E.toBase 1 w ∈
      (subChart d c.isChart a₀).model.O ∩ W₁ := by
    rw [← hW₁eq]; exact ⟨x, ⟨hxσ, hxχ⟩, hwσ.symm⟩
  have hm₂ : (subChart d c.isChart a₀).model.E.toBase 1 w ∈
      (subChart d c.isChart a₀).model.O ∩ W₂ := by
    rw [← hW₂eq]; exact ⟨x, ⟨hxσ, hxW⟩, hwσ.symm⟩
  have h1 : tangentSpace c.φ.model.E c.φ.model.C ((subChart d c.isChart a₀).overlap χ) w =
      tangentSpace c.φ.model.E c.φ.model.C (subChart d c.isChart a₀).model.O w :=
    (congrArg (fun Q => tangentSpace c.φ.model.E c.φ.model.C Q w) hW₁eq).trans
      (tangentSpace_inter_isOpen hO hW₁ hm₁)
  have h2 : tangentSpace c.φ.model.E c.φ.model.C
      (c.φ '' ((d.shrink c.φ ∩ W) ∩ solutionSet P f)) w =
      tangentSpace c.φ.model.E c.φ.model.C (subChart d c.isChart a₀).model.O w :=
    (congrArg (fun Q => tangentSpace c.φ.model.E c.φ.model.C Q w) (hGS.trans hW₂eq)).trans
      (tangentSpace_inter_isOpen hO hW₂ hm₂)
  exact h1.trans (h2.symm.trans hker)

/-- **The tangent map of `S ∩ Ω ↪ X` takes values in `ker f'(x)`** (`modelDeriv_mem_linKer` for
`S ∩ Ω`). -/
theorem modelDeriv_mem_linKer_open (hΩ : IsOpen Ω) (hft : B.IsScFredholmSectionTame f)
    {c : StrongBundleChart PX P}
    (hc : B.IsChart c) (d : PX.SubData (solutionSet P f ∩ Ω)) (a₀ : ↥(solutionSet P f ∩ Ω))
    {x : ↥(solutionSet P f ∩ Ω)} (hxκ : x ∈ κ.s) (hxσ : x ∈ (subChart d c.isChart a₀).source)
    {z : κ.χ.model.E 1} (hz : κ.χ.model.E.toBase 1 z = κ.χ x)
    (hgp : B.IsGeneralPositionGerm f x.1) {w : c.φ.model.E 1}
    (hw : c.φ.model.E.toBase 1 w = c.φ x.1) (v : EuclideanSpace ℝ (Fin n)) :
    modelDeriv κ c.isChart d a₀ z v ∈ c.linKer f w := by
  set σ := subChart d c.isChart a₀
  have hσ := subPolyfold_isChart hY d c.isChart a₀
  have hmem := transDeriv_mem_tangentSpace κ.isCornerChart κ.isChart hσ (κ.s_subset hxκ) hxσ hz
    (κ.Ψ.symm (ofLp v))
  have hy := toBase_levelMap_transition κ.isCornerChart κ.isChart hσ (κ.s_subset hxκ) hxσ hz
  have hyw : levelMap (κ.χ.transition σ ∘ overlapRet κ.isCornerChart σ) 1 z = w :=
    c.φ.model.E.toBase_injective 1 (hy.trans hw.symm)
  rw [hyw] at hmem
  have := tangentSpace_subChart_overlap_open hΩ hft hc d a₀ κ.χ hxσ (κ.s_subset hxκ) hgp hw
  rw [← SetLike.mem_coe, ← this]
  exact hmem

end SolutionSet

/-! ### The orientation of the Mathlib manifold `S ∩ Ω` -/

section Orient

open MPolyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {Ω : Set X} [hΩ : Fact (IsOpen Ω)] [ParacompactSpace ↥(solutionSet P f ∩ Ω)]
  {hY : PX.IsSubMPolyfold (solutionSet P f ∩ Ω)} {n : ℕ}

variable (hft : B.IsScFredholmSectionTame f) (κ : CornerCoords (subPolyfold hY) n)

/-- **The tangent map of `S ↪ X` at `x` as an isomorphism `ℝⁿ ≅ ker f'(x)`**: `modelDeriv` (the
tangent map read in the corner coordinates `κ` and the chart `c`) is injective with values in
`ker Lin(w)` (`modelDeriv_mem_linKer_open`), and both sides have dimension `n`. -/
def solKerEquivOpen {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (d : PX.SubData (solutionSet P f ∩ Ω))
    (a₀ : ↥(solutionSet P f ∩ Ω)) {x : ↥(solutionSet P f ∩ Ω)} (hxκ : x ∈ κ.s)
    (hxσ : x ∈ (subChart d c.isChart a₀).source) (hgp : B.IsGeneralPositionGerm f x.1)
    {w : c.φ.model.E 1} (hw : c.φ.model.E.toBase 1 w = c.φ x.1)
    (hdim : FiniteDimensional ℝ (c.linKer f w) ∧ finrank ℝ (c.linKer f w) = n) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] c.linKer f w :=
  haveI := hdim.1
  LinearMap.linearEquivOfInjective
    ((modelDeriv κ c.isChart d a₀ (κ.zOf x) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] c.φ.model.E 0).codRestrict (c.linKer f w)
      (modelDeriv_mem_linKer_open κ hΩ.out hft hc d a₀ hxκ hxσ (κ.toBase_zOf x) hgp hw))
    (fun _ _ h => modelDeriv_injective κ c.isChart d a₀ hxκ hxσ (κ.toBase_zOf x)
      (congrArg Subtype.val h))
    (by rw [finrank_euclideanSpace_fin, hdim.2])

theorem coe_solKerEquiv_open {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (d : PX.SubData (solutionSet P f ∩ Ω)) (a₀ : ↥(solutionSet P f ∩ Ω))
    {x : ↥(solutionSet P f ∩ Ω)}
    (hxκ : x ∈ κ.s) (hxσ : x ∈ (subChart d c.isChart a₀).source)
    (hgp : B.IsGeneralPositionGerm f x.1) {w : c.φ.model.E 1}
    (hw : c.φ.model.E.toBase 1 w = c.φ x.1)
    (hdim : FiniteDimensional ℝ (c.linKer f w) ∧ finrank ℝ (c.linKer f w) = n)
    (v : EuclideanSpace ℝ (Fin n)) :
    (solKerEquivOpen hft κ hc d a₀ hxκ hxσ hgp hw hdim v : c.φ.model.E 0) =
      modelDeriv κ c.isChart d a₀ (κ.zOf x) v := by
  have := hdim.1
  rfl

variable (o : SectionOrientation f hft.toIsScFredholmSection)
  (hgp : ∀ x ∈ solutionSet P f ∩ Ω, B.IsGeneralPositionGerm f x)
  (hidx : ∀ y ∈ solutionSet P f ∩ Ω, B.IsLinOfIndex f y n)

/-- **The orientation `o_x` read in the corner coordinates `κ` of `S` and the chart `c` of `X`**:
the orientation of `ℝⁿ` pulled back from `tangentOr(o_x)` on `ker f'(x)` along `solKerEquivOpen`
(`pullOr`). -/
def solReadOrOpen {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (d : PX.SubData (solutionSet P f ∩ Ω))
    (a₀ : ↥(solutionSet P f ∩ Ω)) {x : ↥(solutionSet P f ∩ Ω)} (hxκ : x ∈ κ.s)
    (hxσ : x ∈ (subChart d c.isChart a₀).source) :
    Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) :=
  pullOr finrank_euclideanSpace_fin
    (solKerEquivOpen hft κ hc d a₀ hxκ hxσ (hgp x.1 x.2)
      (chartPtOf c hc (d.shrink_subset_source c.φ hxσ)
        (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2.1)).toBase_z
      (finrank_linKer_of hft x.2.1 (hgp x.1 x.2) (hidx x.1 x.2) hc (d.shrink_subset_source c.φ hxσ)
        _ (chartPtOf c hc (d.shrink_subset_source c.φ hxσ)
          (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2.1)).toBase_z))
    ((chartPtOf c hc (d.shrink_subset_source c.φ hxσ)
        (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2.1)).tangentOr
      hft.toIsScFredholmSection x.2.1 (hgp x.1 x.2).isLinSurjAt
      (toChartOr hft.toIsScFredholmSection
        (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2.1) c hc
        (d.shrink_subset_source c.φ hxσ)
        (o.1 x.1 (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2.1))))

theorem solReadOr_congr_open {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (d : PX.SubData (solutionSet P f ∩ Ω)) (a₀ : ↥(solutionSet P f ∩ Ω))
    {x x' : ↥(solutionSet P f ∩ Ω)}
    (h : x = x') (hxκ : x ∈ κ.s) (hxσ : x ∈ (subChart d c.isChart a₀).source) (hxκ' : x' ∈ κ.s)
    (hxσ' : x' ∈ (subChart d c.isChart a₀).source) :
    solReadOrOpen hft κ o hgp hidx hc d a₀ hxκ hxσ =
      solReadOrOpen hft κ o hgp hidx hc d a₀ hxκ' hxσ' := by
  subst h; rfl

/-- **The reading does not depend on the chart of `X`**: by the chain rule
(`modelDeriv_chartChange`), the two isomorphisms `ℝⁿ ≅ ker f'(x)` differ by the tangent map of
the transition, which also relates the two tangent orientations (`tangentOrAt_toChartOr`). -/
theorem solReadOr_chartChange_open {c c' : StrongBundleChart PX P} (hc : B.IsChart c)
    (hc' : B.IsChart c') (d d' : PX.SubData (solutionSet P f ∩ Ω)) (a₀ a₀' : ↥(solutionSet P f ∩ Ω))
    {x : ↥(solutionSet P f ∩ Ω)} (hxκ : x ∈ κ.s) (hxσ : x ∈ (subChart d c.isChart a₀).source)
    (hxσ' : x ∈ (subChart d' c'.isChart a₀').source) :
    solReadOrOpen hft κ o hgp hidx hc d a₀ hxκ hxσ =
      solReadOrOpen hft κ o hgp hidx hc' d' a₀' hxκ hxσ' := by
  have hs := hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2.1
  have h := tangentOrAt_toChartOr hft.toIsScFredholmSection hs x.2.1 (hgp x.1 x.2).isLinSurjAt
    (o.1 x.1 hs) hc hc' (d.shrink_subset_source c.φ hxσ) (d'.shrink_subset_source c'.φ hxσ')
  unfold solReadOrOpen
  rw [h]
  have hxc := d.shrink_subset_source c.φ hxσ
  have hdim := finrank_linKer_of hft x.2.1 (hgp x.1 x.2) (hidx x.1 x.2) hc hxc _
    (chartPtOf c hc hxc hs).toBase_z
  refine (pullOr_eq_of_comp _ (fun v => Subtype.ext ?_) _).symm
  refine (coe_solKerEquiv_open _ _ _ _ _ _ _ _ _ _ v).trans
    ((modelDeriv_chartChange κ hc hc' d d' a₀ a₀' hxκ hxσ hxσ' (κ.toBase_zOf x) hs v).trans ?_)
  rw [← coe_solKerEquiv_open hft κ hc d a₀ hxκ hxσ (hgp x.1 x.2) (chartPtOf c hc hxc hs).toBase_z
    hdim v]
  exact (ChartPoint.coe_tangentKerEquiv (chartPtOf c hc hxc hs)
    (chartPtOf c' hc' (d'.shrink_subset_source c'.φ hxσ') hs) hft.toIsScFredholmSection x.2.1
    _).symm

/-- **The reading changes with the corner coordinates by the chart change of `S`**:
`signMap D(κ' ∘ κ⁻¹)` moves the reading in `κ` to the reading in `κ'` (the chain rule
`derivIn_comp_chartChangeDeriv` for the tangent map of `S ↪ X`, `derivIn_incl`). -/
theorem signMap_solReadOr_open [ChartedSpace (EuclideanQuadrant n) ↥(solutionSet P f ∩ Ω)]
    (κ' : CornerCoords (subPolyfold hY) n)
    (he : κ.toQuadrantChart ∈ IsManifold.maximalAtlas (𝓠 n) ∞ ↥(solutionSet P f ∩ Ω))
    (he' : κ'.toQuadrantChart ∈ IsManifold.maximalAtlas (𝓠 n) ∞ ↥(solutionSet P f ∩ Ω))
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (d : PX.SubData (solutionSet P f ∩ Ω))
    (a₀ : ↥(solutionSet P f ∩ Ω)) {x : ↥(solutionSet P f ∩ Ω)} (hxκ : x ∈ κ.s) (hxκ' : x ∈ κ'.s)
    (hxσ : x ∈ (subChart d c.isChart a₀).source) :
    signMap (chartChangeDeriv (𝓠 n) κ.toQuadrantChart κ'.toQuadrantChart x)
        (solReadOrOpen hft κ o hgp hidx hc d a₀ hxκ hxσ) =
      solReadOrOpen hft κ' o hgp hidx hc d a₀ hxκ' hxσ := by
  have h1 := derivIn_incl κ' c.isChart d a₀ hxκ' hxσ (κ'.toBase_zOf x)
  have h2 := derivIn_incl κ c.isChart d a₀ hxκ hxσ (κ.toBase_zOf x)
  have h3 := derivIn_comp_chartChangeDeriv (by simp) he he' hxκ hxκ'
    (hasFDerivWithinAt_incl κ' c.isChart d a₀ hxκ' hxσ (κ'.toBase_zOf x)).differentiableWithinAt
  rw [h1, h2] at h3
  unfold solReadOrOpen
  refine signMap_pullOr _ (fun v => Subtype.ext ?_) _
  exact (coe_solKerEquiv_open _ _ _ _ _ _ _ _ _ _ _).trans
    ((DFunLike.congr_fun h3 v).trans (coe_solKerEquiv_open _ _ _ _ _ _ _ _ _ _ v).symm)

variable (hcs : (subPolyfold hY).HasCornerStructureOfDim n)

/-- **The orientation of `T_xS`** (Theorem 6.6.18): `o_x` read in the corner coordinates of the
charted space `cornerChartedSpace hcs` at `x` and the chosen chart `orChart B x` of `X`
(`solReadOrOpen`). -/
def solOrOpen (x : ↥(solutionSet P f ∩ Ω)) : Orientation ℝ (EuclideanSpace ℝ (Fin n)) (Fin n) :=
  solReadOrOpen hft (hcs.exists_cornerCoords x).choose o hgp hidx (isChart_orChart x.1)
    (hY.data x.2) x (hcs.exists_cornerCoords x).choose_spec
    ((hY.data x.2).mem_shrink (orChart B x.1).φ x.2 (hY.mem_data_V x.2) (mem_orChart x.1))

/-- **`solOrOpen` read in any corner coordinates `κ` and any chart `c` of `X`** is the reading
`solReadOrOpen` there (`solReadOr_chartChange_open`, `signMap_solReadOr_open`). -/
theorem orientationIn_solOr_open [inst : ChartedSpace (EuclideanQuadrant n) ↥(solutionSet P f ∩ Ω)]
    (hch : inst = (subPolyfold hY).cornerChartedSpace hcs) {c : StrongBundleChart PX P}
    (hc : B.IsChart c) (d : PX.SubData (solutionSet P f ∩ Ω)) (a₀ : ↥(solutionSet P f ∩ Ω))
    {x : ↥(solutionSet P f ∩ Ω)} (hxκ : x ∈ κ.s) (hxσ : x ∈ (subChart d c.isChart a₀).source) :
    orientationIn (I := 𝓠 n) κ.toQuadrantChart x
        (modelOrToTangent x (solOrOpen hft o hgp hidx hcs x)) =
      solReadOrOpen hft κ o hgp hidx hc d a₀ hxκ hxσ := by
  have := isManifold_of_eq hcs hch
  have hκ₀ := (hcs.exists_cornerCoords x).choose_spec
  have h := solReadOr_chartChange_open hft _ o hgp hidx (isChart_orChart x.1) hc (hY.data x.2) d
    x a₀
    hκ₀ ((hY.data x.2).mem_shrink _ x.2 (hY.mem_data_V x.2) (mem_orChart x.1)) hxσ
  unfold orientationIn
  rw [chartAt_eq_of_eq hcs hch x]
  refine (congrArg (signMap _) h).trans ?_
  exact signMap_solReadOr_open hft _ o hgp hidx κ (mem_maximalAtlas_of_eq hcs hch _)
    (mem_maximalAtlas_of_eq hcs hch κ) hc d a₀ hκ₀ hxκ hxσ

/-- **`solOrOpen` agrees with `o_x` on `ker f'(x)`**: for every chart `c` of `X` at `x`, the tangent
map of `S ↪ X` at `x` (read in Mathlib's chart at `x` and in `c`) is an isomorphism
`ι : T_xS = ℝⁿ ≅ ker f'(x)`, and a basis `b` of `T_xS` is positive for `solOrOpen` iff
`ι b₁ ∧ … ∧ ι bₙ` is positive for `tangentOr(o_x)`. -/
theorem solOr_spec_open [inst : ChartedSpace (EuclideanQuadrant n) ↥(solutionSet P f ∩ Ω)]
    (hch : inst = (subPolyfold hY).cornerChartedSpace hcs) (x : ↥(solutionSet P f ∩ Ω))
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hxc : x.1 ∈ c.φ.source) :
    ∃ ι : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] c.linKer f (chartPtOf c hc hxc
        (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2.1)).z,
      (∀ v, (ι v : c.φ.model.E 0) = derivIn (𝓠 n) (chartAt (EuclideanQuadrant n) x)
        (fun y : ↥(solutionSet P f ∩ Ω) => c.φ y.1) x v) ∧
      ∀ b : Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
        b.orientation = solOrOpen hft o hgp hidx hcs x ↔
          (chartPtOf c hc hxc (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2.1)).tangentOr
              hft.toIsScFredholmSection x.2.1 (hgp x.1 x.2).isLinSurjAt
              (toChartOr hft.toIsScFredholmSection
                (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2.1) c hc hxc
                (o.1 x.1 (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2.1))) =
            rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι b) := by
  have hs := hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2.1
  have hκ₀ := (hcs.exists_cornerCoords x).choose_spec
  have hxσ : x ∈ (subChart (hY.data x.2) c.isChart x).source :=
    (hY.data x.2).mem_shrink c.φ x.2 (hY.mem_data_V x.2) hxc
  have hdim := finrank_linKer_of hft x.2.1 (hgp x.1 x.2) (hidx x.1 x.2) hc hxc _
    (chartPtOf c hc hxc hs).toBase_z
  refine ⟨solKerEquivOpen hft _ hc (hY.data x.2) x hκ₀ hxσ (hgp x.1 x.2)
    (chartPtOf c hc hxc hs).toBase_z hdim, fun v => ?_, fun b => ?_⟩
  · refine (coe_solKerEquiv_open _ _ _ _ _ _ _ _ _ _ v).trans ?_
    rw [chartAt_eq_of_eq hcs hch x]
    exact (DFunLike.congr_fun (derivIn_incl _ c.isChart _ x hκ₀ hxσ
      (MPolyfold.CornerCoords.toBase_zOf _ x)) v).symm
  · have h : solOrOpen hft o hgp hidx hcs x =
        solReadOrOpen hft _ o hgp hidx hc (hY.data x.2) x hκ₀ hxσ :=
      solReadOr_chartChange_open hft _ o hgp hidx (isChart_orChart x.1) hc (hY.data x.2)
        (hY.data x.2)
        x x hκ₀ ((hY.data x.2).mem_shrink _ x.2 (hY.mem_data_V x.2) (mem_orChart x.1)) hxσ
    exact (Eq.congr_right h).trans (orientation_eq_pullOr_iff _ _ _ b)

/-- **The frame of `ker f'` given by the tangent map of `S ↪ X` along a path of `S`**: along a
path `γ` of `S` in the corner coordinates `κ` and the chart `c`, the wedges
`ι_q b₁ ∧ … ∧ ι_q bₙ` (`ι_q = solKerEquivOpen` at `γ(q)`, `b = pullBasis`) orient the kernel line
bundle `λ(tangentFamily)` (`continuousOn_deriv`: `D(σ ∘ χ⁻¹)` is continuous). -/
theorem isLineOrientation_solKer_open {c : StrongBundleChart PX P} (hc : B.IsChart c)
    (d : PX.SubData (solutionSet P f ∩ Ω)) (a₀ : ↥(solutionSet P f ∩ Ω))
    {γ : (Fin 1 → ℝ) → ↥(solutionSet P f ∩ Ω)}
    (hγs : (rnPolyfold 1).IsScSmoothMap PX (Subtype.val ∘ γ)) (hγκ : ∀ p, γ p ∈ κ.s)
    (hγσ : ∀ p, γ p ∈ (subChart d c.isChart a₀).source) (hγχ : Continuous fun p => κ.χ (γ p))
    (hγc : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, (Subtype.val ∘ γ) q ∈ c.φ.source)
    (hγ0 : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt P f ((Subtype.val ∘ γ) q))
    (hγgp : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, B.IsGeneralPositionGerm f ((Subtype.val ∘ γ) q)) :
    IsLineOrientation (tangentFamily hft hc hγs hγc hγ0 hγgp).det fun q =>
      rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin
        (solKerEquivOpen hft κ hc d a₀ (hγκ q) (hγσ q) (hgp _ (γ q).2)
          (chartPtOf c hc (hγc q q.2)
            (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2))).toBase_z
          (finrank_linKer_of hft (γ q).2.1 (hgp _ (γ q).2) (hidx _ (γ q).2) hc (hγc q q.2) _
            (chartPtOf c hc (hγc q q.2)
              (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2))).toBase_z))
        (pullBasis finrank_euclideanSpace_fin)) := by
  have hfin := κ.isCornerChart.finiteDimensional
  have hσ := subPolyfold_isChart hY d c.isChart a₀
  have q₀ : Icc (0 : Fin 1 → ℝ) 1 := ⟨0, left_mem_Icc.2 fun _ => zero_le_one⟩
  have hΛn : (tangentFamily hft hc hγs hγc hγ0 hγgp).n = n :=
    ((tangentFamily hft hc hγs hγc hγ0 hγgp).finrank_eq q₀).symm.trans
      (finrank_linKer_of hft (γ q₀).2.1 (hgp _ (γ q₀).2) (hidx _ (γ q₀).2) hc (hγc q₀ q₀.2) _
        (chartPtOf c hc (hγc q₀ q₀.2)
          (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q₀ q₀.2))).toBase_z).2
  have hz : Continuous fun q : Icc (0 : Fin 1 → ℝ) 1 => κ.zOf (γ q) :=
    (ContinuousLinearEquiv.continuous _).comp (hγχ.comp continuous_subtype_val)
  have hD := (isDiffeoGerm_transition κ.isCornerChart κ.isChart hσ).isSc1.isSc1With_scDeriv
    |>.continuousOn_deriv
  have hli : ∀ q : Icc (0 : Fin 1 → ℝ) 1, LinearIndependent ℝ fun i => modelDeriv κ c.isChart d a₀
      (κ.zOf (γ q)) (pullBasis finrank_euclideanSpace_fin (Fin.cast hΛn i)) := fun q => by
    have h1 := (pullBasis (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := n))).linearIndependent.comp _
      (Fin.cast_injective hΛn)
    have h2 := h1.map' (modelDeriv κ c.isChart d a₀ (κ.zOf (γ q))).toLinearMap
      (LinearMap.ker_eq_bot.2
        (modelDeriv_injective κ c.isChart d a₀ (hγκ q) (hγσ q) (κ.toBase_zOf _)))
    exact h2
  have hcont : ∀ w : EuclideanSpace ℝ (Fin n), Continuous fun q : Icc (0 : Fin 1 → ℝ) 1 =>
      modelDeriv κ c.isChart d a₀ (κ.zOf (γ q)) w := fun w => by
    have h := hD.comp_continuous (hz.prodMk (continuous_const (y := κ.Ψ.symm (ofLp w))))
      fun q => by
        change κ.χ.model.E.toBase 1 (κ.zOf (γ q)) ∈
          (overlapRet κ.isCornerChart (subChart d c.isChart a₀)).U
        rw [κ.toBase_zOf]
        exact κ.χ.mem_overlap _ (κ.s_subset (hγκ q)) (hγσ q)
    exact h
  let ε : (tangentFamily hft hc hγs hγc hγ0 hγgp).Frame :=
    { U := univ
      isOpen := isOpen_univ
      e := fun i q => modelDeriv κ c.isChart d a₀ (κ.zOf (γ q))
        (pullBasis finrank_euclideanSpace_fin (Fin.cast hΛn i))
      continuousOn := fun i => (hcont _).continuousOn
      mem := fun q _ i => modelDeriv_mem_linKer_open κ hΩ.out hft hc d a₀ (hγκ q) (hγσ q)
        (κ.toBase_zOf _)
        (hgp _ (γ q).2) (chartPtOf c hc (hγc q q.2)
          (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2))).toBase_z _
      linearIndependent := fun q _ => hli q }
  refine (ε.isLineOrientation rfl).congr fun q => rayOfNeZero_congr ?_ _ _
  rw [SubspaceFamily.Frame.wedgeAt_of_mem _ (mem_univ q)]
  refine Eq.trans ?_ (wedge_cast _ _ hΛn)
  congr 1


/-- **The reading of `o` is locally constant on `S`** (the continuity in Theorem 6.6.18): near
`x₀`, in an orientable neighbourhood of `x₀` (`exists_isOrientableNbhd`, which needs the bump
functions) and the corner coordinates `κ`, every `y` is joined to `x₀` by a segment
(`eventually_exists_segPath`); along it `tangentOr(o)` and the frame of
`isLineOrientation_solKer_open` are two orientations of the kernel line bundle
(`isLineOrientation_tangentOr_of_isSectionOrientation`), which
agree at both ends or at neither (`IsLineOrientation.eq_iff_eq`). -/
theorem eventually_solReadOr_eq_open (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    {x₀ : ↥(solutionSet P f ∩ Ω)} (hx₀ : x₀ ∈ κ.s) :
    ∃ (c : StrongBundleChart PX P) (hc : B.IsChart c) (d : PX.SubData (solutionSet P f ∩ Ω))
      (hxσ₀ : x₀ ∈ (subChart d c.isChart x₀).source),
      ∀ᶠ y in 𝓝 x₀, ∃ (hyκ : y ∈ κ.s) (hyσ : y ∈ (subChart d c.isChart x₀).source),
        solReadOrOpen hft κ o hgp hidx hc d x₀ hyκ hyσ =
          solReadOrOpen hft κ o hgp hidx hc d x₀ hx₀ hxσ₀ := by
  have := paracompactSpace_rn_prod PX
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_rn_prod PX
  have := paracompactSpace_rn_rn_pullback B
  have hs₀ := hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x₀.2.1
  obtain ⟨c, hc, U, V, hN⟩ := exists_isOrientableNbhd hX hbump hft hs₀
  have hVc : ∀ {y : X}, y ∈ V → y ∈ c.φ.source := fun hy =>
    hN.hasLocalPropagation.subset (hN.subset hy)
  have hxσ₀ : x₀ ∈ (subChart (hY.data x₀.2) c.isChart x₀).source :=
    (hY.data x₀.2).mem_shrink c.φ x₀.2 (hY.mem_data_V x₀.2) (hVc hN.mem)
  refine ⟨c, hc, hY.data x₀.2, hxσ₀, ?_⟩
  have hG : IsOpen ((subChart (hY.data x₀.2) c.isChart x₀).source ∩ Subtype.val ⁻¹' V) :=
    (subChart _ c.isChart x₀).isOpen_source.inter (hN.isOpen_V.preimage continuous_subtype_val)
  filter_upwards [eventually_exists_segPath κ hx₀ hG ⟨hxσ₀, hN.mem⟩] with y hy
  obtain ⟨hyκ, γ, hγs, hγ0', hγ1', hγG, hγχ⟩ := hy
  have hyσ : y ∈ (subChart (hY.data x₀.2) c.isChart x₀).source := hγ1' ▸ (hγG 1).2.1
  refine ⟨hyκ, hyσ, ?_⟩
  have hγsX : (rnPolyfold 1).IsScSmoothMap PX (Subtype.val ∘ γ) :=
    (subPolyfold_inclusion_isScSmooth hY).comp hγs
  have hγV : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, (Subtype.val ∘ γ) q ∈ V := fun q _ => (hγG q).2.2
  have hγZ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt P f ((Subtype.val ∘ γ) q) := fun q _ =>
    (γ q).2.1
  have hγcont : Continuous fun p => κ.χ (γ p) := by
    simp only [hγχ]
    exact continuous_const.add ((Real.smoothTransition.continuous.comp (continuous_apply 0)).smul
      continuous_const)
  have hT := isLineOrientation_tangentOr_of_isSectionOrientation hft o.2 hs₀ hN hγsX hγV hγZ
    fun q _ => hgp _ (γ q).2
  have hL := isLineOrientation_solKer_open hft κ hgp hidx hc (hY.data x₀.2) x₀ hγsX
    (fun p => (hγG p).1)
    (fun p => (hγG p).2.1) hγcont (fun q hq => hVc (hγV q hq)) hγZ
    (fun q _ => hgp _ (γ q).2)
  have : PreconnectedSpace (Icc (0 : Fin 1 → ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.1 (convex_Icc 0 1).isPreconnected
  have hiff := IsLineOrientation.eq_iff_eq hT hL ⟨1, right_mem_Icc.2 fun _ => zero_le_one⟩
    ⟨0, left_mem_Icc.2 fun _ => zero_le_one⟩
  refine (solReadOr_congr_open hft κ o hgp hidx hc _ x₀ hγ1'.symm hyκ hyσ (hγG 1).1
    (hγG 1).2.1).trans ?_
  refine (pullOr_eq_of_iff _ hiff).trans ?_
  exact solReadOr_congr_open hft κ o hgp hidx hc _ x₀ hγ0' (hγG 0).1 (hγG 0).2.1 hx₀ hxσ₀

/-- **`solOrOpen` is a continuous tangent orientation of the Mathlib manifold `S`**: read in the
corner coordinates at `x₀` it is locally constant (`eventually_solReadOr_eq_open`,
`orientationIn_solOr_open`, `TangentOrientation.isContinuous_of_forall`). -/
theorem isContinuous_solOr_open (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    [inst : ChartedSpace (EuclideanQuadrant n) ↥(solutionSet P f ∩ Ω)]
    (hch : inst = (subPolyfold hY).cornerChartedSpace hcs) :
    TangentOrientation.IsContinuous (𝓠 n) ∞
      (fun x => modelOrToTangent x (solOrOpen hft o hgp hidx hcs x)) := by
  have := isManifold_of_eq hcs hch
  refine TangentOrientation.isContinuous_of_forall (by simp) fun x₀ => ?_
  obtain ⟨κ, hx₀⟩ := hcs.exists_cornerCoords x₀
  obtain ⟨c, hc, d, hxσ₀, hev⟩ := eventually_solReadOr_eq_open hft κ o hgp hidx hX hbump hx₀
  refine ⟨κ.toQuadrantChart, mem_maximalAtlas_of_eq hcs hch κ, hx₀, ?_⟩
  filter_upwards [hev] with y hy
  obtain ⟨hyκ, hyσ, hy⟩ := hy
  rw [orientationIn_solOr_open hft κ o hgp hidx hcs hch hc d x₀ hyκ hyσ,
    orientationIn_solOr_open hft κ o hgp hidx hcs hch hc d x₀ hx₀ hxσ₀, hy]

end Orient


/-! ### `S ∩ V` as an oriented Mathlib manifold -/

section Main

open MPolyfold

local notation "𝓠" => modelWithCornersEuclideanQuadrant

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y} {V : Set X}

/-- **`S ∩ V` is a `d`-dimensional submanifold** (2021 Theorem 3.6.8 (2), (3), p. 136; preprint
Theorem 3.54) when every zero in the open `V` is in general position with index `d`
(`theorem_3_6_8_isSubmanifoldOfDim` with the index given on `V`). -/
theorem isSubmanifoldOfDim_inter_open (hft : B.IsScFredholmSectionTame f) (hV : IsOpen V)
    (hgp : ∀ x ∈ V, IsZeroAt P f x → B.IsGeneralPositionGerm f x) {d : ℕ}
    (hidx : ∀ y ∈ V, IsZeroAt P f y → B.IsLinOfIndex f y d) :
    PX.IsSubmanifoldOfDim (solutionSet P f ∩ V) d := by
  have hall : ∀ y ∈ V, IsZeroAt P f y → B.IsGoodPositionGermTame f y := fun y hy hy0 =>
    (hgp y hy hy0).isGoodPositionGermTame hft hy0
  have hA : PX.IsSmoothSubmanifold (solutionSet P f ∩ V) :=
    StrongBundle.isSmoothSubmanifold_solutionSet_inter hft.isScSmooth.1 hV hall
  refine ⟨hA, fun y hy => ?_⟩
  obtain ⟨V', hV'o, hyV', -, hA', hdim⟩ := StrongBundle.hasDimAt_solutionSet_inter hft
    (hall y hy.2 hy.1) hy.1 (StrongBundle.isSurjLinOfIndex_of_isLinSurjAt hft.isScSmooth hy.1
      (hgp y hy.2 hy.1).isLinSurjAt (hidx y hy.2 hy.1))
  have h1 : PX.HasDimAt ((solutionSet P f ∩ V') ∩ V) y d :=
    (MPolyfold.hasDimAt_inter_isOpen_iff hA' hV hy.2).2 hdim
  rw [inter_right_comm] at h1
  exact (MPolyfold.hasDimAt_inter_isOpen_iff hA hV'o hyV').1 h1

/-- **`S ∩ V` is in good position** (2021 Lemma 4.2.8, p. 166; preprint Lemma 4.19) at every point
when every zero in the open `V` is in general position (`exists_isOpen_isGeneralPositionGerm`). -/
theorem isGoodPositionAt_inter_open (hX : PX.IsTame) (hft : B.IsScFredholmSectionTame f)
    (hV : IsOpen V) (hgp : ∀ x ∈ V, IsZeroAt P f x → B.IsGeneralPositionGerm f x) :
    ∀ y ∈ solutionSet P f ∩ V, PX.IsGoodPositionAt (solutionSet P f ∩ V) y := by
  have hSm : PX.IsSmoothSubmanifold (solutionSet P f ∩ V) :=
    StrongBundle.isSmoothSubmanifold_solutionSet_inter hft.isScSmooth.1 hV fun y hy hy0 =>
      (hgp y hy hy0).isGoodPositionGermTame hft hy0
  intro y hy
  obtain ⟨W, hWo, hyW, hWA, hW⟩ := exists_isOpen_isGeneralPositionGerm hX hft hy.1 (hgp y hy.2 hy.1)
  refine (MPolyfold.IsGeneralPositionAt.congr_nhds hWA hSm (hWo.inter hV) ⟨hyW, hy.2⟩ ?_
    (hW y hyW hy.1).2.2).isGoodPositionAt hX hSm
  ext w
  simp only [mem_inter_iff]
  tauto

/-- **The charted space of `S ∩ V`**: the corner structure of dimension `d` induced from `X`
(`hasCornerStructureOfDim_of_tame`, with `isSubmanifoldOfDim_inter_open` and
`isGoodPositionAt_inter_open`). -/
abbrev solChartedSpaceOpen (hX : PX.IsTame) (hft : B.IsScFredholmSectionTame f) (hV : IsOpen V)
    (hgp : ∀ x ∈ V, IsZeroAt P f x → B.IsGeneralPositionGerm f x) {d : ℕ}
    (hidx : ∀ y ∈ V, IsZeroAt P f y → B.IsLinOfIndex f y d) :
    ChartedSpace (EuclideanQuadrant d) ↥(solutionSet P f ∩ V) :=
  letI := PX.paracompactSpace_subtype (solutionSet P f ∩ V)
  (MPolyfold.subPolyfold
    (isSubmanifoldOfDim_inter_open hft hV hgp hidx).1.isSubMPolyfold).cornerChartedSpace
    ((isSubmanifoldOfDim_inter_open hft hV hgp hidx).hasCornerStructureOfDim_of_tame hX
      (isGoodPositionAt_inter_open hX hft hV hgp))

/-- **Theorem 6.6.18 for an open part of the solution set** (2021, p. 275; preprint Theorem 6.41),
the orientation part without properness: over a tame `X` with sc-smooth bump functions, let `f` be
an sc-Fredholm section (tame germ data), `o` an orientation of `f` (Definition 6.6.16, p. 273) and
`V` open such that every zero in `V` is in general position with index `d`. Then `S ∩ V` (with
`solChartedSpaceOpen`) is a Hausdorff smooth manifold with boundary and corners, σ-compact when
`S ∩ V` is, carrying a continuous tangent orientation `oS` which at every `x` is `o_x` on
`T_x(S ∩ V) = ker f'(x)`, in the form of `theorem_6_6_18_oriented`. The book's theorem is the
case `V = X` with `S` compact; `hbump` is the added hypothesis of `theorem_6_6_18_oriented`. -/
theorem theorem_6_6_18_oriented_open (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hft : B.IsScFredholmSectionTame f) (hV : IsOpen V)
    (hgp : ∀ x ∈ V, IsZeroAt P f x → B.IsGeneralPositionGerm f x) {d : ℕ}
    (hidx : ∀ y ∈ V, IsZeroAt P f y → B.IsLinOfIndex f y d)
    (o : SectionOrientation f hft.toIsScFredholmSection) :
    letI := solChartedSpaceOpen hX hft hV hgp hidx
    IsManifold (𝓠 d) ∞ ↥(solutionSet P f ∩ V) ∧ T2Space ↥(solutionSet P f ∩ V) ∧
      (IsSigmaCompact (solutionSet P f ∩ V) → SigmaCompactSpace ↥(solutionSet P f ∩ V)) ∧
      ∃ oS : TangentOrientation (𝓠 d) ↥(solutionSet P f ∩ V) d, oS.IsContinuous (𝓠 d) ∞ ∧
        ∀ (x : ↥(solutionSet P f ∩ V)) (c : StrongBundleChart PX P) (hc : B.IsChart c)
          (hxc : x.1 ∈ c.φ.source),
          ∃ ι : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] c.linKer f (chartPtOf c hc hxc
              (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2.1)).z,
            (∀ v, (ι v : c.φ.model.E 0) = derivIn (𝓠 d) (chartAt (EuclideanQuadrant d) x)
              (fun y : ↥(solutionSet P f ∩ V) => c.φ y.1) x v) ∧
            ∀ b : Basis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)),
              b.orientation = tangentOrToModel (oS x) ↔
                (chartPtOf c hc hxc
                    (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2.1)).tangentOr
                  hft.toIsScFredholmSection x.2.1 (hgp x.1 x.2.2 x.2.1).isLinSurjAt
                  (toChartOr hft.toIsScFredholmSection
                    (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2.1) c hc hxc
                    (o.1 x.1 (hft.toIsScFredholmSection.mem_smoothSet_of_isZeroAt x.2.1))) =
                  rayOfNeZero ℝ _ (wedge_equiv_ne_zero finrank_euclideanSpace_fin ι b) := by
  let := PX.paracompactSpace_subtype (solutionSet P f ∩ V)
  have : Fact (IsOpen V) := ⟨hV⟩
  have h1 := isSubmanifoldOfDim_inter_open hft hV hgp hidx
  have hcs := h1.hasCornerStructureOfDim_of_tame hX (isGoodPositionAt_inter_open hX hft hV hgp)
  let := solChartedSpaceOpen hX hft hV hgp hidx
  have hgp' : ∀ x ∈ solutionSet P f ∩ V, B.IsGeneralPositionGerm f x := fun x hx =>
    hgp x hx.2 hx.1
  have hidx' : ∀ y ∈ solutionSet P f ∩ V, B.IsLinOfIndex f y d := fun y hy => hidx y hy.2 hy.1
  exact ⟨isManifold_of_eq hcs rfl, inferInstance, fun h => isSigmaCompact_iff_sigmaCompactSpace.1 h,
    fun x => modelOrToTangent x (solOrOpen hft o hgp' hidx' hcs x),
    isContinuous_solOr_open hft o hgp' hidx' hcs hX hbump rfl,
    fun x c hc hxc => solOr_spec_open hft o hgp' hidx' hcs rfl x hc hxc⟩

end Main


/-! ### The parts of one index -/

section IndexParts

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **The index parts of `S` are cut out by open sets** (the index is locally constant along `S`,
2021 Theorem 3.6.8, p. 136, and Proposition 6.2.2; `theorem_3_6_8_index_locally_constant`): if
`f` is in general position at every zero, then for every `k` there is an open `V_k` with
`S ∩ V_k = S_k = {x ∈ S | f'(x) has index k}`. So `theorem_6_6_18_oriented_open` applies to
`S_k` with `V = V_k` and `d = k`. -/
theorem exists_isOpen_inter_eq_index (hft : B.IsScFredholmSectionTame f)
    (hgp : ∀ x, IsZeroAt P f x → B.IsGeneralPositionGerm f x) (k : ℕ) :
    ∃ V : Set X, IsOpen V ∧
      solutionSet P f ∩ V = {x ∈ solutionSet P f | B.IsLinOfIndex f x k} := by
  choose Vx d hVo hxV hind using fun x : solutionSet P f =>
    theorem_3_6_8_index_locally_constant hft ((hgp x.1 x.2).isGoodPositionGermTame hft x.2) x.2
  refine ⟨⋃ x ∈ {x : solutionSet P f | d x = k}, Vx x, isOpen_biUnion fun x _ => hVo x, ?_⟩
  ext y
  simp only [mem_inter_iff, mem_iUnion, mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨hy, x, hxk, hyV⟩
    refine ⟨hy, ?_⟩
    have := (hind x y hyV hy).isLinOfIndex
    rwa [hxk] at this
  · rintro ⟨hy, hk⟩
    refine ⟨hy, ⟨y, hy⟩, ?_, hxV _⟩
    have h := (hind ⟨y, hy⟩ y (hxV _) hy).isLinOfIndex
    exact_mod_cast StrongBundle.IsLinOfIndex.unique hft.toIsScFredholmSection hy h hk

/-- **The index parts of `S` are clopen in `S`** (R-c of the Theorem 6.7.1 plan): for `f` in general
position at every zero, `{x ∈ S | f'(x) has index k}` is open and closed in `S`. -/
theorem isClopen_index_part (hft : B.IsScFredholmSectionTame f)
    (hgp : ∀ x, IsZeroAt P f x → B.IsGeneralPositionGerm f x) (k : ℕ) :
    IsClopen {x : solutionSet P f | B.IsLinOfIndex f x.1 k} := by
  choose Vx d hVo hxV hind using fun x : solutionSet P f =>
    theorem_3_6_8_index_locally_constant hft ((hgp x.1 x.2).isGoodPositionGermTame hft x.2) x.2
  have hidx : ∀ x y : solutionSet P f, y.1 ∈ Vx x →
      (B.IsLinOfIndex f y.1 k ↔ d x = k) := fun x y hy => by
    have h := (hind x y.1 hy y.2).isLinOfIndex
    constructor
    · intro hk
      exact_mod_cast StrongBundle.IsLinOfIndex.unique hft.toIsScFredholmSection y.2 h hk
    · intro hxk
      rwa [hxk] at h
  have hopen : ∀ j : ℕ → Prop, IsOpen {y : solutionSet P f | ∃ x, j (d x) ∧ y.1 ∈ Vx x} :=
    fun j => by
      have : {y : solutionSet P f | ∃ x, j (d x) ∧ y.1 ∈ Vx x} =
          ⋃ x ∈ {x | j (d x)}, Subtype.val ⁻¹' Vx x := by
        ext y; simp
      rw [this]
      exact isOpen_biUnion fun x _ => (hVo x).preimage continuous_subtype_val
  have e1 : {x : solutionSet P f | B.IsLinOfIndex f x.1 k} =
      {y : solutionSet P f | ∃ x, d x = k ∧ y.1 ∈ Vx x} := by
    ext y
    exact ⟨fun h => ⟨y, (hidx y y (hxV y)).1 h, hxV y⟩,
      fun ⟨x, hx, hy⟩ => (hidx x y hy).2 hx⟩
  have e2 : {x : solutionSet P f | B.IsLinOfIndex f x.1 k}ᶜ =
      {y : solutionSet P f | ∃ x, d x ≠ k ∧ y.1 ∈ Vx x} := by
    ext y
    simp only [mem_compl_iff, mem_ofPred_eq]
    exact ⟨fun h => ⟨y, fun hk => h ((hidx y y (hxV y)).2 hk), hxV y⟩,
      fun ⟨x, hx, hy⟩ h => hx ((hidx x y hy).1 h)⟩
  refine ⟨?_, ?_⟩
  · rw [← isOpen_compl_iff, e2]; exact hopen (· ≠ k)
  · rw [e1]; exact hopen (· = k)

end IndexParts

end Polyfold
