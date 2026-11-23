import Polyfold.Chapter15.CylinderOrientationLocalIso
import Polyfold.Chapter12.ChartTransportCommute
import Polyfold.Chapter12.LocalOrientationIsoTransport
import Polyfold.Chapter12.LocalOrientationEquivalenceComparison
import Polyfold.Chapter15.CanonicalLiftContinuityLocal
import Polyfold.Chapter15.CylinderCanonicalOrientation
import Polyfold.Chapter15.CubeSectionsThrough

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, pp. 702–703
(**Theorem 15.4.1**, 2017: Theorem 15.6, on the cylinder of the proof of Corollary 15.4.4),
with Part I, §6.6, Definition 6.6.16 (p. 274) and **Remark 6.6.19** (p. 276).

# The orientation `õ = e ∧ o` on `[0, 1] × X` is an orientation made with local sc⁺-sections

## The text, paraphrased

(p. 703) On `[0, 1] × X` the section `f̃(t, x) = (t, f(x))` is oriented by the standard
orientation of `[0, 1]` followed by the orientation `o` of `f` (Remark 6.6.19).  An orientation
is a family `o_y ∈ Or_y^f` which near every smooth point is carried along by the propagation
along sc-smooth paths (Definition 6.6.16); the sets `Or_y^f` and the propagation are made with
sc⁺-sections defined near the point.

## What is formalized

No sc-smooth bump functions are used.

* `StrongBundle.LocalIso.orxVia_comm_local_of_isPush`: for a local strong bundle isomorphism
  `L` from a bundle with a chart over its whole base, the transport along a short path `γ` is
  every push-forward of the target section along `ϕ ∘ γ`, read through the orientation map of
  `L`.
* `hasScPlusSectionsThrough_ivBundle`: sc⁺-sections through the smooth fibre points of the
  pull-back to `[0, 1] × X`.
* `isSectionOrientationLoc_ivFirstFun_of_chart`: over a bundle with a chart over its whole base,
  `(t, x) ↦ e ∧ o_x` is an orientation of `f̃` made with local sc⁺-sections if `o` is an
  orientation of `f`.
* **`isSectionOrientationLoc_ivFirstFun`**: the same over any strong bundle over a tame
  M-polyfold with sc⁺-sections through the smooth fibre points, for an orientation `o` made
  with local sc⁺-sections.
* **`SBLocalization.isSectionOrientationLoc_cubeOrientation`**: the statement for `A : SEP`.
* **`SBLocalization.theorem_15_4_1_cylinder_loc`**: Theorem 15.4.1 on the cylinder.
* `SBLocalization.canonContinuous_cubeOrientation_loc`: the orientations of the kernels induced
  by `õ` are continuous along the sheets.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

open StrongRetr UnitCube

universe u v u' v'

/-! ### The transport and a push-forward of the target section -/

section Comm

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'}

namespace StrongBundle.LocalIso

variable {U' : Set X'} (L : LocalIso B B' univ U')

variable [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X')]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P' (Prod.snd : (Fin n → ℝ) × X' → X'))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

variable (hX : PX.IsTame) (hch : ∃ c ∈ B.atlas.charts, c.φ.source = univ)
  (hf : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough)
  (hcg : ∃ cg ∈ B'.atlas.charts, U' ⊆ cg.φ.source)
  (hf' : B'.IsScFredholmSection f')
  (hsec' : B'.HasScPlusSectionsThrough) (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) univ)

include hcg in
/-- **The transport on short paths is every push-forward of the target section, read through
`L`** (the local half of the last sentence of Theorem 12.5.3, p. 594, with a given
push-forward): let `Y` have a chart over its whole base and `L : Y → Y'|U'` be defined on all
of `X`, with `U'` inside the base domain of a chart of `Y'`.  Every smooth `a₀` has an open
neighbourhood `V` such that for every sc-smooth path `γ` in `V` and every push-forward `e'` of
`f'` along `ϕ ∘ γ` in a chart `c'` of `Y'`, the orientation map of `L` followed by the
transport of `f` along `γ` is `e'`, read in the chosen charts, followed by the orientation map
of `L`. -/
theorem orxVia_comm_local_of_isPush {a₀ : X} (has₀ : a₀ ∈ PX.smoothSet) :
    ∃ V : Set X, IsOpen V ∧ a₀ ∈ V ∧ ∀ (γ : (Fin 1 → ℝ) → X)
      (hγ : (rnPolyfold 1).IsScSmoothMap PX γ),
      (∀ t ∈ Icc (0 : ℝ) 1, γ (pt1 t) ∈ V) →
      ∀ (hs₀ : γ (pt1 0) ∈ PX.smoothSet) (hs₁ : γ (pt1 1) ∈ PX.smoothSet)
        (c' : StrongBundleChart PX' P') (hc' : B'.IsChart c')
        (hγc' : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, L.ϕ (γ q) ∈ c'.φ.source)
        (hx₀ : L.ϕ (γ (pt1 0)) ∈ c'.φ.source) (hx₁ : L.ϕ (γ (pt1 1)) ∈ c'.φ.source)
        (e' : (chartPtOf c' hc' hx₀ ((L.mem_smoothSet_iff (mem_univ _)).1 hs₀)).Or f' hf' ≃
          (chartPtOf c' hc' hx₁ ((L.mem_smoothSet_iff (mem_univ _)).1 hs₁)).Or f' hf'),
        IsPush f' hf' c' hc' (fun q => L.ϕ (γ q)) hγc' rfl rfl hx₀ hx₁
          ((L.mem_smoothSet_iff (mem_univ _)).1 hs₀) ((L.mem_smoothSet_iff (mem_univ _)).1 hs₁)
          e' →
        (L.orxVia hf.toIsScFredholmSection hf' hfL hsec hsec' (mem_univ _) hs₀).trans
          ((orLocalTransportOfChart hX hch hf hsec).transport γ hγ rfl rfl hs₀ hs₁) =
        ((toChartOr hf' ((L.mem_smoothSet_iff (mem_univ _)).1 hs₀) c' hc' hx₀).trans
          (e'.trans (toChartOr hf' ((L.mem_smoothSet_iff (mem_univ _)).1 hs₁) c' hc'
            hx₁).symm)).trans
          (L.orxVia hf.toIsScFredholmSection hf' hfL hsec hsec' (mem_univ _) hs₁) := by
  obtain ⟨cB, hcB, VB, hVBo, haVB, hLP⟩ := theorem_6_6_11_of_chart hX hch hf has₀
  obtain ⟨cg, hcgA, hcgs⟩ := hcg
  have hcg : B'.IsChart cg := B'.isChart_of_mem hcgA
  refine ⟨VB, hVBo, haVB, ?_⟩
  intro γ hγ hγV hs₀ hs₁ c' hc' hγc' hx₀ hx₁ e' he'
  have hγV' := forall_mem_of_forall_pt1_mem hγV
  have hγc : Continuous γ := continuousOn_univ.1 hγ.continuousOn
  have hγU : ∀ q, γ q ∈ (univ : Set X) := fun _ => mem_univ _
  have hϕγ := L.isScSmoothMap_comp_or hγ hγU
  have hs₀' := (L.mem_smoothSet_iff (mem_univ (γ (pt1 0)))).1 hs₀
  have hs₁' := (L.mem_smoothSet_iff (mem_univ (γ (pt1 1)))).1 hs₁
  have hc₀ : B'.IsChart (cg.restrictInter L.isOpen_U') := hcg.restrictInter L.isOpen_U'
  have hsub₀ : (cg.restrictInter L.isOpen_U').φ.source ⊆ U' := fun _ hy => hy.2
  have hW : IsOpen (univ : Set X') := isOpen_univ
  -- the transported chart has base domain `X`
  have hT : ∀ x : X, x ∈ (L.transportChart
      ((cg.restrictInter L.isOpen_U').restrictInter hW) fun _ hy => hsub₀ hy.1).φ.source :=
    fun x => ⟨mem_univ x, ⟨hcgs (L.base.mapsTo (mem_univ x)), L.base.mapsTo (mem_univ x)⟩,
      mem_univ _⟩
  have hβ : PX.IsScSmoothMap realPolyfold (fun _ : X => (1 : ℝ)) := isScSmoothMap_real_const 1
  have hβs : tsupport (fun _ : X => (1 : ℝ)) ⊆ (L.transportChart _ hsub₀).φ.source :=
    fun x _ => ⟨mem_univ x, hcgs (L.base.mapsTo (mem_univ x)), L.base.mapsTo (mem_univ x)⟩
  have hγT : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ (L.transportChart
      ((cg.restrictInter L.isOpen_U').restrictInter hW) fun _ hy => hsub₀ hy.1).φ.source :=
    fun q _ => hT (γ q)
  have hγB : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ VB := fun q hq => hγV' q hq
  have m0 := pt1_mem_Icc (left_mem_Icc.2 (zero_le_one : (0 : ℝ) ≤ 1))
  have m1 := pt1_mem_Icc (right_mem_Icc.2 (zero_le_one : (0 : ℝ) ≤ 1))
  have he'W := IsPush.transfer hc' (hc₀.restrictInter hW) hϕγ hγc'
    (fun q hq => (hγT q hq).2) rfl rfl hx₀ hx₁ (hγT _ m0).2 (hγT _ m1).2 hs₀' hs₁' he'
  have heT := L.isPush_mpull hf.toIsScFredholmSection hf' hfL hsec hsec'
    hc₀ hsub₀ hW hβ hβs (fun _ _ => rfl) hγc hγT hs₀ hs₁ hs₀' hs₁' he'W
  have heB := IsPush.transfer (L.isChart_transportChart _ _ (hc₀.restrictInter hW)) hcB hγ hγT
    (fun q hq => hLP.subset (hγB q hq)) rfl rfl (hγT _ m0) (hγT _ m1)
    (hLP.subset (hγB _ m0)) (hLP.subset (hγB _ m1)) hs₀ hs₁ heT
  rw [orLocalTransportOfChart_transport_eq hX hch hf hsec hLP hVBo hγ hγB rfl rfl hs₀ hs₁
      (hLP.subset (hγB _ m0)) (hLP.subset (hγB _ m1)) heB,
    L.orxVia_eq_morVia _ _ hfL hsec hsec' (mem_univ _) hs₀
      (chartPtOf ((cg.restrictInter L.isOpen_U').restrictInter hW) (hc₀.restrictInter hW)
        (hγT _ m0).2 hs₀') (fun _ hy => hsub₀ hy.1),
    L.orxVia_eq_morVia _ _ hfL hsec hsec' (mem_univ _) hs₁
      (chartPtOf ((cg.restrictInter L.isOpen_U').restrictInter hW) (hc₀.restrictInter hW)
        (hγT _ m1).2 hs₁') (fun _ hy => hsub₀ hy.1)]
  exact equiv_comm_square_or _ _ _ _ _ _ (ChartPoint.orTransfer_trans _ _ _ _ _)
    (ChartPoint.orTransfer_trans _ _ _ _ _) _ _ _ _ _ _ _ _
    (ChartPoint.orTransfer_trans _ _ _ _ _) (ChartPoint.orTransfer_trans _ _ _ _ _) _

end StrongBundle.LocalIso

end Comm

/-! ### The orientation `e ∧ o` over `[0, 1] × X` -/

section Iv

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] {f : X → Y}
  [ParacompactSpace ((Fin 1 → unitInterval) × X)]
  [ParacompactSpace (pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))]
  [∀ k : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin 1 → unitInterval) × X))]
  [∀ k : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P
    (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin 1 → unitInterval) × X) → (Fin 1 → unitInterval) × X))]

/-- **Sc⁺-sections through the smooth fibre points of the pull-back to `[0, 1] × X`**, from
those of `P`, by lifting (`isScPlusSection_cubeLift`). -/
theorem hasScPlusSectionsThrough_ivBundle (hsec : B.HasScPlusSectionsThrough) :
    (ivBundle B).HasScPlusSectionsThrough := by
  intro z hz e he hez
  have hπ := MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX
  have hx : z.2 ∈ PX.smoothSet := prod_cube_mem_smoothSet_iff.1 hz
  have he' : e.1.2 ∈ B.toMPolyfold0.smoothSet :=
    mem_iInter.2 fun m => (B.isScSmoothMap_pullbackProj' hπ).mapsTo_levelSet m
      (mem_iInter.1 he m)
  have hPe : P e.1.2 = z.2 := e.2.trans (congrArg Prod.snd hez)
  obtain ⟨s, hs, hsx⟩ := hsec z.2 hx e.1.2 he' hPe
  exact ⟨cubeLift (n := 1) s hs.1, isScPlusSection_cubeLift hs,
    Subtype.ext (Prod.ext hez.symm hsx)⟩

/-- **`(t, x) ↦ e ∧ o_x` read in a product chart**: in the product chart `χ_b × φ_c`, for any
chart `c` of `X` at `x` and any chart `χ_b` of `[0, 1]` at `t`, it is `e ∧ (o_x read in c)`. -/
theorem toChartOr_ivFirstFun_ivChart (hf : B.IsScFredholmSection f)
    (hfc : (ivBundle B).IsScFredholmSection (cubeLift (n := 1) f hf.isScSmooth.1))
    (hsec : B.HasScPlusSectionsThrough) (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy)
    (z : (Fin 1 → unitInterval) × X) (hz : z ∈ ((cubePolyfold 1).prod PX).smoothSet)
    (b : Fin 1 → Bool) (hb : z.1 ∈ (chart b).source)
    {c : StrongBundleChart PX P} (hc : B.IsChart c) (hxc : z.2 ∈ c.φ.source)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X))
    (hne : ((chartPtOf c hc hxc (prod_cube_mem_smoothSet_iff.1 hz)).linSet f).Nonempty) :
    toChartOr hfc hz (ivChart b c q₀) (isChart_ivChart b hc q₀) (mem_ivChart_source q₀ hxc hb)
        (ivFirstFun hf hfc hsec o z hz) =
      ivOrOf b hc hxc (prod_cube_mem_smoothSet_iff.1 hz) hb q₀ hf hfc hne
        (toChartOr hf (prod_cube_mem_smoothSet_iff.1 hz) c hc hxc
          (o z.2 (prod_cube_mem_smoothSet_iff.1 hz))) := by
  have h := toChartOr_ivFirstFun hf hfc hsec o z hz b hb hc hxc q₀ (isChart_ivChart b hc q₀)
    (mem_ivChart_source q₀ hxc hb) hne
  refine h.trans ?_
  rw [ChartPoint.orTransfer_self]
  rfl

/-- **Over a bundle with a chart over its whole base, `(t, x) ↦ e ∧ o_x` is an orientation of
`f̃` made with local sc⁺-sections** (2021 Remark 6.6.19 and Definition 6.6.16) when `o` is an
orientation of `f`.  At `z = (t, x)`, boundary points included: in a domain `W ∋ z` inside
`dom χ_b × V`, for the corner chart `χ_b` at `t` and an orientable neighbourhood `V` of `f`,
the transport of `f̃|W` along a short path `γ` is the lift of a push-forward of `f` along
`pr₂ ∘ γ` (`IsPush.ivLift`, `LocalIso.orxVia_comm_local_of_isPush` for the inclusion of `W`),
which carries `e ∧ o` to `e ∧ o`. -/
theorem isSectionOrientationLoc_ivFirstFun_of_chart (hX : PX.IsTame)
    (hch : ∃ c ∈ B.atlas.charts, c.φ.source = univ) (hf : B.IsScFredholmSectionTame f)
    (hsec : B.HasScPlusSectionsThrough) (hsecc : (ivBundle B).HasScPlusSectionsThrough)
    {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy}
    (ho : IsSectionOrientation f hf.toIsScFredholmSection o) :
    IsSectionOrientationLoc (prod_cube_isTame (n := 1) hX) (hf.paramCube (n := 1))
      fun z hz => orxLocEquiv (hf.paramCube (n := 1)) hsecc z hz
        (ivFirstFun hf.toIsScFredholmSection (hf.paramCube (n := 1)).toIsScFredholmSection hsec
          o z hz) := by
  have := paracompactSpace_rn_rn_prod PX
  have := paracompactSpace_rn_rn_pullback B
  have hXC : ((cubePolyfold 1).prod PX).IsTame := prod_cube_isTame hX
  have hfT := hf.paramCube (n := 1)
  have hfc := hfT.toIsScFredholmSection
  intro z hz
  have hs := prod_cube_mem_smoothSet_iff.1 hz
  obtain ⟨c, hc, U, V, hN⟩ := exists_isOrientableNbhd_of_chart hX hch hf hs
  have hUc := hN.hasLocalPropagation.subset
  set b₀ := corner z.1 with hb₀
  have hWo : IsOpen (Prod.snd ⁻¹' V ∩ Prod.fst ⁻¹' (chart b₀).source :
      Set ((Fin 1 → unitInterval) × X)) :=
    (hN.isOpen_V.preimage continuous_snd).inter ((chart b₀).isOpen_source.preimage continuous_fst)
  have hzW : z ∈ (Prod.snd ⁻¹' V ∩ Prod.fst ⁻¹' (chart b₀).source :
      Set ((Fin 1 → unitInterval) × X)) := ⟨hN.mem, mem_chart_corner z.1⟩
  set D : (ivBundle B).Dom := ((ivBundle B).domAt z).restrict hWo
    ⟨z, (ivBundle B).mem_domAt z, hzW⟩ with hD
  have hzD : z ∈ D.carrier := ⟨(ivBundle B).mem_domAt z, hzW⟩
  have hfL := (ivBundle B).restrictSection_eqOn_restrictIso D.isOpen hfT.isScSmooth.1
  obtain ⟨VE, hVEo, hzVE, hcomm⟩ :=
    ((ivBundle B).restrictIso D.isOpen).orxVia_comm_local_of_isPush (D.isTame hXC)
      D.exists_chart_univ (D.isFredholm hfT) D.hasSections D.exists_chart hfc hsecc hfL
      (a₀ := ⟨z, hzD⟩) (StrongBundle.Dom.mem_smoothSet hzD hz)
  have hUo : IsOpen (Subtype.val '' VE : Set ((Fin 1 → unitInterval) × X)) :=
    D.isOpen.isOpenMap_subtype_val _ hVEo
  refine ⟨Subtype.val '' VE, ⟨⟨z, hzD⟩, hzVE, rfl⟩, ?_⟩
  rw [D.isContOn_iff hXC hfT hUo (by rintro _ ⟨w, -, rfl⟩; exact w.2) _,
    preimage_image_eq _ Subtype.val_injective]
  refine ⟨hVEo, fun γ hγ hγV w₀ w₁ h₀ h₁ hw₀ hw₁ => ?_⟩
  subst h₀ h₁
  have q₀ : pullbackSpace P (Prod.snd : (Fin 1 → unitInterval) × X → X) :=
    cubeLift (n := 1) f hf.isScSmooth.1 z
  have hs₀ : (γ (pt1 0)).1 ∈ ((cubePolyfold 1).prod PX).smoothSet :=
    (MPolyfold.mem_smoothSet_restrictOpen_iff D.isOpen _).1 hw₀
  have hs₁ : (γ (pt1 1)).1 ∈ ((cubePolyfold 1).prod PX).smoothSet :=
    (MPolyfold.mem_smoothSet_restrictOpen_iff D.isOpen _).1 hw₁
  have hxs₀ := prod_cube_mem_smoothSet_iff.1 hs₀
  have hxs₁ := prod_cube_mem_smoothSet_iff.1 hs₁
  have hγ₂s : (rnPolyfold 1).IsScSmoothMap PX (fun q => (γ q).1.2) :=
    (MPolyfold.isScSmoothMap_snd (cubePolyfold 1) PX).comp (D.isScSmoothMap_val_comp hγ)
  have hγ₂V : ∀ q, (γ q).1.2 ∈ V := fun q => (γ q).2.2.1
  have hτ : ∀ q, (γ q).1.1 ∈ (chart b₀).source := fun q => (γ q).2.2.2
  have hne₀ := ChartPoint.linSet_nonempty (chartPtOf c hc (hUc (hN.subset (hγ₂V (pt1 0)))) hxs₀)
    hf.toIsScFredholmSection hxs₀ hsec
  have hne₁ := ChartPoint.linSet_nonempty (chartPtOf c hc (hUc (hN.subset (hγ₂V (pt1 1)))) hxs₁)
    hf.toIsScFredholmSection hxs₁ hsec
  obtain ⟨e, he⟩ := hN.hasLocalPropagation.exists_isPush (fun q => (γ q).1.2) hγ₂s
    (fun q _ => hN.subset (hγ₂V q)) rfl rfl (hUc (hN.subset (hγ₂V (pt1 0))))
    (hUc (hN.subset (hγ₂V (pt1 1)))) hxs₀ hxs₁
  have hcont := ho z.2 hs c hc U V hN (fun q => (γ q).1.2) hγ₂s
    (fun q _ => hN.subset (hγ₂V q)) (hγ₂V (pt1 0)) (hγ₂V (pt1 1)) hxs₀ hxs₁ rfl rfl e he
  obtain ⟨e₂, he₂, he₂o⟩ := he.ivLift hfc b₀ (fun q => (γ q).1.1) (fun q _ => hτ q) q₀ rfl rfl
    (hτ (pt1 0)) (hτ (pt1 1)) hne₀ hne₁
  have key := hcomm γ hγ hγV hw₀ hw₁ (ivChart b₀ c q₀) (isChart_ivChart b₀ hc q₀)
    (fun q _ => mem_ivChart_source q₀ (hUc (hN.subset (hγ₂V q))) (hτ q))
    (mem_ivChart_source q₀ (hUc (hN.subset (hγ₂V (pt1 0)))) (hτ (pt1 0)))
    (mem_ivChart_source q₀ (hUc (hN.subset (hγ₂V (pt1 1)))) (hτ (pt1 1))) e₂ he₂
  have k₀ := toChartOr_ivFirstFun_ivChart hf.toIsScFredholmSection hfc hsec o (γ (pt1 0)).1 hs₀
    b₀ (hτ (pt1 0)) hc (hUc (hN.subset (hγ₂V (pt1 0)))) q₀ hne₀
  have k₁ := toChartOr_ivFirstFun_ivChart hf.toIsScFredholmSection hfc hsec o (γ (pt1 1)).1 hs₁
    b₀ (hτ (pt1 1)) hc (hUc (hN.subset (hγ₂V (pt1 1)))) q₀ hne₁
  have key' := DFunLike.congr_fun key
    (ivFirstFun hf.toIsScFredholmSection hfc hsec o (γ (pt1 0)).1 hs₀)
  have hpush : ∀ (w : D.carrier)
      (hw : w ∈ (((cubePolyfold 1).prod PX).restrictOpen D.isOpen).smoothSet)
      (hws : w.1 ∈ ((cubePolyfold 1).prod PX).smoothSet),
      D.pushLoc hfT (fun y hy => orxLocEquiv hfT hsecc y hy
        (ivFirstFun hf.toIsScFredholmSection hfc hsec o y hy)) w hw =
      ((ivBundle B).restrictIso D.isOpen).orxVia (D.isFredholm hfT).toIsScFredholmSection hfc
        hfL D.hasSections hsecc (mem_univ w) hw
        (ivFirstFun hf.toIsScFredholmSection hfc hsec o w.1 hws) := fun w hw hws =>
    DFunLike.congr_fun (orxLocEquiv_toLoc hfT hsecc D w.1 w.2 hws)
      (ivFirstFun hf.toIsScFredholmSection hfc hsec o w.1 hws)
  have hfin : (toChartOr hfc hs₁ (ivChart b₀ c q₀) (isChart_ivChart b₀ hc q₀)
      (mem_ivChart_source q₀ (hUc (hN.subset (hγ₂V (pt1 1)))) (hτ (pt1 1)))).symm
      (e₂ (toChartOr hfc hs₀ (ivChart b₀ c q₀) (isChart_ivChart b₀ hc q₀)
        (mem_ivChart_source q₀ (hUc (hN.subset (hγ₂V (pt1 0)))) (hτ (pt1 0)))
        (ivFirstFun hf.toIsScFredholmSection hfc hsec o (γ (pt1 0)).1 hs₀))) =
      ivFirstFun hf.toIsScFredholmSection hfc hsec o (γ (pt1 1)).1 hs₁ :=
    (Equiv.symm_apply_eq _).2 ((congrArg e₂ k₀).trans ((he₂o _).trans
      ((congrArg _ hcont).trans k₁.symm)))
  refine (congrArg ((D.transport hXC hfT).transport γ hγ rfl rfl hw₀ hw₁)
    (hpush _ hw₀ hs₀)).trans (Eq.trans ?_ (hpush _ hw₁ hs₁).symm)
  exact key'.trans (congrArg (((ivBundle B).restrictIso D.isOpen).orxVia
    (D.isFredholm hfT).toIsScFredholmSection hfc hfL D.hasSections hsecc (mem_univ _) hw₁) hfin)

/-- **`(t, x) ↦ e ∧ o_x` is an orientation of `f̃` over `[0, 1] × X` made with local
sc⁺-sections** (2021 Remark 6.6.19 and Definition 6.6.16; p. 703), when `o` is an orientation of
`f` made with local sc⁺-sections, `X` is tame and `P` and its pull-back have sc⁺-sections
through the smooth fibre points.  Near `(t, x)` one works over `[0, 1] × W` for a domain
`W ∋ x`: the pull-back of `P|W` is the part over `[0, 1] × W` of the pull-back of `P`
(`StrongBundle.ivRestrictIso`), the inclusion carries `e ∧ o` to `e ∧ (o|W)`
(`LocalIso.orxViaAt_ivFirstFun`), `P|W` has a chart over its whole base
(`isSectionOrientationLoc_ivFirstFun_of_chart`), and local strong bundle isomorphisms carry
continuous families to continuous families (`LocalIso.isContOn_of_pullLoc`). -/
theorem isSectionOrientationLoc_ivFirstFun (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f)
    (hsec : B.HasScPlusSectionsThrough) (hsecc : (ivBundle B).HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy)
    (hoL : IsSectionOrientationLoc hX hf fun y hy => orxLocEquiv hf hsec y hy (o y hy)) :
    IsSectionOrientationLoc (prod_cube_isTame (n := 1) hX) (hf.paramCube (n := 1))
      fun z hz => orxLocEquiv (hf.paramCube (n := 1)) hsecc z hz
        (ivFirstFun hf.toIsScFredholmSection (hf.paramCube (n := 1)).toIsScFredholmSection hsec
          o z hz) := by
  have hXC : ((cubePolyfold 1).prod PX).IsTame := prod_cube_isTame hX
  have hfT := hf.paramCube (n := 1)
  have := paracompactSpace_rn_rn_prod PX
  have := paracompactSpace_rn_rn_pullback B
  have := paracompactSpace_rn_rn_prod ((cubePolyfold 1).prod PX)
  have := paracompactSpace_rn_rn_pullback (ivBundle B)
  intro z hz
  set D := B.domAt z.2 with hD
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) (PX.restrictOpen D.isOpen)
  have := D.bundle.paracompactSpace_pullback
    ((cubePolyfold 1).prod (PX.restrictOpen D.isOpen))
    (Prod.snd : (Fin 1 → unitInterval) × D.carrier → D.carrier)
  have := paracompactSpace_rn_prod ((cubePolyfold 1).prod (PX.restrictOpen D.isOpen))
  have := paracompactSpace_rn_pullback (ivBundle D.bundle)
  have := paracompactSpace_rn_rn_prod ((cubePolyfold 1).prod (PX.restrictOpen D.isOpen))
  have := paracompactSpace_rn_rn_pullback (ivBundle D.bundle)
  have hX₁ := D.isTame hX
  have hf₁ := D.isFredholm hf
  have hf₁T := hf₁.paramCube (n := 1)
  have hsecc₁ : (ivBundle D.bundle).HasScPlusSectionsThrough :=
    hasScPlusSectionsThrough_ivBundle D.hasSections
  have ho₁ := D.isSectionOrientation_pushGlobal hX hf hsec o hoL
  have S1 := isSectionOrientationLoc_ivFirstFun_of_chart hX₁ D.exists_chart_univ hf₁
    D.hasSections hsecc₁ ho₁
  have hcont₁ := (isSectionOrientationLoc_iff_isContOn_univ _ _ _).1 S1
  have hfL := B.cubeLift_eqOn_ivRestrictIso D.isOpen hf.isScSmooth.1
  have hfL₀ := B.restrictSection_eqOn_restrictIso D.isOpen hf.isScSmooth.1
  have heq : (B.ivRestrictIso D.isOpen).pullLoc hf₁T hfT hfL (fun z hz =>
      orxLocEquiv hfT hsecc z hz (ivFirstFun hf.toIsScFredholmSection
        hfT.toIsScFredholmSection hsec o z hz)) =
      fun w hw => orxLocEquiv hf₁T hsecc₁ w hw (ivFirstFun hf₁.toIsScFredholmSection
        hf₁T.toIsScFredholmSection D.hasSections (D.pushGlobal hf hsec o) w hw) := by
    funext w hw
    obtain ⟨t, a⟩ := w
    have has : a ∈ (PX.restrictOpen D.isOpen).smoothSet := prod_cube_mem_smoothSet_iff.1 hw
    have hxs : a.1 ∈ PX.smoothSet := (MPolyfold.mem_smoothSet_restrictOpen_iff D.isOpen a).1 has
    have hw' : ((t, a.1) : (Fin 1 → unitInterval) × X) ∈ ((cubePolyfold 1).prod PX).smoothSet :=
      prod_cube_mem_smoothSet_iff.2 hxs
    rw [(B.ivRestrictIso D.isOpen).pullLoc_of_mem hf₁T hfT hfL _ (mem_univ _) hw hw']
    have h1 := DFunLike.congr_fun ((B.ivRestrictIso D.isOpen).orxLocEquiv_orxViaAt hf₁T hfT hfL
      hsecc₁ hsecc (a := (t, a)) (mem_univ _) rfl hw hw')
      (ivFirstFun hf.toIsScFredholmSection hfT.toIsScFredholmSection hsec o (t, a.1) hw')
    have h2 := StrongBundle.LocalIso.orxViaAt_ivFirstFun
      (B.isIntervalProductAt₂_ivRestrictIso D.isOpen (t, a)) hf₁.toIsScFredholmSection
      hf.toIsScFredholmSection hf₁T.toIsScFredholmSection hfT.toIsScFredholmSection hfL hfL₀
      D.hasSections hsec hsecc₁ hsecc (D.pushGlobal hf hsec o) o (mem_univ _) rfl (mem_univ _)
      rfl has hxs rfl
    exact h1.symm.trans (congrArg (orxLocEquiv hf₁T hsecc₁ (t, a) hw) h2)
  have h := (B.ivRestrictIso D.isOpen).isContOn_of_pullLoc (prod_cube_isTame (n := 1) hX₁) hXC
    hf₁T hfT hfL (V' := univ) isOpen_univ (by
      rw [heq, preimage_univ, inter_univ]; exact hcont₁)
  exact ⟨Prod.snd ⁻¹' D.carrier ∩ univ, ⟨B.mem_domAt z.2, mem_univ _⟩, h⟩

end Iv

/-! ### The cylinder of a strong bundle over an ep-groupoid -/

namespace SBLocalization

open StrongBundle MPolyfold Linearization15 EpGroupoid SEP

variable {A : SEP.{u}} {f : A.Obj → A.W}

/-- The cylinder `[0, 1] × X` over a tame `X` is tame. -/
theorem isTame_cubeSEP (hX : A.X.PObj.IsTame) : (A.cubeSEP 1).X.PObj.IsTame :=
  A.X.isTame_cubeProd 1 hX

/-- **`õ = e ∧ o` is an orientation of `f̃` over `[0, 1] × X` made with local sc⁺-sections**
(Definition 6.6.16; 2021 Remark 6.6.19 and p. 703), for `X` tame and `o` an orientation of `f`
made with local sc⁺-sections. -/
theorem isSectionOrientationLoc_cubeOrientation (hX : A.X.PObj.IsTame)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (hoL : IsSectionOrientationLoc hX hft fun y hy => orxLocEquiv hft hsec y hy (o y hy)) :
    IsSectionOrientationLoc (isTame_cubeSEP hX)
      (isScFredholmSectionTame_cubeLiftEp (n := 1) hft)
      fun z hz => orxLocEquiv (isScFredholmSectionTame_cubeLiftEp (n := 1) hft) hsec' z hz
        (cubeOrientation hf hft hsec o z hz) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
    (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)
  have := paracompactSpace_rn_prod A.X.PObj
  have := paracompactSpace_rn_pullback A.B
  have := paracompactSpace_rn_prod ((cubePolyfold 1).prod A.X.PObj)
  have := paracompactSpace_rn_pullback (ivBundle A.B)
  exact isSectionOrientationLoc_ivFirstFun hX hft hsec hsec' o hoL

/-- **The orientations of the kernels induced by `õ = e ∧ o` are continuous along the sheets**
(Theorem 15.4.1 on the cylinder; Definition 9.3.2), for `X` tame and `o` an orientation of `f`
made with local sc⁺-sections. -/
theorem canonContinuous_cubeOrientation_loc (Λ' : (A.cubeSEP 1).W → ℚ≥0)
    (hX : A.X.PObj.IsTame) (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) (hsec : A.B.HasScPlusSectionsThrough)
    (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (hoL : IsSectionOrientationLoc hX hft fun y hy => orxLocEquiv hft hsec y hy (o y hy)) :
    CanonContinuous Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
      (cubeOrientation hf hft hsec o) :=
  canonContinuous_loc Λ' (isTame_cubeSEP hX)
    (isScFredholmSectionTame_cubeLiftEp (n := 1) hft) hsec' (cubeOrientation hf hft hsec o)
    (isSectionOrientationLoc_cubeOrientation hX hf hft hsec hsec' o hoL)

/-- **Theorem 15.4.1 (2021 p. 702; 2017: Theorem 15.6) for the cobordism** (2021 p. 703), for
an orientation made with local sc⁺-sections: let `d_X ≡ 0`, `(f, o)` an sc-Fredholm section
functor with tame germ data of index `m + 1`, `o` an orientation of `f` in the sense of
Definition 6.6.16 for the local orientation sets, and `õ = e ∧ o` invariant under the morphisms
of the cylinder.  For a transversal sc⁺-multisection `Λ̃` on `[0, 1] × X` with `Λ̃ = Λᵢ` over
`t = i` and the face condition of Theorem 15.3.9 for the glued data, the formula of Theorem
15.4.1 for `(f̃, õ)` defines the canonical orientation of `Θ̃ = Λ̃ ∘ f̃`, of dimension `m + 2`. -/
theorem theorem_15_4_1_cylinder_loc (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough) (hsec' : (A.cubeSEP 1).B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hf.2 y hy)
    (hoL : IsSectionOrientationLoc (A.X.isTame_of_degIndex_eq_zero hd) hft
      fun y hy => orxLocEquiv hft hsec y hy (o y hy))
    (hinvC : (A.cubeSEP 1).E.IsOrInvariant
      (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft) hsec'
      (cubeOrientation hf hft hsec o))
    {m : ℕ} (hidx : ∀ x ∈ A.X.PObj.smoothSet, A.B.IsIndexAt f x ((m + 1 : ℕ) : ℤ))
    {Λ' : (A.cubeSEP 1).W → ℚ≥0} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hΛ' : IsScPlusMultisection (A.cubeSEP 1) Λ')
    (htr : IsTransversal (cubeLiftEp (n := 1) f hf.1.1.1) Λ')
    (h0 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 0 → Λ' w = Λ₀ (cubeVal w).2)
    (h1 : ∀ w, ((cubeVal w).1.1 0 : ℝ) = 1 → Λ' w = Λ₁ (cubeVal w).2)
    (honto : IsBoundaryFaceOnto (cubeLiftEp (n := 1) f hf.1.1.1) (cubeGlue Λ₀ Λ₁)) :
    IsCanonicalFor Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
      (cubeOrientation hf hft hsec o) (m + 1 + 1)
      (canonicalOrientation Λ' (isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft).2 hsec'
        (cubeOrientation hf hft hsec o)) := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hfC := isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft
  have hftC := isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  have hbd : ∀ w : (A.cubeSEP 1).W, (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary →
      Λ' w = cubeGlue Λ₀ Λ₁ w := fun w hw => by
    rcases (mem_boundary_cubeSEP_iff hX hd _).1 hw with h | h
    · exact (h0 w h).trans (cubeGlue_of_zero h).symm
    · exact (h1 w h).trans (cubeGlue_of_one h).symm
  have hgood : ∀ z ∈ (A.cubeSEP 1).X.PObj.boundary,
      0 < Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) →
        IsGoodPositionAt (cubeLiftEp (n := 1) f hf.1.1.1) Λ' z := fun z hz hpos =>
    isGoodPositionAt_of_isInGeneralPositionAt hfC hftC hΛ' hpos
      (isInGeneralPositionAt_of_isBoundaryFaceOnto hfC hftC hΛ' hbd honto hz hpos)
  have hidxC : ∀ z ∈ EpGroupoid.supp
      (fun z => (Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) : ℚ)),
      (A.cubeSEP 1).B.IsIndexAt (cubeLiftEp (n := 1) f hf.1.1.1) z ((m + 1 + 1 : ℕ) : ℤ) :=
    fun z hz => by
    have hpos : 0 < Λ' (cubeLiftEp (n := 1) f hf.1.1.1 z) := by exact_mod_cast hz
    have hzs : z ∈ (A.cubeSEP 1).X.PObj.smoothSet := mem_smoothSet_of_pos hftC hΛ' hpos
    have hxs : z.2 ∈ A.X.PObj.smoothSet := prod_cube_mem_smoothSet_iff.1 hzs
    exact isIndexAt_cubeLiftEp hf hft hsec hxs (hidx z.2 hxs) z.1
  exact theorem_15_4_1_of_isSectionOrientationLoc (isTame_cubeSEP hX) hfC hftC hΛ' hsec'
    (cubeOrientation hf hft hsec o) hinvC
    (isSectionOrientationLoc_cubeOrientation hX hf hft hsec hsec' o hoL)
    (isGoodPositionAt_of_transversal hfC hftC hΛ' htr hgood) hidxC
    ((A.cubeSEP 1).X.hasIndependentTangentSums _)

end SBLocalization

end Polyfold
