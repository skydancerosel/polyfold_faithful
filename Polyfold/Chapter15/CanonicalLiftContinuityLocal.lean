import Polyfold.Chapter15.CanonicalLiftContinuityLocalFrames
import Polyfold.Chapter12.LocalOrientationFunctor

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part III, §15.4,
pp. 701–702: **Theorem 15.4.1** and **Definition 15.4.2** (2017: Theorem 15.6, Definition 15.7),
the continuity of the canonical lift `T̂_((f, o), Λ)` along the sheets, for an orientation of `f`
made with local sc⁺-sections.

# The canonical lift is continuous along the sheets: local sc⁺-sections

## The text, paraphrased

(Theorem 15.4.1) For an oriented sc-Fredholm section functor `(f, o)` and an sc⁺-multisection
`Λ` in good position, `T_Θ`, `Θ = Λ ∘ f`, has a canonical lift
`T̂(y) = ∑_{i : f(y) = sᵢ(y)} σᵢ · (ker (f − sᵢ)'(y), o_{i,y})` to `Ĝr(X)`, with `o_{i,y}` the
orientation of `ker (f − sᵢ)'(y) = T_yMᵢ` induced by `o_y`.  The sections `sᵢ` are local
sc⁺-sections, and the linearizations of §6.2 are made with locally defined sc⁺-sections.

## What is formalized

The statements of `CanonicalLiftContinuity` for an orientation of `f` in the sense of
Definition 6.6.16 made with local sc⁺-sections (`IsSectionOrientationLoc`), on a tame `X`.  No
sc-smooth bump functions are assumed.

* `StrongBundle.Dom.pushGlobal`, `StrongBundle.Dom.isSectionOrientation_pushGlobal`: an
  orientation of `f` made with local sc⁺-sections, read in a domain `W`, is an orientation of
  `f|W` in the sense of Definition 6.6.16.
* **`KernelBranching.eventually_incFrame_mem_frames_loc`**: the sign of a frame field of a
  sheet `Mᵢ` in corner coordinates, for `o_{i,y}`, is locally constant.  Near `x₀ ∈ Mᵢ` one works
  in a domain `W ∋ x₀` inside the domain of the local sections (`StrongBundle.Dom`): over `W`
  the local section `sᵢ` is an sc⁺-section of `P|W`, `P|W` has a chart over its whole base
  (orientable neighbourhoods: `exists_isOrientableNbhd_of_chart`), the family `o` read in `W`
  is an orientation of `f|W` (`isSectionOrientationLoc_iff_forall_dom_isSectionOrientation`),
  and `o_{i,y}` is Part I's tangent orientation of `f|W − sᵢ|W`
  (`KernelBranching.mem_frames_iff_tangentOr_dom`).
* **`KernelBranching.framesContinuous_loc`**, **`canonContinuous_loc`**: `CanonContinuous`.
* **`theorem_15_4_1_of_isSectionOrientationLoc`**: Theorem 15.4.1 in `Ĝr(X)` for such an
  orientation invariant under the morphisms, with the independence of Theorem 9.2.1 as a
  hypothesis.

## Reading

The orientation `o` is a family `o_y ∈ Or_y^f` in the sets of `SectionOrientation` (the standing
hypothesis of §12.5, sc⁺-sections through all smooth fibre points, identifies them with the
local orientation sets, `orxLocEquiv`); the continuity hypothesis is the one for the local
orientation sets.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module Manifold

noncomputable section

namespace Polyfold

universe u

/-! ### An orientation read in a domain -/

section Dom

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **A family `o_y ∈ Or_y^f` read in a domain `W`**: the image of `o_w` under the orientation
map of the inclusion `P|W → P`, for the smooth points `w` of `W`. -/
def StrongBundle.Dom.pushGlobal (D : B.Dom) (hf : B.IsScFredholmSectionTame f)
    (hsec : B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy) (w : D.carrier)
    (hw : w ∈ (PX.restrictOpen D.isOpen).smoothSet) :
    Orx (D.sec f hf.isScSmooth.1) (D.isFredholm hf).toIsScFredholmSection w hw :=
  D.toGlobal hf hsec w.1 w.2 ((MPolyfold.mem_smoothSet_restrictOpen_iff D.isOpen w).1 hw)
    (o w.1 ((MPolyfold.mem_smoothSet_restrictOpen_iff D.isOpen w).1 hw))

/-- The family read in a domain through the local orientation sets is the family read through
the inclusion of the domain. -/
theorem StrongBundle.Dom.pushLoc_orxLocEquiv (D : B.Dom) (hf : B.IsScFredholmSectionTame f)
    (hsec : B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy) :
    D.pushLoc hf (fun y hy => orxLocEquiv hf hsec y hy (o y hy)) = D.pushGlobal hf hsec o := by
  funext w hw
  obtain ⟨w, hwD⟩ := w
  exact DFunLike.congr_fun (orxLocEquiv_toLoc hf hsec D w hwD
    ((MPolyfold.mem_smoothSet_restrictOpen_iff D.isOpen ⟨w, hwD⟩).1 hw))
    (o w ((MPolyfold.mem_smoothSet_restrictOpen_iff D.isOpen ⟨w, hwD⟩).1 hw))

/-- **An orientation of `f` made with local sc⁺-sections, read in a domain `W`, is an
orientation of `f|W`** in the sense of Definition 6.6.16. -/
theorem StrongBundle.Dom.isSectionOrientation_pushGlobal (D : B.Dom) (hX : PX.IsTame)
    (hf : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf.toIsScFredholmSection y hy)
    (hoL : IsSectionOrientationLoc hX hf fun y hy => orxLocEquiv hf hsec y hy (o y hy)) :
    IsSectionOrientation (D.sec f hf.isScSmooth.1) (D.isFredholm hf).toIsScFredholmSection
      (D.pushGlobal hf hsec o) :=
  D.pushLoc_orxLocEquiv hf hsec o ▸
    (isSectionOrientationLoc_iff_forall_dom_isSectionOrientation hX hf _).1 hoL D

end Dom

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid

variable {A : SEP.{u}} {f : A.Obj → A.W} {Λ : A.W → ℚ≥0} {x : A.Obj}

namespace KernelBranching

/-- **The sign of a frame field in corner coordinates is locally constant along a sheet**, for
an orientation `o` of `f` made with local sc⁺-sections (Definition 6.6.16,
`IsSectionOrientationLoc`) on a tame `X`: for a sheet `Mᵢ` of positive dimension, corner
coordinates `κ` of `Mᵢ` and a basis `b` of `ℝⁿ`, if the frame `(Tι(b₁), …, Tι(bₙ))` of
`T_{x₀}Mᵢ` is positive for `o_{i,x₀}`, the frames `(Tι(b₁), …, Tι(bₙ))` of `T_yMᵢ` are positive
for `o_{i,y}` at all `y ∈ Mᵢ` near `x₀`. -/
theorem eventually_incFrame_mem_frames_loc (hX : A.X.PObj.IsTame)
    (hft : A.B.IsScFredholmSectionTame f) (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hft.toIsScFredholmSection y hy)
    (hoL : IsSectionOrientationLoc hX hft fun y hy => orxLocEquiv hft hsec y hy (o y hy))
    (K : KernelBranching A f Λ x) (i : K.ι) (hn : 0 < K.dim i) [ParacompactSpace (K.M i)]
    {hY : A.X.PObj.IsSubMPolyfold (K.M i)}
    {hcs : (subPolyfold hY).HasCornerStructureOfDim (K.dim i)}
    (κ : CornerCoords (subPolyfold hY) (K.dim i)) {x₀ : K.M i} (hx₀ : x₀ ∈ κ.s)
    (b : Basis (Fin (K.dim i)) ℝ (EuclideanSpace ℝ (Fin (K.dim i))))
    (hb : (fun j => incFrame hcs κ hx₀ (b j)) ∈
      K.frames hft.toIsScFredholmSection hsec o i x₀.1) :
    ∀ᶠ y in 𝓝 x₀, ∃ hy : y ∈ κ.s,
      (fun j => incFrame hcs κ hy (b j)) ∈ K.frames hft.toIsScFredholmSection hsec o i y.1 := by
  have hf : A.B.IsScFredholmSection f := hft.toIsScFredholmSection
  have hfsec : IsSection A.P f := hft.isScSmooth.1
  have hs₀ := K.smooth i x₀.1 x₀.2
  have hNd := K.isSubmanifoldOfDim i
  -- a domain at `x₀` inside the domain of the local sections
  obtain ⟨D, hDO, hx₀D⟩ : ∃ D : A.B.Dom, D.carrier ⊆ K.O ∧ x₀.1 ∈ D.carrier :=
    ⟨(A.B.domAt x₀.1).restrict K.isOpen_O ⟨x₀.1, A.B.mem_domAt x₀.1, K.mem_O x₀.2⟩,
      fun _ hy => hy.2, A.B.mem_domAt x₀.1, K.mem_O x₀.2⟩
  have hfD := D.isFredholm hft
  have htD := K.isScPlusSection_negSecD i hDO
  have hgt := theorem_3_1_18_tame hfD htD
  have hg := theorem_3_1_18_preprint hfD.toIsScFredholmSection htD
  -- the orientation read in the domain
  have hoD := D.isSectionOrientation_pushGlobal hX hft hsec o hoL
  have ho' := isSectionOrientation_sectionAdd hfD.toIsScFredholmSection htD hoD
  have hs₀D : (⟨x₀.1, hx₀D⟩ : D.carrier) ∈ (A.X.PObj.restrictOpen D.isOpen).smoothSet :=
    StrongBundle.Dom.mem_smoothSet hx₀D hs₀
  obtain ⟨c, hc, U, V, hN⟩ := exists_isOrientableNbhd_of_chart (D.isTame hX) D.exists_chart_univ
    hgt hs₀D
  have hVc : ∀ {w : D.carrier}, w ∈ V → w ∈ c.φ.source := fun hw =>
    hN.hasLocalPropagation.subset (hN.subset hw)
  have hx₀c : x₀.1 ∈ (D.chart c).φ.source := D.mem_chart_source hx₀D (hVc hN.mem)
  set d := hY.data x₀.2 with hd
  have hxσ₀ : x₀ ∈ (subChart d (D.chart c).isChart x₀).source :=
    d.mem_shrink (D.chart c).φ x₀.2 (hY.mem_data_V x₀.2) hx₀c
  have hW : IsOpen (Subtype.val '' V : Set A.Obj) :=
    D.isOpen.isOpenMap_subtype_val V hN.isOpen_V
  have hWD : ∀ {y : A.Obj}, y ∈ (Subtype.val '' V : Set A.Obj) →
      ∃ hy : y ∈ D.carrier, (⟨y, hy⟩ : D.carrier) ∈ V := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨w.2, hw⟩
  have hG : IsOpen ((subChart d (D.chart c).isChart x₀).source ∩
      Subtype.val ⁻¹' (Subtype.val '' V : Set A.Obj)) :=
    (subChart _ (D.chart c).isChart x₀).isOpen_source.inter (hW.preimage continuous_subtype_val)
  -- the pointwise description of the frames
  have hpt := fun (w : K.M i) (hwD : w.1 ∈ D.carrier) (hwV : (⟨w.1, hwD⟩ : D.carrier) ∈ V) =>
    K.mem_frames_iff_tangentOr_dom D hft hsec o hDO w.2 hwD hc (hVc hwV)
  choose hZ hLs hnk hA hiff using hpt
  filter_upwards [eventually_exists_segPath κ hx₀ hG
    ⟨hxσ₀, ⟨x₀.1, hx₀D⟩, hN.mem, rfl⟩] with y hy
  obtain ⟨hyκ, γ, hγs, hγ0', hγ1', hγG, hγχ⟩ := hy
  refine ⟨hyκ, ?_⟩
  have hγsX : (rnPolyfold 1).IsScSmoothMap A.X.PObj (Subtype.val ∘ γ) :=
    (subPolyfold_inclusion_isScSmooth hY).comp hγs
  have hγD : ∀ q, (Subtype.val ∘ γ) q ∈ D.carrier := fun q => (hWD (hγG q).2.2).1
  have hγDs := D.isScSmoothMap_liftPath hγsX hγD
  have hγV : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, D.liftPath (Subtype.val ∘ γ) hγD q ∈ V := fun q _ =>
    (hWD (hγG q).2.2).2
  have hγZ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1,
      IsZeroAt (pullbackProj A.P (Subtype.val : D.carrier → A.Obj)) (K.subD D i hfsec)
        (D.liftPath (Subtype.val ∘ γ) hγD q) := fun q hq => hZ (γ q) (hγD q) (hγV q hq)
  have hγL : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, D.bundle.IsLinSurjAt (K.subD D i hfsec)
      (D.liftPath (Subtype.val ∘ γ) hγD q) := fun q hq => hLs (γ q) (hγD q) (hγV q hq)
  -- the frame of the kernels along the path
  let m : K.M i → EuclideanSpace ℝ (Fin (K.dim i)) →L[ℝ] c.φ.model.E 0 := fun w =>
    ((D.model c).symm : (D.chart c).φ.model.E 0 →L[ℝ] c.φ.model.E 0).comp
      (modelDeriv κ (D.chart c).isChart d x₀ (levelLift κ.χ 1 w))
  have hcv : ∀ (w : K.M i) (hw : w ∈ κ.s), w ∈ (subChart d (D.chart c).isChart x₀).source →
      ∀ v, (D.model c).symm (chartVec (D.chart c).isChart (incFrame hcs κ hw v)) = m w v :=
    fun w hw hwσ v => congrArg (D.model c).symm
      (chartVec_incFrame κ hw v (D.chart c).isChart d x₀ hwσ)
  have hmem : ∀ (q : (Fin 1 → ℝ)) (hq : q ∈ Icc (0 : Fin 1 → ℝ) 1) v, m (γ q) v ∈ c.linKer
      (K.subD D i hfsec) (chartPtOf c hc (hVc (hγV q hq))
        (hg.mem_smoothSet_of_isZeroAt (hγZ q hq))).z := fun q hq v => by
    rw [← hcv (γ q) (hγG q).1 (hγG q).2.1 v]
    exact hA (γ q) (hγD q) (hγV q hq) _ (incFrame_mem hNd.1 κ (hγG q).1 v)
  have hli : ∀ q : (Fin 1 → ℝ), LinearIndependent ℝ fun j => m (γ q) (b j) := fun q =>
    (b.linearIndependent.map' (modelDeriv κ (D.chart c).isChart d x₀
      (levelLift κ.χ 1 (γ q))).toLinearMap (LinearMap.ker_eq_bot.2
      (modelDeriv_injective κ (D.chart c).isChart d x₀ (hγG q).1 (hγG q).2.1
        ((subPolyfold hY).toBase_levelLift κ.isChart (κ.s_subset (hγG q).1)
          (levelVal_mem (hcs.levelOne (γ q))))))).map'
      ((D.model c).symm : (D.chart c).φ.model.E 0 →L[ℝ] c.φ.model.E 0).toLinearMap
      (LinearMap.ker_eq_bot.2 (D.model c).symm.injective)
  have hγc : Continuous γ := continuousOn_univ.1 hγs.continuousOn
  have hcont : ∀ v, Continuous fun q : Icc (0 : Fin 1 → ℝ) 1 => m (γ q) v := fun v =>
    (D.model c).symm.continuous.comp
      ((continuousOn_modelDeriv_levelLift hcs κ (D.chart c).isChart d x₀ v).comp_continuous
        (hγc.comp continuous_subtype_val) fun q => ⟨(hγG q).1, (hγG q).2.1⟩)
  let Λ₁ : SubspaceFamily (Icc (0 : Fin 1 → ℝ) 1) (c.φ.model.E 0) :=
    { L := fun q => c.linKer (K.subD D i hfsec)
        (chartPtOf c hc (hVc (hγV q q.2)) (hg.mem_smoothSet_of_isZeroAt (hγZ q q.2))).z
      n := K.dim i
      finiteDimensional := fun q => Module.finite_of_finrank_pos
        (lt_of_lt_of_eq hn (hnk (γ q) (hγD q) (hγV q q.2)).symm)
      finrank_eq := fun q => hnk (γ q) (hγD q) (hγV q q.2)
      exists_frame := fun _ => ⟨univ, isOpen_univ, mem_univ _, fun j q => m (γ q) (b j),
        fun j => (hcont (b j)).continuousOn, fun q _ => ⟨fun j => hmem q q.2 (b j), hli q⟩⟩ }
  have hT := isLineOrientation_tangentOr_of_family_of_isSectionOrientation hg ho' hs₀D hN hγDs
    hγV hγZ hγL Λ₁ (fun q => rfl)
  let ε : (Λ₁.congrL _ (fun q => rfl)).Frame :=
    { U := univ
      isOpen := isOpen_univ
      e := fun j q => m (γ q) (b j)
      continuousOn := fun j => (hcont (b j)).continuousOn
      mem := fun q _ j => hmem q q.2 (b j)
      linearIndependent := fun q _ => hli q }
  have hL := ε.isLineOrientation rfl
  have : PreconnectedSpace (Icc (0 : Fin 1 → ℝ) 1) :=
    isPreconnected_iff_preconnectedSpace.1 (convex_Icc 0 1).isPreconnected
  have hiff01 := IsLineOrientation.eq_iff_eq hT hL ⟨1, right_mem_Icc.2 fun _ => zero_le_one⟩
    ⟨0, left_mem_Icc.2 fun _ => zero_le_one⟩
  -- the frames of `o_{i,γ(q)}` and the two orientations of the line bundle
  have hkey : ∀ q : Icc (0 : Fin 1 → ℝ) 1,
      (fun j => incFrame hcs κ (hγG q).1 (b j)) ∈ K.frames hf hsec o i (γ q).1 ↔
        tangentOrAt (K.subD D i hfsec) hg c hc
            (hN.hasLocalPropagation.subset (hN.subset (hγV q q.2)))
            (hg.mem_smoothSet_of_isZeroAt (hγZ q q.2)) (hγZ q q.2) (hγL q q.2)
            (restrictOr (fun y hy => (chartPtOf (orChart D.bundle y) (isChart_orChart y)
              (mem_orChart y) hy).orSectionAdd hfD.toIsScFredholmSection htD
                (D.pushGlobal hft hsec o y hy)) hN (D.liftPath (Subtype.val ∘ γ) hγD q)
              (hγV q q.2) (hg.mem_smoothSet_of_isZeroAt (hγZ q q.2))) =
          rayOfNeZero ℝ (ε.wedgeAt q) (ε.wedgeAt_ne_zero (mem_univ q)) := fun q => by
    have hw : (fun j => (D.model c).symm (chartVec (D.chart c).isChart
        (incFrame hcs κ (hγG q).1 (b j)))) = fun j => m (γ q) (b j) :=
      funext fun j => hcv (γ q) (hγG q).1 (hγG q).2.1 (b j)
    have hwe := ε.wedgeAt_of_mem (mem_univ q)
    have hstep := congrArg (tangentOrAt (K.subD D i hfsec) hg c hc
      (hN.hasLocalPropagation.subset (hN.subset (hγV q q.2)))
      (hg.mem_smoothSet_of_isZeroAt (hγZ q q.2)) (hγZ q q.2) (hγL q q.2))
      (toChartOr_orSectionAdd hfD.toIsScFredholmSection htD
        (hg.mem_smoothSet_of_isZeroAt (hγZ q q.2))
        (D.pushGlobal hft hsec o (D.liftPath (Subtype.val ∘ γ) hγD q)
          (hg.mem_smoothSet_of_isZeroAt (hγZ q q.2)))
        c hc (hN.hasLocalPropagation.subset (hN.subset (hγV q q.2))))
    refine (hiff (γ q) (hγD q) (hγV q q.2) _).trans ?_
    refine (and_iff_right fun j => incFrame_mem hNd.1 κ (hγG q).1 (b j)).trans ?_
    refine (exists_ray_wedge_congr _ hw _).trans ?_
    constructor
    · rintro ⟨_, hne, he⟩
      exact hstep.trans (he.trans (rayOfNeZero_congr hwe.symm _ _))
    · intro he
      exact ⟨fun j => hmem q q.2 (b j), hwe ▸ ε.wedgeAt_ne_zero (mem_univ q),
        hstep.symm.trans (he.trans (rayOfNeZero_congr hwe _ _))⟩
  have htr : ∀ (w w' : K.M i) (_ : w = w') (hw : w ∈ κ.s) (hw' : w' ∈ κ.s),
      ((fun j => incFrame hcs κ hw (b j)) ∈ K.frames hf hsec o i w.1 ↔
        (fun j => incFrame hcs κ hw' (b j)) ∈ K.frames hf hsec o i w'.1) := by
    intro w w' h hw hw'
    subst h
    rfl
  exact (htr _ _ hγ1' (hγG 1).1 hyκ).1 ((hkey ⟨1, right_mem_Icc.2 fun _ => zero_le_one⟩).2
    (hiff01.2 ((hkey ⟨0, left_mem_Icc.2 fun _ => zero_le_one⟩).1
      ((htr _ _ hγ0'.symm hx₀ (hγG 0).1).1 hb))))

/-- **Continuity of `y ↦ o_{i,y}` along the sheets** (Theorem 15.4.1; Definition 9.3.2), for an
orientation `o` of `f` made with local sc⁺-sections (`IsSectionOrientationLoc`) on a tame `X`:
every local branching structure described by kernels has continuous frames. -/
theorem framesContinuous_loc (hX : A.X.PObj.IsTame) (hft : A.B.IsScFredholmSectionTame f)
    (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hft.toIsScFredholmSection y hy)
    (hoL : IsSectionOrientationLoc hX hft fun y hy => orxLocEquiv hft hsec y hy (o y hy))
    (K : KernelBranching A f Λ x) : K.FramesContinuous hft.toIsScFredholmSection hsec o := by
  intro i hn y hy
  let _ := A.X.PObj.paracompactSpace_subtype (K.M i)
  have hNd := K.isSubmanifoldOfDim i
  have hcs := hNd.hasCornerStructureOfDim_of_hasTameInducedStructure
    (K.hasTameInducedStructure i)
  obtain ⟨κ, hκ⟩ := hcs.exists_cornerCoords ⟨y, hy⟩
  obtain ⟨b, hb⟩ := exists_basis_incFrame_mem_of_isOrientedAt (hcs := hcs) hn hNd
    (K.isOrientedAt hft.toIsScFredholmSection hsec o hy) κ hκ
  exact exists_continuousOn_frame_of_eventually (hcs := hcs) hNd
    (K.frames hft.toIsScFredholmSection hsec o i) κ hκ b
    (K.eventually_incFrame_mem_frames_loc hX hft hsec o hoL i hn κ hκ b hb)

end KernelBranching

/-! ### Theorem 15.4.1 -/

/-- **Theorem 15.4.1 (2021 p. 702; 2017: Theorem 15.6), continuity of the canonical lift**, for
an orientation made with local sc⁺-sections: let `X` be tame, `f` an sc-Fredholm section with
tame germ data and `o` a family `o_y ∈ Or_y^f` which is an orientation of `f` in the sense of
Definition 6.6.16 for the local orientation sets (`IsSectionOrientationLoc`).  Then for every
local branching structure of `Θ = Λ ∘ f` described by kernels, `y ↦ o_{i,y}` is continuous along
the sheets `Mᵢ` (`CanonContinuous`).  Boundary points are included. -/
theorem canonContinuous_loc (Λ : A.W → ℚ≥0) (hX : A.X.PObj.IsTame)
    (hft : A.B.IsScFredholmSectionTame f) (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hft.toIsScFredholmSection y hy)
    (hoL : IsSectionOrientationLoc hX hft fun y hy => orxLocEquiv hft hsec y hy (o y hy)) :
    CanonContinuous Λ hft.toIsScFredholmSection hsec o :=
  fun _ K => K.framesContinuous_loc hX hft hsec o hoL

/-- **Theorem 15.4.1 (2021 p. 702; 2017: Theorem 15.6) in `Ĝr(X)`, for an sc-Fredholm section
functor oriented with local sc⁺-sections**: let `X` be tame, `f` an sc-Fredholm section functor
with tame germ data, `o` an orientation of `f` (Definition 6.6.16 for the local orientation
sets) invariant under the morphisms (Definition 12.5.4), and `Λ` an sc⁺-multisection such that
`(f, Λ)` is in good position (Definition 15.2.4) and `f` has index `n` at every point of
`supp(Λ ∘ f)`.  Then, with the independence of Theorem 9.2.1 (`hTS`), `canonicalOrientation`
is an orientation of `Θ = Λ ∘ f` (Definition 9.3.2), and it is the canonical one
(`IsCanonicalFor`). -/
theorem theorem_15_4_1_of_isSectionOrientationLoc (hX : A.X.PObj.IsTame)
    (hF : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hΛ : IsScPlusMultisection A Λ) (hsec : A.B.HasScPlusSectionsThrough)
    (o : ∀ y (hy : y ∈ A.X.PObj.smoothSet), Orx f hF.2 y hy)
    (hinv : A.E.IsOrInvariant hF hsec o)
    (hoL : IsSectionOrientationLoc hX hft fun y hy => orxLocEquiv hft hsec y hy (o y hy))
    {n : ℕ}
    (hgp : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), IsGoodPositionAt f Λ x)
    (hidx : ∀ x ∈ EpGroupoid.supp (fun z => (Λ (f z) : ℚ)), A.B.IsIndexAt f x n)
    (hTS : A.X.HasIndependentTangentSums (fun z => (Λ (f z) : ℚ))) :
    IsCanonicalFor Λ hF.2 hsec o n (canonicalOrientation Λ hF.2 hsec o) :=
  theorem_15_4_1_of_natural_continuous hF hft hΛ
    (fun x hx => exists_kernelBranching_dim hF hft hsec (hgp x hx) (hidx x hx)) hTS
    (canonNatural Λ hF hΛ hsec o hinv) (canonContinuous_loc Λ hX hft hsec o hoL)

end SBLocalization

end Polyfold
