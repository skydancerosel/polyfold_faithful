import Polyfold.Chapter15.RestrictedSeedsFinal0

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, proof of
**Theorem 15.3.9** (Transversal Extension Theorem), steps (c)–(d), pp. 698–699, and
**Corollary 15.3.10 (3)**, p. 699; used for **Corollary 15.4.4**, p. 703.

# The local families on the cylinder of a restriction

## The text, paraphrased

The proof of Theorem 15.3.9 covers the compact set `supp(Λ₀ ∘ f)` by finitely many saturated
open sets carrying local parameter families of sc⁺-multisections which fill the cokernels.  The
families are built with sc-smooth functions of small support.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `exists_finite_centres`: finitely many interior centres with their data (`CentreData`) and
  finitely many saturated open sets on which the reduced linearizations are onto, which together
  cover `supp(Λ₀ ∘ f)`.
* **`hasRestrictedCylinderFamilies`**: for two transversal perturbations of an sc-Fredholm
  section functor with tame germ data and sc⁺-sections through the smooth fibre points, on an
  ep-groupoid with `d_X ≡ 0` and paracompact orbit space, there is a saturated open `V` such that
  the cylinder of `X|V` carries the local families (`HasRestrictedCylinderFamilies`).  Bump
  functions on `X` are not assumed.

## Reading

Only finitely many functions are needed, and each of them only near a compact subset of `|X|`;
such functions exist on a saturated open neighbourhood `V` of that compact set (Remark 9.5.19,
2021 p. 451).  The centres and their data are chosen on `[0, 1] × X` first, `V` last.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP

section Cover

variable {A : SEP.{u}} {f : A.Obj → A.W} {Λ₀ : A.W → ℚ≥0} {N : A.B.One → ℝ} {U : Set A.Obj}

/-- **Finitely many centres cover `supp(Λ₀ ∘ f)`** (step (c) of the proof of Theorem 15.3.9,
2021 pp. 698–699).  Let `X` be tame, `f` sc-Fredholm with tame germ data and sc⁺-sections
through the smooth fibre points, `(N, U)` controlling compactness, `h` continuous, `Λ₀` an
sc⁺-multisection with dom-supp in `U`, `N(Λ₀) ≤ 1`, `N(Λ₀) < h` off `∂X`, and `(f, Λ₀)` in
general position at the points of `supp(Λ₀ ∘ f) ∩ ∂X`.  Then there are finitely many interior
centres with data, and finitely many saturated open sets on which the reduced linearizations
are onto, such that every point of `supp(Λ₀ ∘ f)` lies over the cover set `|N'|` of a centre or
in one of the open sets. -/
theorem exists_finite_centres (hX : A.X.IsTame) (hsec : A.B.HasScPlusSectionsThrough)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hcc : ControlsCompactness A f N U) (hΛ₀ : IsScPlusMultisection A Λ₀)
    {h : A.Obj → ℝ} (hhc : Continuous h) (hN1 : ∀ x, pointwiseNorm N Λ₀ x ≤ 1)
    (hdom : domSupp Λ₀ ⊆ U)
    (hlt : ∀ x ∉ A.X.PObj.boundary, pointwiseNorm N Λ₀ x < h x)
    (hbd : ∀ x : A.X.PObj.Level 1, A.X.PObj.levelVal 1 x ∈ A.X.PObj.boundary →
      0 < Λ₀ (f (A.X.PObj.levelVal 1 x)) → IsReducedOntoAtPt f Λ₀ x) :
    ∃ (ι : Type u) (_ : Finite ι) (z : ι → A.Obj) (D : ∀ i, CentreData A f Λ₀ N U h (z i))
      (κ : Type u) (_ : Finite κ) (P : κ → Set A.Obj),
      (∀ k, IsOpen (P k) ∧ A.X.IsSaturated (P k) ∧ ∀ y : A.X.PObj.Level 1,
        A.X.PObj.levelVal 1 y ∈ P k → 0 < Λ₀ (f (A.X.PObj.levelVal 1 y)) →
          IsReducedOntoAtPt f Λ₀ y) ∧
      ∀ y, 0 < Λ₀ (f y) → (∃ i, A.X.π y ∈ A.X.π '' (D i).N') ∨ ∃ k, y ∈ P k := by
  classical
  have hfc : Continuous f := continuousOn_univ.1 hft.isScSmooth.2.continuousOn
  have hK := isCompact_image_supp_comp hf hfc hΛ₀ hcc hN1 hdom
  let I := {x : A.Obj // 0 < Λ₀ (f x) ∧ x ∉ A.X.PObj.boundary}
  let J := {x : A.Obj // 0 < Λ₀ (f x) ∧ x ∈ A.X.PObj.boundary}
  have hI : ∀ x : I, Nonempty (CentreData A f Λ₀ N U h x.1) := fun x =>
    nonempty_centreData hX hsec hf hft hcc hΛ₀ hhc
      (auxLe_of_pos hf.1.1.1 hΛ₀ hcc.2.2.2.1 hN1 hdom x.2.1).1 x.2.2 x.2.1 (hlt _ x.2.2)
  let D : ∀ x : I, CentreData A f Λ₀ N U h x.1 := fun x => (hI x).some
  have hJ : ∀ x : J, ∃ Q : Set A.Obj, IsOpen Q ∧ A.X.IsSaturated Q ∧ x.1 ∈ Q ∧
      ∀ y : A.X.PObj.Level 1, A.X.PObj.levelVal 1 y ∈ Q →
        0 < Λ₀ (f (A.X.PObj.levelVal 1 y)) → IsReducedOntoAtPt f Λ₀ y := fun x =>
    exists_isOpen_isReducedOntoAtPt hX hf hft hΛ₀ (mem_levelSet_one_of_pos hf hΛ₀ x.2.1)
      (hbd _ (by rw [A.X.PObj.levelVal_levelMk]; exact x.2.2)
        (by rw [A.X.PObj.levelVal_levelMk]; exact x.2.1))
  choose P hPo hPs hxP hPred using hJ
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun s : I ⊕ J => Sum.elim (fun x => A.X.π '' (D x).N') (fun x => A.X.π '' P x) s)
    (by
      rintro (x | x)
      · exact A.X.proposition_7_1_8 _ (D x).hN'
      · exact A.X.proposition_7_1_8 _ (hPo x))
    (by
      rintro _ ⟨y, hy, rfl⟩
      by_cases hb : y ∈ A.X.PObj.boundary
      · exact mem_iUnion.2 ⟨Sum.inr ⟨y, hy, hb⟩, y, hxP _, rfl⟩
      · exact mem_iUnion.2 ⟨Sum.inl ⟨y, hy, hb⟩, y, (D _).hxN', rfl⟩)
  have hfinI : Finite {x : I // Sum.inl x ∈ t} :=
    Finite.of_injective (fun x => (⟨Sum.inl x.1, x.2⟩ : {s : I ⊕ J // s ∈ t}))
      fun a b hab => Subtype.ext (Sum.inl_injective (congrArg Subtype.val hab))
  have hfinJ : Finite {x : J // Sum.inr x ∈ t} :=
    Finite.of_injective (fun x => (⟨Sum.inr x.1, x.2⟩ : {s : I ⊕ J // s ∈ t}))
      fun a b hab => Subtype.ext (Sum.inr_injective (congrArg Subtype.val hab))
  refine ⟨{x : I // Sum.inl x ∈ t}, hfinI, fun i => i.1.1, fun i => D i.1,
    {x : J // Sum.inr x ∈ t}, hfinJ, fun k => P k.1, fun k => ⟨hPo _, hPs _, hPred _⟩,
    fun y hy => ?_⟩
  have hmem := ht ⟨y, hy, rfl⟩
  simp only [mem_iUnion] at hmem
  obtain ⟨s, hs, hsm⟩ := hmem
  rcases s with x | x
  · exact Or.inl ⟨⟨x, hs⟩, hsm⟩
  · refine Or.inr ⟨⟨x, hs⟩, ?_⟩
    obtain ⟨y', hy', e⟩ := hsm
    change y ∈ P x
    rw [← hPs x]
    exact ⟨y', hy', e⟩

end Cover

section Cylinder

variable {A : SEP.{u}} {f : A.Obj → A.W}

set_option maxHeartbeats 1600000 in
-- the cylinder and the cylinder of the restriction are unfolded in several places
/-- **The local families on the cylinder of a restriction** (steps (c)–(d) of the proof of
Theorem 15.3.9, 2021 pp. 698–699, and Corollary 15.3.10 (3), p. 699).  Let `d_X ≡ 0`, `|X|` be
paracompact, `f` an sc-Fredholm section functor with tame germ data and sc⁺-sections through
the smooth fibre points, and `(Nⁱ, Uⁱ, Λⁱ)`, `i = 0, 1`, transversal perturbations.  Then there
is a saturated open `V ⊇ {x ∈ Uⁱ | Nⁱ(f(x)) ≤ 1}` (closures in the orbit space) such that on the
cylinder of `X|V` the explicit extension of the restricted end data has local families at the
interior points of its solution set.  Bump functions on `X` are not assumed. -/
theorem hasRestrictedCylinderFamilies (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hpara : A.X.HasParacompactOrbitSpace) (hsec : A.B.HasScPlusSectionsThrough)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ Λ₀) (hr₁ : IsTransversalPerturbation A f N₁ U₁ Λ₁) :
    HasRestrictedCylinderFamilies A f hf N₀ N₁ U₀ U₁ Λ₀ Λ₁ := by
  classical
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hcc := controlsCompactness_collar hf.1.1.1 hr₀.1 hr₁.1
  have hfC := isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft
  have hftC : (A.cubeSEP 1).B.IsScFredholmSectionTame (cubeLiftEp (n := 1) f hf.1.1.1) :=
    isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  have hE := isScPlusMultisection_cylExtension hr₀.2.1 hr₁.2.1
  have hEdom := domSupp_cylExtension_subset hr₀.2.2.1 hr₁.2.2.1
  have hEN := pointwiseNorm_cylExtension_le hr₀.1.1 hr₁.1.1 hr₀.2.1 hr₁.2.1 hr₀.2.2.2.1
    hr₁.2.2.2.1
  have hbonto := isBoundaryFaceOnto_cubeGlue hd hf hft hr₀.2.2.2.2 hr₁.2.2.2.2
  have hglue : ∀ w : (A.cubeSEP 1).W, (A.cubeSEP 1).P w ∈ (A.cubeSEP 1).X.PObj.boundary →
      cylExtension Λ₀ Λ₁ w = cubeGlue Λ₀ Λ₁ w := by
    intro w hw
    rcases (mem_boundary_cubeSEP_iff hX hd _).1 hw with h | h
    · rw [cylExtension_of_zero' hr₀.2.1 h, cubeGlue_of_zero h]
    · rw [cylExtension_of_one' hr₁.2.1 h, cubeGlue_of_one h]
  have hsecC : IsSection (A.cubeSEP 1).P (cubeLiftEp (n := 1) f hf.1.1.1) := hfC.1.1.1
  have hbd : ∀ x : (A.cubeSEP 1).X.PObj.Level 1,
      (A.cubeSEP 1).X.PObj.levelVal 1 x ∈ (A.cubeSEP 1).X.PObj.boundary →
      0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1
        ((A.cubeSEP 1).X.PObj.levelVal 1 x)) →
      IsReducedOntoAtPt (cubeLiftEp (n := 1) f hf.1.1.1) (cylExtension Λ₀ Λ₁) x := by
    intro x hx hpos
    have hPx : (A.cubeSEP 1).P (cubeLiftEp (n := 1) f hf.1.1.1
        ((A.cubeSEP 1).X.PObj.levelVal 1 x)) ∈ (A.cubeSEP 1).X.PObj.boundary := by
      rw [hsecC]; exact hx
    exact hbonto _ hE hglue x hx (mem_smoothSet_of_pos hftC hE hpos)
      (by rw [← hglue _ hPx]; exact hpos)
  have hhc : Continuous (fun z : (A.cubeSEP 1).Obj =>
      (1 + (collarCut₀ (cubeT z) + collarCut₁ (cubeT z))) / 2) :=
    (continuous_const.add ((contDiff_collarCut₀.continuous.comp continuous_cubeT).add
      (contDiff_collarCut₁.continuous.comp continuous_cubeT))).div_const 2
  have hNlt : ∀ z ∉ (A.cubeSEP 1).X.PObj.boundary,
      pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension Λ₀ Λ₁) z <
        (1 + (collarCut₀ (cubeT z) + collarCut₁ (cubeT z))) / 2 := fun z hz => by
    have hz' := (not_congr (mem_boundary_cubeSEP_iff hX hd z)).1 hz
    rw [not_or] at hz'
    have t0 : (0 : ℝ) ≤ cubeT z := (z.1 0).2.1
    have t1 : cubeT z ≤ 1 := (z.1 0).2.2
    have t0' : (0 : ℝ) < cubeT z := lt_of_le_of_ne t0 (Ne.symm hz'.1)
    have t1' : cubeT z < 1 := lt_of_le_of_ne t1 hz'.2
    have := collarCut_add_lt_one t0' t1'
    have := hEN z
    linarith
  have hN1 : ∀ z, pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension Λ₀ Λ₁) z ≤ 1 :=
    fun z => (hEN z).trans (collarCut_add_le_one (cubeT z))
  have hfc : Continuous (cubeLiftEp (n := 1) f hf.1.1.1) :=
    continuousOn_univ.1 hftC.isScSmooth.2.continuousOn
  have hK := isCompact_image_supp_comp hfC hfc hE hcc hN1 hEdom
  -- the centres on the cylinder
  obtain ⟨ι, _, z, D, κ, _, P, hP, hcov⟩ := exists_finite_centres hXC
    (hasScPlusSectionsThrough_cubeSEP hsec) hfC hftC hcc hE hhc hN1 hEdom hNlt hbd
  have hZ := fun i => (D i).exists_connected hK
  choose Z hZcpt hZc hKZ hzZ hZU using hZ
  -- the compact subset of `|X|`
  have hT₀ := hr₀.1.2.2.2.2
  have hT₁ := hr₁.1.2.2.2.2
  have hT' : IsCompact ((A.X.cubeProj 1).orbitMap ''
      ((A.cubeSEP 1).X.π '' {z | 0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1 z)})) :=
    hK.image (A.X.cubeProj 1).continuous_orbitMap
  have hTz : IsCompact (⋃ i, (fun y : (A.cubeSEP 1).Obj => A.X.π y.2) '' Z i) :=
    isCompact_iUnion fun i => (hZcpt i).image (A.X.continuous_π.comp continuous_snd)
  have hT := ((hT₀.union hT₁).union hT').union hTz
  -- the functions
  have hB : ∀ i, ∃ (β : (Fin 1 → unitInterval) × A.Obj → ℝ) (V : Set A.Obj)
      (C : Set ((Fin 1 → unitInterval) × A.Obj)), IsOpen V ∧ A.X.IsSaturated V ∧
      A.X.π ⁻¹' (closure (A.X.π '' {x ∈ U₀ | A.B.AuxLe N₀ (f x) 1}) ∪
        closure (A.X.π '' {x ∈ U₁ | A.B.AuxLe N₁ (f x) 1}) ∪
        (A.X.cubeProj 1).orbitMap '' ((A.cubeSEP 1).X.π ''
          {z | 0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1 z)}) ∪
        ⋃ i, (fun y : (A.cubeSEP 1).Obj => A.X.π y.2) '' Z i) ⊆ V ∧
      (A.X.cubeProd 1).PObj.IsScSmoothOn realPolyfold β (univ ×ˢ V) ∧ (∀ y, 0 ≤ β y) ∧
      (∀ y ∈ closure (D i).N' ∩ (A.cubeSEP 1).X.π ⁻¹' ((A.cubeSEP 1).X.π ''
        {z | 0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1 z)}), 0 < β y) ∧
      IsClosed C ∧ support β ⊆ C ∧
      C ⊆ (D i).Vat ∩ (D i).Wpre ∩
        {y | ∀ j, normW (collarAuxNorm A N₀ N₁) ((D i).S j y) < (D i).M} := fun i =>
    LocalPart.exists_bump_pos_on_compact_cube (X := A.X) (n := 1) hT
      ((D i).isCompact_closure_inter hK)
      (fun y hy => ⟨mem_univ _, Or.inl (Or.inr ⟨(A.cubeSEP 1).X.π y, hy.2, rfl⟩)⟩)
      (((D i).hVat.inter (D i).hWpre).inter (D i).hBopen) (fun y hy => (D i).hNcl hy.1)
  choose β Vs Cs hVso hVss hTV hβ hβ0 hβpos hCs hβCs hCsN using hB
  -- the set `V`
  have hVo : IsOpen (⋂ i, Vs i) := isOpen_iInter_of_finite hVso
  have hVsat : A.X.IsSaturated (⋂ i, Vs i) := A.X.isSaturated_iff.2 fun φ hφ =>
    mem_iInter.2 fun i => (A.X.isSaturated_iff.1 (hVss i)) φ (mem_iInter.1 hφ i)
  have hV : A.X.IsEpSubgroupoid (⋂ i, Vs i) := A.X.isEpSubgroupoid_of_isOpen hVo hVsat
  have hTV' : ∀ {x : A.Obj}, A.X.π x ∈ (closure (A.X.π '' {x ∈ U₀ | A.B.AuxLe N₀ (f x) 1}) ∪
        closure (A.X.π '' {x ∈ U₁ | A.B.AuxLe N₁ (f x) 1}) ∪
        (A.X.cubeProj 1).orbitMap '' ((A.cubeSEP 1).X.π ''
          {z | 0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1 z)}) ∪
        ⋃ i, (fun y : (A.cubeSEP 1).Obj => A.X.π y.2) '' Z i) → x ∈ ⋂ i, Vs i :=
    fun hx => mem_iInter.2 fun i => hTV i hx
  have hK₀ : A.X.π ⁻¹' closure (A.X.π '' {x ∈ U₀ | A.B.AuxLe N₀ (f x) 1}) ⊆ ⋂ i, Vs i :=
    fun x hx => hTV' (Or.inl (Or.inl (Or.inl hx)))
  have hK₁ : A.X.π ⁻¹' closure (A.X.π '' {x ∈ U₁ | A.B.AuxLe N₁ (f x) 1}) ⊆ ⋂ i, Vs i :=
    fun x hx => hTV' (Or.inl (Or.inl (Or.inr hx)))
  have hZV : ∀ i, Z i ⊆ Prod.snd ⁻¹' (⋂ i, Vs i) := fun i y hy =>
    hTV' (Or.inr (mem_iUnion.2 ⟨i, y, hy, rfl⟩))
  refine ⟨⋂ i, Vs i, hV, hVo, hK₀, hK₁, fun x' hxb hpos => ?_⟩
  have hpos₀ : 0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1
      (cubeRestrBase hV x')) := by
    rw [← cubeRestrFib_cubeLiftEp hV hf.1.1.1, ← cylExtension_restrMult hV hVo]
    exact hpos
  rcases hcov _ hpos₀ with ⟨i, hi⟩ | ⟨k, hk⟩
  · obtain ⟨Q', hQo, hQs, hfam, hc⟩ := exists_relGPFamily_of_centreData hV hd hpara hf hft hr₀ hr₁
      hVo hK₀ hK₁ (D i) (hZc i) (hKZ i) (hzZ i) (hZU i) (hZV i)
      ((hβ i).mono (isOpen_univ.prod hVo) (prod_mono subset_rfl (iInter_subset _ i)))
      (hβpos i) (hCs i) (hβCs i) (hCsN i)
    exact ⟨Q', hQo, hQs, hc x' ⟨_, hpos₀, rfl⟩ hi, hfam⟩
  · obtain ⟨h1, h2, h3⟩ := nonempty_relGPFamily_preimage hV hpara hf hft hr₀ hr₁ hVo hK₀ hK₁
      (hP k).1 (hP k).2.1 (hP k).2.2 _ _
    exact ⟨_, h1, h2, hk, h3⟩

end Cylinder

end SBLocalization

end Polyfold
