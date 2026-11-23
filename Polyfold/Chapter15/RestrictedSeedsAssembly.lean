import Polyfold.Chapter15.RestrictedSeedsInclusion
import Polyfold.Chapter15.RestrictedSeedsCompare2
import Polyfold.Chapter15.RestrictedCobordism

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Corollary 15.3.10 (3)
(p. 699) and the proof of Theorem 15.3.9, steps (c)–(d) (pp. 698–699), with the functions of
Remark 9.5.19 (p. 451) in place of sc-smooth bump functions.

# The local families on the cylinder of a restriction

## The text, paraphrased

The perturbation of the cylinder `[0, 1] × X` is built near the compact solution set from
finitely many local families; near the two ends nothing is added, since the end data are in
general position there.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `exists_seedCentre_of_le`: the data of one centre (`exists_seedCentre`) at an interior point of
  `supp(Λ₀ ∘ f)` with `N(Λ₀) < h` there, inside `U ∖ ∂X`, with a margin `c ≤ h − N(Λ₀)` on
  `U(x)`.
* **`hasRestrictedCylinderFamilies_of_seedCentres`**: for two transversal perturbations of an
  sc-Fredholm section functor with tame germ data, `d_X ≡ 0`, `|X|` paracompact and sc⁺-sections
  through the smooth fibre points, there is a saturated open `V` containing the controlled sets
  such that the cylinder of `X|V` has local families at the interior points of the solution set
  of the extension (`HasRestrictedCylinderFamilies`).  No bump functions on `X` are assumed.

## Reading

The order of the choices: the data of the centres and the open sets around the boundary
solution points on `[0, 1] × X`; a finite cover of the compact solution set; compact connected
sets joining the centres to the covered solution points; finitely many functions, sc-smooth
near the compact set made of the controlled sets and of these connected sets; `V` is the
intersection of their domains.
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

section Centre

variable {A : SEP.{u}} {f : A.Obj → A.W} {Λ₀ : A.W → ℚ≥0} {N : A.B.One → ℝ} {U : Set A.Obj}

/-- **The data of one centre at an interior point of `supp(Λ₀ ∘ f)`** (steps (c)–(d) of the
proof of Theorem 15.3.9, 2021 pp. 698–699): as `exists_seedCentre`, with `U(x) ⊆ U ∖ ∂X` and a
margin `0 < c ≤ h − N(Λ₀)` on `U(x)`. -/
theorem exists_seedCentre_of_le (hX : A.X.IsTame) (hsec : A.B.HasScPlusSectionsThrough)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hcc : ControlsCompactness A f N U) (hΛ₀ : IsScPlusMultisection A Λ₀)
    (hdom₀ : domSupp Λ₀ ⊆ U) {h : A.Obj → ℝ} (hhc : Continuous h) (hh1 : ∀ x, h x ≤ 1)
    (hN₀ : ∀ x, pointwiseNorm N Λ₀ x ≤ h x) {x : A.Obj} (hxb : x ∉ A.X.PObj.boundary)
    (hx : 0 < Λ₀ (f x)) (hlt : pointwiseNorm N Λ₀ x < h x) :
    ∃ (R : A.X.NaturalRep x) (Vat G₀ N' : Set A.Obj) (ℓ : ℕ) (S : Fin ℓ → A.Obj → A.W)
      (hS : ∀ j, A.B.IsScPlusSection (S j)) (M c : ℝ),
      A.X.HasPropernessProperty R.U ∧ R.U ⊆ U ∩ A.X.PObj.boundaryᶜ ∧ 0 < c ∧
      (∀ y ∈ R.U, c ≤ h y - pointwiseNorm N Λ₀ y) ∧ IsOpen Vat ∧ x ∈ Vat ∧
      (∀ g, MapsTo (R.Φ g) Vat Vat) ∧ closure Vat ⊆ R.U ∧ 0 < M ∧
      IsOpen G₀ ∧ G₀ ⊆ Vat ∧ (∀ y ∈ G₀, ∀ j, normW N (S j y) < M) ∧
      (∀ y : A.X.PObj.Level 1, A.X.PObj.levelVal 1 y ∈ G₀ →
        0 < Λ₀ (f (A.X.PObj.levelVal 1 y)) →
          IsParamOntoVecRel f Λ₀ y (fun j => ⟨S j (A.X.PObj.levelVal 1 y), (hS j).1 _⟩)) ∧
      IsOpen N' ∧ x ∈ N' ∧ closure N' ⊆ G₀ ∧ (∀ g, MapsTo (R.Φ g) N' N') ∧
      ∀ K : Set A.Obj, IsCompact K → K ⊆ closure N' →
        ∃ Z : Set A.Obj, IsCompact Z ∧ IsPreconnected Z ∧ K ⊆ Z ∧ x ∈ Z ∧ Z ⊆ R.U := by
  have hNB : A.B.IsAuxNorm N := hcc.1.isAuxNorm
  have hxU : x ∈ U := (auxLe_of_pos hf.1.1.1 hΛ₀ hcc.2.2.2.1
    (fun y => (hN₀ y).trans (hh1 y)) hdom₀ hx).1
  set c : ℝ := (h x - pointwiseNorm N Λ₀ x) / 4 with hcdef
  set r : ℝ := (h x + pointwiseNorm N Λ₀ x) / 2 with hrdef
  have hc : 0 < c := by rw [hcdef]; linarith
  set W₁ : Set A.Obj := (U ∩ A.X.PObj.boundaryᶜ) ∩
    ({y | pointwiseNorm N Λ₀ y < r} ∩ {y | r + c < h y}) with hW₁def
  have hW₁ : IsOpen W₁ := (hcc.2.1.inter A.X.PObj.isClosed_boundary.isOpen_compl).inter
    ((isOpen_pointwiseNorm_lt hNB hΛ₀ continuous_const).inter (isOpen_lt continuous_const hhc))
  have hxW₁ : x ∈ W₁ := by
    refine ⟨⟨hxU, hxb⟩, ?_, ?_⟩
    · change pointwiseNorm N Λ₀ x < r
      rw [hrdef]; linarith
    · change r + c < h x
      rw [hrdef, hcdef]; linarith
  obtain ⟨R, Vat, G₀, N', ℓ, S, hS, M, hprop, hRU, hVo, hxV, hVinv, hVcl, hM, hG₀o, hG₀V,
    hG₀M, hG₀on, hN'o, hxN', hN'cl, hN'inv, hconn⟩ :=
    exists_seedCentre hX hsec hf hft hΛ₀ hNB hx hW₁ hxW₁
  refine ⟨R, Vat, G₀, N', ℓ, S, hS, M, c, hprop, hRU.trans inter_subset_left, hc,
    fun y hy => ?_, hVo, hxV, hVinv, hVcl, hM, hG₀o, hG₀V, hG₀M, hG₀on, hN'o, hxN', hN'cl,
    hN'inv, hconn⟩
  have h1 : pointwiseNorm N Λ₀ y < r := (hRU hy).2.1
  have h2 : r + c < h y := (hRU hy).2.2
  linarith

end Centre

section Cylinder

variable {A : SEP.{u}} {f : A.Obj → A.W}

set_option maxHeartbeats 6400000 in
-- the cylinder of the restriction and the ambient cylinder are unfolded in the hypotheses
/-- **The local families on the cylinder of a restriction `X|V`, without bump functions on
`X`** (Corollary 15.3.10 (3), 2021 p. 699; steps (c)–(d) of the proof of Theorem 15.3.9,
pp. 698–699).  Let `d_X ≡ 0`, `|X|` be paracompact, `f` be an sc-Fredholm section functor with
tame germ data and with sc⁺-sections through the smooth fibre points, and let `(Nⁱ, Uⁱ, Λⁱ)`,
`i = 0, 1`, be transversal perturbations.  Then there is a saturated open `V` containing the two
controlled sets such that on the cylinder of `X|V` the extension of the restricted end data has
local families at the interior points of its solution set. -/
theorem hasRestrictedCylinderFamilies_of_seedCentres (hd : ∀ x, A.X.PObj.degIndex x = 0)
    (hpara : A.X.HasParacompactOrbitSpace) (hsec : A.B.HasScPlusSectionsThrough)
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    {N₀ N₁ : A.B.One → ℝ} {U₀ U₁ : Set A.Obj} {Λ₀ Λ₁ : A.W → ℚ≥0}
    (hr₀ : IsTransversalPerturbation A f N₀ U₀ Λ₀)
    (hr₁ : IsTransversalPerturbation A f N₁ U₁ Λ₁) :
    HasRestrictedCylinderFamilies A f hf N₀ N₁ U₀ U₁ Λ₀ Λ₁ := by
  classical
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PMor
  -- the ambient cylinder
  have hX : A.X.IsTame := A.X.isTame_of_degIndex_eq_zero hd
  have hXC : (A.cubeSEP 1).X.IsTame := A.X.isTame_cubeProd 1 hX
  have hcc := controlsCompactness_collar hf.1.1.1 hr₀.1 hr₁.1
  have hfC := isScFredholmSectionFunctor_cubeLiftEp (n := 1) hf hft
  have hftC : (A.cubeSEP 1).B.IsScFredholmSectionTame (cubeLiftEp (n := 1) f hf.1.1.1) :=
    isScFredholmSectionTame_cubeLiftEp (n := 1) hft
  have hsecC := hasScPlusSectionsThrough_cubeSEP hsec
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
  have hsecf : IsSection (A.cubeSEP 1).P (cubeLiftEp (n := 1) f hf.1.1.1) := hfC.1.1.1
  have hbd : ∀ x : (A.cubeSEP 1).X.PObj.Level 1,
      (A.cubeSEP 1).X.PObj.levelVal 1 x ∈ (A.cubeSEP 1).X.PObj.boundary →
      0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1
        ((A.cubeSEP 1).X.PObj.levelVal 1 x)) →
      IsReducedOntoAtPt (cubeLiftEp (n := 1) f hf.1.1.1) (cylExtension Λ₀ Λ₁) x := by
    intro x hx hpos
    have hPx : (A.cubeSEP 1).P (cubeLiftEp (n := 1) f hf.1.1.1
        ((A.cubeSEP 1).X.PObj.levelVal 1 x)) ∈ (A.cubeSEP 1).X.PObj.boundary := by
      rw [hsecf]; exact hx
    exact hbonto _ hE hglue x hx (mem_smoothSet_of_pos hftC hE hpos)
      (by rw [← hglue _ hPx]; exact hpos)
  set h : (A.cubeSEP 1).Obj → ℝ :=
    fun z => (1 + (collarCut₀ (cubeT z) + collarCut₁ (cubeT z))) / 2 with hdef
  have hhc : Continuous h :=
    (continuous_const.add ((contDiff_collarCut₀.continuous.comp continuous_cubeT).add
      (contDiff_collarCut₁.continuous.comp continuous_cubeT))).div_const 2
  have hh1 : ∀ z, h z ≤ 1 := fun z => by
    have := collarCut_add_le_one (cubeT z)
    rw [hdef]; dsimp only; linarith
  have hNle : ∀ z, pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension Λ₀ Λ₁) z ≤ h z :=
    fun z => by
      have := collarCut_add_le_one (cubeT z)
      have := hEN z
      rw [hdef]; dsimp only; linarith
  have hNlt : ∀ z ∉ (A.cubeSEP 1).X.PObj.boundary,
      pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension Λ₀ Λ₁) z < h z := fun z hz => by
    have hz' := (not_congr (mem_boundary_cubeSEP_iff hX hd z)).1 hz
    rw [not_or] at hz'
    have t0 : (0 : ℝ) ≤ cubeT z := (z.1 0).2.1
    have t1 : cubeT z ≤ 1 := (z.1 0).2.2
    have t0' : (0 : ℝ) < cubeT z := lt_of_le_of_ne t0 (Ne.symm hz'.1)
    have t1' : cubeT z < 1 := lt_of_le_of_ne t1 hz'.2
    have := collarCut_add_lt_one t0' t1'
    have := hEN z
    rw [hdef]; dsimp only; linarith
  have hfc : Continuous (cubeLiftEp (n := 1) f hf.1.1.1) :=
    continuousOn_univ.1 hftC.isScSmooth.2.continuousOn
  have hN1 : ∀ z, pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension Λ₀ Λ₁) z ≤ 1 :=
    fun z => (hNle z).trans (hh1 z)
  -- the solution set
  set Sol : Set (A.cubeSEP 1).Obj :=
    {p | 0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1 p)} with hSoldef
  have hK : IsCompact ((A.cubeSEP 1).X.π '' Sol) :=
    isCompact_image_supp_comp hfC hfc hE hcc hN1 hEdom
  have hSolsat : ∀ φ : (A.cubeSEP 1).Mor, (A.cubeSEP 1).X.src φ ∈ Sol →
      (A.cubeSEP 1).X.tgt φ ∈ Sol := fun φ hφ => by
    have h0 := comp_tgt_eq_src hfC hE φ
    have h1 : 0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1
        ((A.cubeSEP 1).X.src φ)) := hφ
    rw [← h0] at h1
    exact h1
  -- the centres
  let ι : Type u := {p : (A.cubeSEP 1).Obj // p ∉ (A.cubeSEP 1).X.PObj.boundary ∧ p ∈ Sol}
  let κ : Type u := {p : (A.cubeSEP 1).Obj // p ∈ (A.cubeSEP 1).X.PObj.boundary ∧ p ∈ Sol}
  have hI : ∀ i : ι, _ := fun i =>
    exists_seedCentre_of_le hXC hsecC hfC hftC hcc hE hEdom hhc hh1 hNle i.2.1 i.2.2
      (hNlt i.1 i.2.1)
  choose R Vat G₀ N' ℓ S hS M c hprop hRU hc hRc hVo hxV hVinv hVcl hM hG₀o hG₀V hG₀M hG₀on
    hN'o hxN' hN'cl hN'inv hconn using hI
  have hB : ∀ k : κ, ∃ Q : Set (A.cubeSEP 1).Obj, IsOpen Q ∧ (A.cubeSEP 1).X.IsSaturated Q ∧
      k.1 ∈ Q ∧ ∀ y : (A.cubeSEP 1).X.PObj.Level 1, (A.cubeSEP 1).X.PObj.levelVal 1 y ∈ Q →
        0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1
          ((A.cubeSEP 1).X.PObj.levelVal 1 y)) →
        IsReducedOntoAtPt (cubeLiftEp (n := 1) f hf.1.1.1) (cylExtension Λ₀ Λ₁) y := fun k => by
    have hx1 := mem_levelSet_one_of_pos hfC hE k.2.2
    exact exists_isOpen_isReducedOntoAtPt hXC hfC hftC hE hx1
      (hbd _ (by rw [(A.cubeSEP 1).X.PObj.levelVal_levelMk]; exact k.2.1)
        (by rw [(A.cubeSEP 1).X.PObj.levelVal_levelMk]; exact k.2.2))
  choose Qb hQbo hQbs hQbx hQbr using hB
  -- the finite cover
  let Ocov : ι ⊕ κ → Set (A.cubeSEP 1).X.OrbitSpace :=
    Sum.elim (fun i => (A.cubeSEP 1).X.π '' N' i) (fun k => (A.cubeSEP 1).X.π '' Qb k)
  have hOcov : ∀ j, IsOpen (Ocov j) := fun j => by
    rcases j with i | k
    · exact (A.cubeSEP 1).X.proposition_7_1_8 _ (hN'o i)
    · exact (A.cubeSEP 1).X.proposition_7_1_8 _ (hQbo k)
  have hcover : (A.cubeSEP 1).X.π '' Sol ⊆ ⋃ j, Ocov j := by
    rintro _ ⟨p, hp, rfl⟩
    by_cases hpb : p ∈ (A.cubeSEP 1).X.PObj.boundary
    · exact mem_iUnion.2 ⟨Sum.inr ⟨p, hpb, hp⟩, p, hQbx ⟨p, hpb, hp⟩, rfl⟩
    · exact mem_iUnion.2 ⟨Sum.inl ⟨p, hpb, hp⟩, p, hxN' ⟨p, hpb, hp⟩, rfl⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover Ocov hOcov hcover
  -- the compact sets
  set T₀ : Set A.X.OrbitSpace :=
    (closure (A.X.π '' {x ∈ U₀ | A.B.AuxLe N₀ (f x) 1}) ∪
      closure (A.X.π '' {x ∈ U₁ | A.B.AuxLe N₁ (f x) 1})) ∪
      (A.X.cubeProj 1).orbitMap '' ((A.cubeSEP 1).X.π '' Sol) with hT₀def
  have hT₀ : IsCompact T₀ := (hr₀.1.2.2.2.2.union hr₁.1.2.2.2.2).union
    (hK.image (A.X.cubeProj 1).continuous_orbitMap)
  have hSolT : ∀ p : (A.cubeSEP 1).Obj, (A.cubeSEP 1).X.π p ∈ (A.cubeSEP 1).X.π '' Sol →
      A.X.π p.2 ∈ T₀ := fun p hp => Or.inr ⟨_, hp, rfl⟩
  set Kc : ι → Set (A.cubeSEP 1).Obj := fun i =>
    (closure (R i).U ∩ (A.cubeSEP 1).X.π ⁻¹' ((A.cubeSEP 1).X.π '' Sol)) ∩ closure (N' i)
    with hKcdef
  have hKc : ∀ i, IsCompact (Kc i) := fun i =>
    (LocalPart.isCompact_inter_preimage_π (hprop i).2 hK).inter_right isClosed_closure
  have hZ : ∀ i, _ := fun i => hconn i (Kc i) (hKc i) inter_subset_right
  choose Z hZc hZp hKZ hxZ hZU using hZ
  let Zim : ι ⊕ κ → Set A.X.OrbitSpace :=
    Sum.elim (fun i => (fun p : (A.cubeSEP 1).Obj => A.X.π p.2) '' Z i) (fun _ => ∅)
  set T₁ : Set A.X.OrbitSpace := T₀ ∪ ⋃ j ∈ t, Zim j with hT₁def
  have hT₁ : IsCompact T₁ := hT₀.union (t.isCompact_biUnion fun j _ => by
    rcases j with i | k
    · exact (hZc i).image (A.X.continuous_π.comp continuous_snd)
    · exact isCompact_empty)
  -- the functions
  have hβ : ∀ i : ι, _ := fun i =>
    LocalPart.exists_bump_pos_on_compact_cube (X := A.X) (n := 1) hT₁ (hKc i)
      (fun y hy => ⟨mem_univ _, Or.inl (hSolT y hy.1.2)⟩) (hG₀o i)
      (fun y hy => hN'cl i hy.2)
  choose β Vβ Cβ hVβo hVβs hVβT hβsm hβ0 hβpos hCβ hβC hCβG using hβ
  -- the set `V`
  let Vfam : ι ⊕ κ → Set A.Obj := Sum.elim (fun i => Vβ i) (fun _ => univ)
  set V : Set A.Obj := ⋂ j ∈ t, Vfam j with hVdef
  have hVopen : IsOpen V := isOpen_biInter_finset fun j _ => by
    rcases j with i | k
    · exact hVβo i
    · exact isOpen_univ
  have hVsat : A.X.IsSaturated V := A.X.isSaturated_iff.2 fun φ hφ => by
    refine mem_iInter₂.2 fun j hj => ?_
    have h1 := mem_iInter₂.1 hφ j hj
    rcases j with i | k
    · exact A.X.isSaturated_iff.1 (hVβs i) φ h1
    · exact mem_univ _
  have hT₁V : A.X.π ⁻¹' T₁ ⊆ V := fun x hx => mem_iInter₂.2 fun j _ => by
    rcases j with i | k
    · exact hVβT i hx
    · exact mem_univ _
  have hV : A.X.IsEpSubgroupoid V := A.X.isEpSubgroupoid_of_isOpen hVopen hVsat
  have hV₀ : A.X.π ⁻¹' closure (A.X.π '' {x ∈ U₀ | A.B.AuxLe N₀ (f x) 1}) ⊆ V :=
    fun x hx => hT₁V (Or.inl (Or.inl (Or.inl hx)))
  have hV₁ : A.X.π ⁻¹' closure (A.X.π '' {x ∈ U₁ | A.B.AuxLe N₁ (f x) 1}) ⊆ V :=
    fun x hx => hT₁V (Or.inl (Or.inl (Or.inr hx)))
  refine ⟨V, hV, hVopen, hV₀, hV₁, fun x' hx'b hx'pos => ?_⟩
  -- the cylinder of the restriction
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) (A.restr hV).X.PObj
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) (A.restr hV).X.PMor
  have hd₁ := degIndex_restr_eq_zero hV hVopen hd
  have hF₁ := isScFredholmSectionFunctor_restrSec hV hVopen hf
  have hft₁ := isScFredholmSectionTame_restrSec hV hVopen hf.1 hft
  have hpara₁ := hasParacompactOrbitSpace_restr hV hVopen hpara
  have hr₀' := isTransversalPerturbation_restr hV hVopen hf hr₀ hV₀
  have hr₁' := isTransversalPerturbation_restr hV hVopen hf hr₁ hV₁
  have hcc' := controlsCompactness_collar (isSection_restrSec hV hf.1.1.1) hr₀'.1 hr₁'.1
  have hfC' := isScFredholmSectionFunctor_cubeLiftEp (n := 1) hF₁ hft₁
  have h𝒰' : Nonempty ((A.restr hV).cubeSEP 1).X.GoodSystem := by
    obtain ⟨-, D, -⟩ := isStructurable_zeroMultisection (A := (A.restr hV).cubeSEP 1)
      ((A.restr hV).X.hasParacompactOrbitSpace_cubeProd (n := 1) hpara₁)
    exact ⟨D.𝒰⟩
  have hE' := isScPlusMultisection_cylExtension hr₀'.2.1 hr₁'.2.1
  have hΛL : ∀ w : ((A.restr hV).cubeSEP 1).W,
      cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁) w =
        cylExtension Λ₀ Λ₁ (cubeRestrFib hV w) := cylExtension_restrMult hV hVopen Λ₀ Λ₁
  have hpn : ∀ z : ((A.restr hV).cubeSEP 1).Obj,
      pointwiseNorm (collarAuxNorm (A.restr hV) (restrNorm hV N₀) (restrNorm hV N₁))
          (cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁)) z =
        pointwiseNorm (collarAuxNorm A N₀ N₁) (cylExtension Λ₀ Λ₁) (cubeRestrBase hV z) :=
    pointwiseNorm_collarAuxNorm_cylExtension_restr hV hVopen N₀ N₁ Λ₀ Λ₁
  -- the image of `x'`
  set z : (A.cubeSEP 1).Obj := cubeRestrBase hV x' with hzdef
  have hzSol : z ∈ Sol := by
    change 0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1 (cubeRestrBase hV x'))
    rw [← cubeRestrFib_cubeLiftEp hV hf.1.1.1 x', ← hΛL]
    exact hx'pos
  obtain ⟨j, hjt, hzj⟩ := mem_iUnion₂.1 (ht ⟨z, hzSol, rfl⟩)
  rcases j with i | k
  · -- an interior centre
    have hZV : ∀ q ∈ Z i, q.2 ∈ V := fun q hq =>
      hT₁V (Or.inr (mem_iUnion₂.2 ⟨Sum.inl i, hjt, q, hq, rfl⟩))
    let xc : ((A.restr hV).cubeSEP 1).Obj := (i.1.1, (⟨i.1.2, hZV _ (hxZ i)⟩ : V))
    let F := cubeRestrInclusion hV hVopen xc.2
    obtain ⟨Q, hQo, hQs, hQmem, hQF⟩ := exists_relGPFamily_of_openInclusion F
      (cubeRestrIso hV hVopen xc) rfl hfC' hfC hE' hE
      (eqOn_cubeLiftEp_restrSec hV hVopen hf.1.1.1 xc) hΛL hcc'.1
      (normW_collarAuxNorm_restr hV N₀ N₁) h𝒰'
      (U' := interpSet (A.restr hV) (restrBase hV ⁻¹' U₀) (restrBase hV ⁻¹' U₁) ∩
        ((A.restr hV).cubeSEP 1).X.PObj.boundaryᶜ)
      (isSaturated_inter_boundary_compl hcc'.2.2.1)
      (g' := fun z => (1 + (collarCut₀ (cubeT z) + collarCut₁ (cubeT z))) / 2 -
        pointwiseNorm (collarAuxNorm (A.restr hV) (restrNorm hV N₀) (restrNorm hV N₁))
          (cylExtension (restrMult hV Λ₀) (restrMult hV Λ₁)) z)
      (fun y => by
        rw [hpn y]
        exact sub_nonneg.2 (hNle (cubeRestrBase hV y)))
      (fun φ => by
        change _ - _ = _ - _
        rw [pointwiseNorm_tgt hcc'.1 hE' φ]
        rfl)
      xc (R i) (hprop i) (hVo i) (hxV i) (hVinv i) (hVcl i) (hS i) (hM i) (hc i) (hG₀V i)
      (hG₀M i) (hG₀on i) (hN'o i) ((subset_closure).trans (hN'cl i)) (hN'inv i)
      (fun y' hy' => ⟨(hRU i hy').1, fun hb =>
        (hRU i hy').2 ((mem_boundary_cubeRestr_iff hV hVopen y').1 hb)⟩)
      (fun y' hy' => by
        have h1 := hRc i _ hy'
        change c i ≤ _ - _
        rw [hpn y']
        exact h1)
      ((hβsm i).mono (hVopen.preimage continuous_snd)
        (fun q (hq : q.2 ∈ V) => (⟨mem_univ _, mem_iInter₂.1 hq (Sum.inl i) hjt⟩ :
          q ∈ (univ : Set (Fin 1 → unitInterval)) ×ˢ Vβ i)))
      (hCβ i) (hβC i) (hCβG i)
      (fun y hyN hyV hypos => by
        have hyK : y ∈ Kc i :=
          ⟨⟨subset_closure (hVcl i (subset_closure (hG₀V i (hN'cl i (subset_closure hyN))))),
            y, hypos, rfl⟩, subset_closure hyN⟩
        refine ⟨?_, (hβpos i y hyK).ne'⟩
        have hZsub : Z i ⊆ (R i).U ∩
            (Prod.snd ⁻¹' V : Set ((Fin 1 → unitInterval) × A.Obj)) :=
          fun q hq => ⟨hZU i hq, hZV q hq⟩
        exact (hZp i).subset_connectedComponentIn (hxZ i) hZsub (hKZ i hyK))
    exact ⟨Q, hQo, hQs, hQmem x' hzj hx'pos, hQF⟩
  · -- near a boundary solution point
    have hzQ : z ∈ Qb k := by
      rw [← hQbs k]; exact hzj
    refine ⟨cubeRestrBase hV ⁻¹' Qb k, (hQbo k).preimage (continuous_cubeRestrBase hV),
      isSaturated_preimage_cubeRestrBase hV (hQbs k), hzQ,
      ⟨RelGPFamily.zeroOn h𝒰' hcc'.1.isAuxNorm fun y hy hpos => ?_⟩⟩
    have hy1 : cubeRestrBase hV (((A.restr hV).cubeSEP 1).X.PObj.levelVal 1 y) ∈
        (A.cubeSEP 1).X.PObj.levelSet 1 :=
      (mem_levelSet_cubeRestr_iff hV hVopen _ 1).1
        (((A.restr hV).cubeSEP 1).X.PObj.levelVal_mem y)
    have hlv := (A.cubeSEP 1).X.PObj.levelVal_levelMk 1 _ hy1
    have hpos' : 0 < cylExtension Λ₀ Λ₁ (cubeLiftEp (n := 1) f hf.1.1.1
        (cubeRestrBase hV (((A.restr hV).cubeSEP 1).X.PObj.levelVal 1 y))) := by
      rw [← cubeRestrFib_cubeLiftEp hV hf.1.1.1, ← hΛL]
      exact hpos
    have hred := hQbr k ((A.cubeSEP 1).X.PObj.levelMk 1 _ hy1) (by rw [hlv]; exact hy)
      (by rw [hlv]; exact hpos')
    exact (isReducedOntoAtLevel_localIso_iff (cubeRestrIso hV hVopen x') hfC' hfC hE
      (eqOn_cubeLiftEp_restrSec hV hVopen hf.1.1.1 x') (fun w _ => hΛL w) (mem_univ _)
      (by rw [hlv]; rfl)).2 hred

end Cylinder

end SBLocalization

end Polyfold
