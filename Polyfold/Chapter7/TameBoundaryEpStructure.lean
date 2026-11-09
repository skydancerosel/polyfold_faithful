import Polyfold.Chapter2.TameBoundaryStructure
import Polyfold.Chapter7.TameBoundaryEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 7,
Appendix §7.6.5.2 "The Case of Tame Ep-Groupoids" (pp. 353–355), new in the 2021 edition:
**Theorem 7.6.9 (2)–(5)** (p. 355) and the characterization after it.  This completes
`Polyfold/Chapter7/TameBoundaryEp.lean` (the sets `bX`, `b𝐗`, the structure maps (7.25)–(7.29),
the groupoid laws and the topological part of Theorem 7.6.9) with the tame M-polyfold structures
of `Polyfold/Chapter2/TameBoundaryStructure.lean` (2021 Theorem 2.7.13 (2)–(4)).

# The boundary ep-groupoid of a tame ep-groupoid

## The text, paraphrased

(Theorem 7.6.9, p. 355, the verification left to the reader) For a tame ep-groupoid `(X, 𝐗)`:
(2) `bX` and `b𝐗`, with their natural topologies, carry natural tame M-polyfold structures;
(3) both maps `B` are sc-smooth; (4) `d_X(B(p)) − 1 = d_{bX}(p)` on `bX` and
`d_𝐗(B(a)) − 1 = d_{b𝐗}(a)` on `b𝐗`; (5) `(bX, b𝐗)` with `s, t, u, ι, m` of (7.25)–(7.29) is a
tame ep-groupoid, the structure maps having the usual smoothness properties.  Topology and
structure of `bX` are characterized as in Theorem 2.7.13 (every `U(x, V, θ)` open, every
`Φ_{(x,V,θ)}` a homeomorphism and an sc-diffeomorphism onto the face `θ`), and similarly for `b𝐗`.
(The sketch) For `[φ, 𝐕, θ]` pick `𝐕` with `s : 𝐕 → V` an sc-diffeomorphism and put `θ = s(θ)`;
in the charts `Φ_{(φ,𝐕,θ)}`, `Φ_{(x,V,θ)}` the map `s : U(φ, 𝐕, θ) → U(x, V, θ)` becomes
`s : θ → s(θ)`, an sc-diffeomorphism, which gives the smoothness of `s`.

## What is formalized

* `MPolyfold.isScSmoothOn_of_bMap`: a continuous map `g : bA → bB` of tame boundaries covering an
  sc-smooth `f : A → B` (`B ∘ g = f ∘ B`) is sc-smooth; in the charts `p ↦ π(φ(B p))` of
  `tameBoundaryPolyfold` it is `π' ∘ (φ' ∘ f ∘ φ⁻¹) ∘ ι`.
* `MPolyfold.isScSmoothMap_bLift`: the lift `bf` (`TameBoundary.bLift`) of an sc-smooth
  index-preserving local homeomorphism is sc-smooth.  `MPolyfold.isLocalScDiffeo_bLift`: the lift
  of a local sc-diffeomorphism is a local sc-diffeomorphism (over a sheet `f : W → V` it maps
  `B⁻¹(W)` onto `B⁻¹(V)`, with an inverse covering `(f|W)⁻¹`).
* For a tame ep-groupoid: `EpGroupoid.bPObj`, `bPMor` (the structures of (2));
  `isLocalScDiffeo_bSrc`, `isLocalScDiffeo_bTgt`, `isScSmoothMap_bUnit`, `isScSmoothMap_bInv`,
  `isScSmoothCompSheet_bComp`, `isScSmoothComp_bComp`; `phiTot_bSrc` (the commutative diagram of
  the sketch); `boundaryEpGroupoid` (**(5)**: the `EpGroupoid` `(bX, b𝐗)`),
  `isTame_boundaryEpGroupoid`; `boundaryEpFunctor` (`B` is an ep-functor, a morphism of the
  category `EP` of 2021 Definition 7.1.7 (2017: Definition 7.7)).
* **Theorem 7.6.9**, `theorem_7_6_9_full`: (1) metrizability; (2) the tame structures, with
  the characterization and its uniqueness, for `bX` and for `b𝐗`; (3); (4) as printed; (5) the
  tame ep-groupoid with its structure maps; and `B` an ep-functor.  The characterization of the
  topologies in (1) is `theorem_7_6_9`.
* Witness: `trivial_quadrant_boundaryEp_witness` (the trivial ep-groupoid of the tame quadrant
  `[0,∞)ⁿ ⊕ W`, `n ≥ 1`: its boundary ep-groupoid is tame with nonempty object and morphism
  sets, and over the corner `d_{bX} = n − 1`).

## What the text leaves implicit, and the choices made

* The sketch's sc-diffeomorphism `s : θ → s(θ)` between faces is replaced by the computation in
  the charts of `tameBoundaryPolyfold`: there every lift is `π' ∘ (φ' ∘ f ∘ φ⁻¹) ∘ ι`, which needs
  only that `f` is sc-smooth.  The diagram itself, `Φ_{(x,V,θ)} ∘ s = s ∘ Φ_{(φ,𝐕,θ)}` on
  `U(φ, 𝐕, θ)`, is `phiTot_bSrc`.
* "Natural tame M-polyfold structures" are `tameBoundaryPolyfold` of the object and of the
  morphism M-polyfold (`𝐗` is tame, `isTame_PMor`); "natural" is read through the
  characterization and its uniqueness, for representatives with `V` centred at `x` as in
  Chapter 2.
* Condition (4) of an ep-groupoid (2021 Definition 7.1.3 (2017: Definition 7.3); `m` sc-smooth on
  `b𝐗 ₛ×ₜ b𝐗`) is proved in the sheet form `IsScSmoothCompSheet` and converted by
  `isScSmoothComp_iff_sheet`: near `b`, the map `b' ↦ m(σ(t b'), b')` covers
  `γ ↦ m(σ₁(t γ), γ)` for a sheet `σ₁` of `s` on `𝐗`, which is sc-smooth.
* (4) is stated as printed, with natural-number subtraction (`B` takes values in `∂X`, where
  `d_X ≥ 1`); the additive form is `MPolyfold.degIndex_tameBoundaryMap`.
* The paracompactness of `bX` and `b𝐗` (2021 Proposition 2.7.16) is registered as the instances
  `paracompactSpace_bObj`, `paracompactSpace_bMor`.
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

noncomputable section

namespace Polyfold

namespace MPolyfold

open TameBoundary

universe u v

variable {A : Type u} [TopologicalSpace A] [T2Space A] [ParacompactSpace A] {P : MPolyfold A}
  {B : Type v} [TopologicalSpace B] [T2Space B] [ParacompactSpace B] {Q : MPolyfold B}

/-- Sc-smoothness on an open set is local. -/
private theorem isScSmoothOn_of_local' {f : A → B} {U : Set A} (hU : IsOpen U)
    (h : ∀ x ∈ U, ∃ W : Set A, x ∈ W ∧ P.IsScSmoothOn Q f W) : P.IsScSmoothOn Q f U := by
  have hcont : ContinuousOn f U := fun x hx => by
    obtain ⟨W, hxW, hW⟩ := h x hx
    exact (hW.continuousOn.continuousAt (hW.isOpen.mem_nhds hxW)).continuousWithinAt
  refine MPolyfold.IsScSmoothOn.of_exists_charts hU hcont fun x hx => ?_
  obtain ⟨W, hxW, hW⟩ := h x hx
  obtain ⟨φ, hφ, hxφ⟩ := P.exists_isChart_mem_source x
  obtain ⟨ψ, hψ, hfx⟩ := Q.exists_isChart_mem_source (f x)
  have hVo : IsOpen ((W ∩ U ∩ φ.source) ∩ f ⁻¹' ψ.source) :=
    (hW.continuousOn.mono fun y hy => hy.1.1).isOpen_inter_preimage
      ((hW.isOpen.inter hU).inter φ.isOpen_source) ψ.isOpen_source
  exact ⟨φ, ψ, _, hφ, hψ, hVo, ⟨⟨⟨hxW, hx⟩, hxφ⟩, hfx⟩, fun y hy => ⟨hy.1.1.2, hy.1.2⟩,
    fun y hy => hy.2, hW.smooth φ ψ hφ hψ _ hVo (fun y hy => ⟨hy.1.1.1, hy.1.2⟩) fun y hy => hy.2⟩

/-- **A map of tame boundaries covering an sc-smooth map is sc-smooth**: if `f : A → B` is
sc-smooth on `U` and `g : bA → bB` is continuous on an open `O ⊆ B⁻¹(U)` with `B ∘ g = f ∘ B` on
`O`, then `g` is sc-smooth on `O` (for `tameBoundaryPolyfold`).  In the charts `χ_D = π ∘ φ ∘ B`
of `bA` and `χ_{D'} = π' ∘ φ' ∘ B` of `bB` the map `g` is `π' ∘ (φ' ∘ f ∘ φ⁻¹) ∘ ι`. -/
theorem isScSmoothOn_of_bMap (hP : P.IsTame) (hQ : Q.IsTame) {f : A → B} {U : Set A}
    (hf : P.IsScSmoothOn Q f U) {g : P.TameBoundarySpace hP → Q.TameBoundarySpace hQ}
    {O : Set (P.TameBoundarySpace hP)} (hO : IsOpen O)
    (hOU : O ⊆ bMap (P.isCornerIndex_degIndex hP) ⁻¹' U) (hg : ContinuousOn g O)
    (hgB : ∀ p ∈ O, bMap (Q.isCornerIndex_degIndex hQ) (g p) =
      f (bMap (P.isCornerIndex_degIndex hP) p)) :
    (P.tameBoundaryPolyfold hP).IsScSmoothOn (Q.tameBoundaryPolyfold hQ) g O := by
  refine IsScSmoothOn.of_exists_charts hO hg fun p hp => ?_
  obtain ⟨D, hpD⟩ := P.exists_bChartData_mem hP p
  obtain ⟨D', hgD'⟩ := Q.exists_bChartData_mem hQ (g p)
  set V := (O ∩ D.chart.source) ∩ g ⁻¹' D'.chart.source with hVdef
  have hVo : IsOpen V := (hg.mono inter_subset_left).isOpen_inter_preimage
    (hO.inter D.chart.isOpen_source) D'.chart.isOpen_source
  set V₀ := (D.φ.source ∩ U) ∩ f ⁻¹' D'.φ.source with hV₀def
  have hV₀o : IsOpen V₀ := (hf.continuousOn.mono inter_subset_right).isOpen_inter_preimage
    (D.φ.isOpen_source.inter hf.isOpen) D'.φ.isOpen_source
  have hBV : ∀ q ∈ V, bMap _ q ∈ V₀ := fun q hq =>
    ⟨⟨D.bMap_mem_source hq.1.2, hOU hq.1.1⟩, by
      change f (bMap _ q) ∈ D'.φ.source
      rw [← hgB q hq.1.1]; exact D'.bMap_mem_source hq.2⟩
  have hfs := hf.smooth D.φ D'.φ D.isChart D'.isChart V₀ hV₀o (fun y hy => ⟨hy.1.2, hy.1.1⟩)
    fun y hy => hy.2
  have h1 : IsScSmoothRetractMap D.chart.model.E D.chart.model.C (D.chart '' V) D.φ.model.E
      D.φ.model.C (D.φ '' V₀) (faceIncl D.T D.i 0) := by
    refine (faceIncl D.T D.i).isScSmoothRetractMap
      (D.chart.isScRetract_image (fun q hq => hq.1.2) hVo) ?_
    rintro _ ⟨q, hq, rfl⟩
    rw [D.incl_chart hq.1.2]
    exact ⟨_, hBV q hq, rfl⟩
  have h3 : IsScSmoothRetractMap D'.φ.model.E D'.φ.model.C D'.φ.model.O D'.chart.model.E
      D'.chart.model.C univ (faceProj D'.T D'.i 0) :=
    (faceProj D'.T D'.i).isScSmoothRetractMap D'.φ.model.isScRetract (mapsTo_univ _ _)
  have h := h3.comp (hfs.comp h1 (D.φ.isScRetract_image (fun y hy => hy.1.1) hV₀o))
    D'.φ.model.isScRetract
  have heq : ∀ q ∈ V, (faceProj D'.T D'.i 0 ∘ ((D'.φ ∘ f ∘ D.φ.symm) ∘ faceIncl D.T D.i 0))
      (D.chart q) = D'.chart (g q) := by
    intro q hq
    change faceProj D'.T D'.i 0 (D'.φ (f (D.φ.symm (faceIncl D.T D.i 0 (D.chart q))))) =
      faceProj D'.T D'.i 0 (D'.φ (bMap _ (g q)))
    rw [D.incl_chart hq.1.2, D.φ.symm_apply_apply (D.bMap_mem_source hq.1.2), hgB q hq.1.1]
  refine ⟨D.chart, D'.chart, V, P.isChart_chart D, Q.isChart_chart D', hVo, ⟨⟨hp, hpD⟩, hgD'⟩,
    fun q hq => ⟨hq.1.1, hq.1.2⟩, fun q hq => hq.2, ?_⟩
  refine (h.mono_target ?_).congr ?_
  · rintro _ ⟨q, hq, rfl⟩
    exact (heq q hq).symm ▸ D'.chart_mem_O hq.2
  · rintro _ ⟨q, hq, rfl⟩
    refine (heq q hq).trans ?_
    change D'.chart (g q) = D'.chart (g (D.chart.symm (D.chart q)))
    rw [D.chart.symm_apply_apply hq.1.2]

variable (hP : P.IsTame) (hQ : Q.IsTame)

/-- The lift `bf : bA → bB`, `[y, V, θ] ↦ [f(y), f(V), f(θ)]`, of an sc-smooth index-preserving
local homeomorphism `f` is sc-smooth (it covers `f`, `bMap_bLift`). -/
theorem isScSmoothMap_bLift {f : A → B} (hf : IsDLocalHomeo P.degIndex Q.degIndex f)
    (hfs : P.IsScSmoothMap Q f) :
    (P.tameBoundaryPolyfold hP).IsScSmoothMap (Q.tameBoundaryPolyfold hQ)
      (bLift (P.isCornerIndex_degIndex hP) (Q.isCornerIndex_degIndex hQ) hf) :=
  isScSmoothOn_of_bMap hP hQ hfs isOpen_univ (subset_univ _)
    (continuous_bLift _ _ hf).continuousOn fun p _ => bMap_bLift _ _ hf p

/-- A local inverse `σ` of `f` lifts `bf(c)` back to `c`. -/
theorem isLiftOf_bLift_sheet {f : A → B} (hf : P.IsLocalScDiffeo Q f) {W : Set A} {V : Set B}
    {σ : B → A} (hd : P.IsScDiffeoOn Q f σ W V) {c : P.TameBoundarySpace hP}
    (hc : bMap (P.isCornerIndex_degIndex hP) c ∈ W) :
    IsLiftOf (Q.isCornerIndex_degIndex hQ) (P.isCornerIndex_degIndex hP) σ
      (bLift (P.isCornerIndex_degIndex hP) (Q.isCornerIndex_degIndex hQ) hf.isDLocalHomeo c) c := by
  obtain ⟨q, hq⟩ := exists_isLiftOf (Q.isCornerIndex_degIndex hQ) (P.isCornerIndex_degIndex hP)
    hd.symm.isDHomeoOn
    (p := bLift (P.isCornerIndex_degIndex hP) (Q.isCornerIndex_degIndex hQ) hf.isDLocalHomeo c)
    (by rw [bMap_bLift]; exact hd.mapsTo hc)
  have h1 := (isLiftOf_bLift _ _ hf.isDLocalHomeo c).comp hq
  have : q = c := h1.unique (isLiftOf_id _ c)
    (eventuallyEq_of_mem (hd.isOpen_source.mem_nhds hc) fun φ hφ => hd.left_inv φ hφ)
  rwa [this] at hq

/-- **The lift `bf` of a local sc-diffeomorphism is a local sc-diffeomorphism**: over a sheet
`f : W → V` with inverse `σ`, `bf` maps `B⁻¹(W)` sc-diffeomorphically onto `B⁻¹(V)`, the inverse
covering `σ`. -/
theorem isLocalScDiffeo_bLift {f : A → B} (hf : P.IsLocalScDiffeo Q f) :
    (P.tameBoundaryPolyfold hP).IsLocalScDiffeo (Q.tameBoundaryPolyfold hQ)
      (bLift (P.isCornerIndex_degIndex hP) (Q.isCornerIndex_degIndex hQ) hf.isDLocalHomeo) := by
  intro a
  obtain ⟨W, V, σ, haW, hd⟩ := hf (bMap (P.isCornerIndex_degIndex hP) a)
  set g := bLift (P.isCornerIndex_degIndex hP) (Q.isCornerIndex_degIndex hQ) hf.isDLocalHomeo
    with hgdef
  set Wb := bMap (P.isCornerIndex_degIndex hP) ⁻¹' W with hWbdef
  set Vb := bMap (Q.isCornerIndex_degIndex hQ) ⁻¹' V with hVbdef
  have hWb : IsOpen Wb := hd.isOpen_source.preimage (continuous_bMap _)
  have hVb : IsOpen Vb := hd.isOpen_target.preimage (continuous_bMap _)
  have hinj : InjOn g Wb := by
    intro c hc c' hc' h
    have h1 := isLiftOf_bLift_sheet hP hQ hf hd hc
    have h2 := isLiftOf_bLift_sheet hP hQ hf hd hc'
    rw [← hgdef, h] at h1
    exact h1.unique h2 EventuallyEq.rfl
  have hsurj : ∀ p ∈ Vb, ∃ c ∈ Wb, g c = p := by
    intro p hp
    obtain ⟨q, hq⟩ := exists_isLiftOf (Q.isCornerIndex_degIndex hQ) (P.isCornerIndex_degIndex hP)
      hd.symm.isDHomeoOn (p := p) hp
    refine ⟨q, ?_, ?_⟩
    · change bMap _ q ∈ W
      rw [hq.bMap_eq]; exact hd.mapsTo_inv hp
    · exact (hq.comp (isLiftOf_bLift _ _ hf.isDLocalHomeo q)).unique (isLiftOf_id _ p)
        (eventuallyEq_of_mem (hd.isOpen_target.mem_nhds hp) fun y hy => hd.right_inv y hy)
  have : Nonempty (P.TameBoundarySpace hP) := ⟨a⟩
  set h := invFunOn g Wb with hhdef
  have hmaps : MapsTo g Wb Vb := fun c hc => by
    change bMap _ (g c) ∈ V
    rw [hgdef, bMap_bLift]; exact hd.mapsTo hc
  have hright : ∀ p ∈ Vb, g (h p) = p := fun p hp => invFunOn_eq (hsurj p hp)
  have hmem : ∀ p ∈ Vb, h p ∈ Wb := fun p hp => invFunOn_mem (hsurj p hp)
  have hleft : ∀ c ∈ Wb, h (g c) = c := fun c hc => hinj.leftInvOn_invFunOn hc
  have hcont : ContinuousOn h Vb := by
    rw [continuousOn_open_iff hVb]
    intro O hO
    have : Vb ∩ h ⁻¹' O = g '' (Wb ∩ O) := by
      ext p
      constructor
      · rintro ⟨hp, hpO⟩; exact ⟨h p, ⟨hmem p hp, hpO⟩, hright p hp⟩
      · rintro ⟨c, ⟨hc, hcO⟩, rfl⟩
        exact ⟨hmaps hc, by rw [mem_preimage, hleft c hc]; exact hcO⟩
    rw [this]
    exact isOpenMap_bLift _ _ _ _ (hWb.inter hO)
  have hhB : ∀ p ∈ Vb, bMap (P.isCornerIndex_degIndex hP) (h p) =
      σ (bMap (Q.isCornerIndex_degIndex hQ) p) := fun p hp => by
    conv_rhs => rw [← hright p hp]
    rw [hgdef, bMap_bLift, hd.left_inv _ (hmem p hp)]
  refine ⟨Wb, Vb, h, haW, ⟨?_, ?_, hmaps, hmem, hleft, hright⟩⟩
  · exact (isScSmoothMap_bLift hP hQ hf.isDLocalHomeo hf.isScSmoothMap).mono hWb (subset_univ _)
  · exact isScSmoothOn_of_bMap hQ hP hd.isScSmoothOn_inv hVb subset_rfl hcont hhB

end MPolyfold

namespace EpGroupoid

open TameBoundary MPolyfold

universe w

variable {Obj Mor : Type w} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

/-- `bX` is paracompact (metrizable, 2021 Proposition 2.7.16). -/
instance paracompactSpace_bObj (hX : X.IsTame) : ParacompactSpace (X.bObj hX) :=
  X.PObj.paracompactSpace_tameBoundarySpace hX

/-- `b𝐗` is paracompact (metrizable, 2021 Proposition 2.7.16). -/
instance paracompactSpace_bMor (hX : X.IsTame) : ParacompactSpace (X.bMor hX) :=
  X.PMor.paracompactSpace_tameBoundarySpace (X.isTame_PMor hX)

variable (X) in
/-- The tame M-polyfold structure of `bX` (2021 Theorem 2.7.13 (2) for the object M-polyfold). -/
abbrev bPObj (hX : X.IsTame) : MPolyfold (X.bObj hX) := X.PObj.tameBoundaryPolyfold hX

variable (X) in
/-- The tame M-polyfold structure of `b𝐗` (2021 Theorem 2.7.13 (2) for the morphism M-polyfold). -/
abbrev bPMor (hX : X.IsTame) : MPolyfold (X.bMor hX) :=
  X.PMor.tameBoundaryPolyfold (X.isTame_PMor hX)

/-- **2021 Theorem 7.6.9 (5)**: `s : b𝐗 → bX` of (7.25) is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_bSrc (hX : X.IsTame) :
    (X.bPMor hX).IsLocalScDiffeo (X.bPObj hX) (X.bSrc hX) :=
  isLocalScDiffeo_bLift (X.isTame_PMor hX) hX X.isLocalScDiffeo_src

/-- **2021 Theorem 7.6.9 (5)**: `t : b𝐗 → bX` of (7.25) is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_bTgt (hX : X.IsTame) :
    (X.bPMor hX).IsLocalScDiffeo (X.bPObj hX) (X.bTgt hX) :=
  isLocalScDiffeo_bLift (X.isTame_PMor hX) hX X.isLocalScDiffeo_tgt

/-- **2021 Theorem 7.6.9 (5)**: the unit map `u` of (7.28) is sc-smooth. -/
theorem isScSmoothMap_bUnit (hX : X.IsTame) :
    (X.bPObj hX).IsScSmoothMap (X.bPMor hX) (X.bUnit hX) :=
  isScSmoothMap_bLift hX (X.isTame_PMor hX) X.isDLocalHomeo_unit X.isScSmoothMap_unit

/-- **2021 Theorem 7.6.9 (5)**: the inversion `ι` of (7.27) is sc-smooth. -/
theorem isScSmoothMap_bInv (hX : X.IsTame) :
    (X.bPMor hX).IsScSmoothMap (X.bPMor hX) (X.bInv hX) :=
  isScSmoothMap_bLift (X.isTame_PMor hX) (X.isTame_PMor hX) X.isDLocalHomeo_inv
    X.isScSmoothMap_inv

/-- **2021 Theorem 7.6.9 (5)**, the multiplication `m` of (7.29), sheet form: for every sheet
`σ` of `s : b𝐗 → bX` over `V`, `b ↦ m(σ(t b), b)` is sc-smooth on `t⁻¹(V)`.  Near `b` it covers
`γ ↦ m(σ₁(t γ), γ)` for a sheet `σ₁` of `s : 𝐗 → X` through `B(σ(t b))`. -/
theorem isScSmoothCompSheet_bComp (hX : X.IsTame) :
    IsScSmoothCompSheet (X.bPObj hX) (X.bPMor hX) (X.bSrc hX) (X.bTgt hX) (X.bComp hX) := by
  intro σ W V hd
  refine isScSmoothOn_of_local' (hd.isOpen_target.preimage (continuous_bTgt hX)) fun b hb => ?_
  have hσc : ContinuousOn σ V := hd.isScSmoothOn_inv.continuousOn
  obtain ⟨W₁, V₁, σ₁, hW₁, hd₁⟩ :=
    X.isLocalScDiffeo_src (bMap (X.cornerMor hX) (σ (X.bTgt hX b)))
  have hc1 : ContinuousOn (fun b' => σ (X.bTgt hX b')) (X.bTgt hX ⁻¹' V) :=
    hσc.comp (continuous_bTgt hX).continuousOn fun _ h => h
  set N := X.bTgt hX ⁻¹' V ∩
    (fun b' => bMap (X.cornerMor hX) (σ (X.bTgt hX b'))) ⁻¹' W₁ with hNdef
  have hN : IsOpen N := ((continuous_bMap _).comp_continuousOn hc1).isOpen_inter_preimage
    (hd.isOpen_target.preimage (continuous_bTgt hX)) hd₁.isOpen_source
  refine ⟨N, ⟨hb, hW₁⟩, ?_⟩
  have hcomp : ∀ b' ∈ N, X.bSrc hX (σ (X.bTgt hX b')) = X.bTgt hX b' := fun b' hb' =>
    hd.right_inv _ hb'.1
  have hcont : ContinuousOn (fun b' => X.bComp hX (σ (X.bTgt hX b')) b') N := by
    have h1 : ContinuousOn (fun b' => (σ (X.bTgt hX b'), b')) N :=
      (hc1.mono inter_subset_left).prodMk continuousOn_id
    exact (continuousOn_bComp hX).comp h1 fun b' hb' => hcomp b' hb'
  have htgt : ∀ b' ∈ N, X.tgt (bMap (X.cornerMor hX) b') =
      X.src (bMap (X.cornerMor hX) (σ (X.bTgt hX b'))) := fun b' hb' => by
    rw [← bMap_bTgt hX, ← bMap_bSrc hX, hcomp b' hb']
  refine isScSmoothOn_of_bMap (X.isTame_PMor hX) (X.isTame_PMor hX)
    (X.isScSmoothCompSheet σ₁ W₁ V₁ hd₁) hN ?_ hcont ?_
  · intro b' hb'
    change X.tgt (bMap _ b') ∈ V₁
    rw [htgt b' hb']
    exact hd₁.mapsTo hb'.2
  · intro b' hb'
    rw [(bComp_spec hX (hcomp b' hb')).1, htgt b' hb', hd₁.left_inv _ hb'.2]

/-- **2021 Theorem 7.6.9 (5)**: `m` of (7.29) is sc-smooth on the fibred product
`b𝐗 ₛ×ₜ b𝐗` (condition (4) of 2021 Definition 7.1.3 (2017: Definition 7.3)). -/
theorem isScSmoothComp_bComp (hX : X.IsTame) :
    IsScSmoothComp (X.bPObj hX) (X.bPMor hX) (X.bSrc hX) (X.bTgt hX) (X.bComp hX)
      (isLocalScDiffeo_bSrc hX) (isLocalScDiffeo_bTgt hX).isScSmoothMap :=
  (isScSmoothComp_iff_sheet _ _).2 (isScSmoothCompSheet_bComp hX)

variable (X) in
/-- **2021 Theorem 7.6.9 (5), p. 355**: the boundary ep-groupoid `(bX, b𝐗)`, with the tame
M-polyfold structures of (2) and the structure maps `s, t, m, u, ι` of (7.25)–(7.29); it is an
ep-groupoid in the sense of 2021 Definition 7.1.3 (2017: Definition 7.3). -/
def boundaryEpGroupoid (hX : X.IsTame) : EpGroupoid (X.bObj hX) (X.bMor hX) where
  toGroupoidStr := X.boundaryGroupoid hX
  PObj := X.bPObj hX
  PMor := X.bPMor hX
  isLocalScDiffeo_src := isLocalScDiffeo_bSrc hX
  isLocalScDiffeo_tgt := isLocalScDiffeo_bTgt hX
  isScSmoothMap_unit := isScSmoothMap_bUnit hX
  isScSmoothMap_inv := isScSmoothMap_bInv hX
  exists_isProperMap := exists_isProperMap_bTgt hX
  isScSmoothComp := isScSmoothComp_bComp hX

/-- **2021 Theorem 7.6.9 (5)**: the boundary ep-groupoid is tame (2021 Definition 7.1.6 (2017:
Definition 7.6)). -/
theorem isTame_boundaryEpGroupoid (hX : X.IsTame) : (X.boundaryEpGroupoid hX).IsTame :=
  X.PObj.tameBoundaryPolyfold_isTame hX

variable (X) in
/-- **2021 Theorem 7.6.9 (3), (5)**: `B : (bX, b𝐗) → (X, 𝐗)` is a functor, sc-smooth on objects
and morphisms, i.e. a morphism of the category `EP` (2021 Definition 7.1.7 (2017: Definition
7.7)). -/
def boundaryEpFunctor (hX : X.IsTame) : EpFunctor (X.boundaryEpGroupoid hX) X where
  toGroupoidFunctor := X.boundaryFunctor hX
  isScSmoothMap_obj := X.PObj.tameBoundaryMap_isScSmooth hX
  isScSmoothMap_mor := X.PMor.tameBoundaryMap_isScSmooth (X.isTame_PMor hX)

/-- **The commutative diagram in the proof of 2021 Theorem 7.6.9, p. 355**: for a representative
`(φ, 𝐕, θ)` with `𝐕` inside a sheet `𝐖` of `s` (`s : 𝐖 → V` an sc-diffeomorphism), `s` maps
`U(φ, 𝐕, θ)` into `U(x, s(𝐕), s(θ))` and `Φ_{(x,s(𝐕),s(θ))} ∘ s = s ∘ Φ_{(φ,𝐕,θ)}` there. -/
theorem phiTot_bSrc (hX : X.IsTame) {W : Set Mor} {V : Set Obj} {σ : Obj → Mor}
    (hd : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) (t : BTriple (X.cornerMor hX))
    (ht : t.V ⊆ W) {p : X.bMor hX} (hp : p ∈ uSet _ t) :
    X.bSrc hX p ∈ uSet _ (t.map (X.cornerObj hX) hd.isDHomeoOn ht) ∧
      (X.PObj.phiTot hX (t.map (X.cornerObj hX) hd.isDHomeoOn ht) (X.bSrc hX p) : Obj) =
        X.src (X.PMor.phiTot (X.isTame_PMor hX) t p) := by
  obtain ⟨q', hq', hpq'⟩ := exists_isLiftOf_mem_uSet _ _ hd.isDHomeoOn ht hp
  have hq : X.bSrc hX p = q' := bLift_eq _ _ _ hpq'
  have hmem : X.bSrc hX p ∈ uSet _ (t.map (X.cornerObj hX) hd.isDHomeoOn ht) := hq ▸ hq'
  exact ⟨hmem, (congrArg Subtype.val (X.PObj.phiTot_of_mem hmem)).trans ((bMap_bSrc hX p).trans
    (congrArg X.src (congrArg Subtype.val (X.PMor.phiTot_of_mem hp)).symm))⟩

/-- **2021 Theorem 7.6.9, p. 355** (new in the 2021 edition), for a tame ep-groupoid `(X, 𝐗)`:
(1) `bX` and `b𝐗` are metrizable (the characterization of their topologies is
`theorem_7_6_9`); (2) `bX` and `b𝐗` carry the tame M-polyfold structures `bPObj`, `bPMor`,
characterized as in 2021 Theorem 2.7.13: every `U(x, V, θ)` is open and, for `V` centred at `x`,
`Φ_{(x,V,θ)}` is an sc-diffeomorphism onto the face `θ` with its natural structure, and every
structure with this property is equivalent to it; (3) both maps `B` are sc-smooth;
(4) `d_X(B(p)) − 1 = d_{bX}(p)` and `d_𝐗(B(a)) − 1 = d_{b𝐗}(a)`; (5) `(bX, b𝐗)` with
`s, t, u, ι, m` of (7.25)–(7.29) is the tame ep-groupoid `boundaryEpGroupoid`: `s, t` local
sc-diffeomorphisms, `u, ι` sc-smooth, `m` sc-smooth on `b𝐗 ₛ×ₜ b𝐗`; and `B` is an ep-functor.
The hypothesis of the two uniqueness statements is satisfied by `bPObj`, `bPMor` themselves (the
two conjuncts before them). -/
theorem theorem_7_6_9_full (hX : X.IsTame) :
    -- (1)
    TopologicalSpace.MetrizableSpace (X.bObj hX) ∧ TopologicalSpace.MetrizableSpace (X.bMor hX) ∧
      -- (2), tameness
      (X.bPObj hX).IsTame ∧ (X.bPMor hX).IsTame ∧
      -- (3)
      (X.bPObj hX).IsScSmoothMap X.PObj (X.PObj.tameBoundaryMap hX) ∧
      (X.bPMor hX).IsScSmoothMap X.PMor (X.PMor.tameBoundaryMap (X.isTame_PMor hX)) ∧
      -- (4)
      (∀ p, X.PObj.degIndex (X.PObj.tameBoundaryMap hX p) - 1 = (X.bPObj hX).degIndex p) ∧
      (∀ a, X.PMor.degIndex (X.PMor.tameBoundaryMap (X.isTame_PMor hX) a) - 1 =
        (X.bPMor hX).degIndex a) ∧
      -- (5), the tame ep-groupoid and its structure maps
      (X.boundaryEpGroupoid hX).IsTame ∧
      (X.boundaryEpGroupoid hX).toGroupoidStr = X.boundaryGroupoid hX ∧
      (X.boundaryEpGroupoid hX).PObj = X.bPObj hX ∧ (X.boundaryEpGroupoid hX).PMor = X.bPMor hX ∧
      (X.bPMor hX).IsLocalScDiffeo (X.bPObj hX) (X.bSrc hX) ∧
      (X.bPMor hX).IsLocalScDiffeo (X.bPObj hX) (X.bTgt hX) ∧
      (X.bPObj hX).IsScSmoothMap (X.bPMor hX) (X.bUnit hX) ∧
      (X.bPMor hX).IsScSmoothMap (X.bPMor hX) (X.bInv hX) ∧
      IsScSmoothComp (X.bPObj hX) (X.bPMor hX) (X.bSrc hX) (X.bTgt hX) (X.bComp hX)
        (isLocalScDiffeo_bSrc hX) (isLocalScDiffeo_bTgt hX).isScSmoothMap ∧
      -- `B` is an ep-functor
      (∃ F : EpFunctor (X.boundaryEpGroupoid hX) X,
        F.obj = X.PObj.tameBoundaryMap hX ∧ F.mor = X.PMor.tameBoundaryMap (X.isTame_PMor hX)) ∧
      -- (2), the characterization, for `bX` and for `b𝐗`
      (∀ (t : BTriple (X.cornerObj hX)) (ht : IsCenteredAt X.PObj.degIndex t.x t.V),
        IsOpen (uSet _ t) ∧
        letI := X.PObj.paracompactSpace_subtype t.θ
        (X.bPObj hX).IsScDiffeoOn (X.PObj.facePolyfold hX t.mem.1.1 t.mem_faces.1)
          (X.PObj.phiTot hX t) (fun y => ((phiHomeomorph _ ht).symm y : X.bObj hX))
          (uSet _ t) univ) ∧
      (∀ (t : BTriple (X.cornerMor hX)) (ht : IsCenteredAt X.PMor.degIndex t.x t.V),
        IsOpen (uSet _ t) ∧
        letI := X.PMor.paracompactSpace_subtype t.θ
        (X.bPMor hX).IsScDiffeoOn (X.PMor.facePolyfold (X.isTame_PMor hX) t.mem.1.1 t.mem_faces.1)
          (X.PMor.phiTot (X.isTame_PMor hX) t) (fun y => ((phiHomeomorph _ ht).symm y : X.bMor hX))
          (uSet _ t) univ) ∧
      -- (2), the uniqueness, for `bX` and for `b𝐗`
      (∀ Q' : MPolyfold (X.bObj hX),
        (∀ (t : BTriple (X.cornerObj hX)) (ht : IsCenteredAt X.PObj.degIndex t.x t.V),
          letI := X.PObj.paracompactSpace_subtype t.θ
          Q'.IsScDiffeoOn (X.PObj.facePolyfold hX t.mem.1.1 t.mem_faces.1) (X.PObj.phiTot hX t)
            (fun y => ((phiHomeomorph _ ht).symm y : X.bObj hX)) (uSet _ t) univ) →
        Q'.atlas.Equiv (X.bPObj hX).atlas) ∧
      ∀ Q' : MPolyfold (X.bMor hX),
        (∀ (t : BTriple (X.cornerMor hX)) (ht : IsCenteredAt X.PMor.degIndex t.x t.V),
          letI := X.PMor.paracompactSpace_subtype t.θ
          Q'.IsScDiffeoOn (X.PMor.facePolyfold (X.isTame_PMor hX) t.mem.1.1 t.mem_faces.1)
            (X.PMor.phiTot (X.isTame_PMor hX) t)
            (fun y => ((phiHomeomorph _ ht).symm y : X.bMor hX)) (uSet _ t) univ) →
        Q'.atlas.Equiv (X.bPMor hX).atlas := by
  obtain ⟨t₀, s₀, d₀, c₀, u₀⟩ := X.PObj.theorem_2_7_13_structure hX
  obtain ⟨t₁, s₁, d₁, c₁, u₁⟩ := X.PMor.theorem_2_7_13_structure (X.isTame_PMor hX)
  exact ⟨metrizableSpace_bObj hX, metrizableSpace_bMor hX, t₀, t₁, s₀, s₁, d₀, d₁,
    isTame_boundaryEpGroupoid hX, rfl, rfl, rfl, isLocalScDiffeo_bSrc hX,
    isLocalScDiffeo_bTgt hX, isScSmoothMap_bUnit hX, isScSmoothMap_bInv hX,
    isScSmoothComp_bComp hX, ⟨X.boundaryEpFunctor hX, rfl, rfl⟩, c₀, c₁, u₀, u₁⟩

/-! ### Witness -/

/-- **Witness** for `theorem_7_6_9_full` (its only hypothesis, tameness, is satisfied, and
its conclusions are not vacuous): the trivial ep-groupoid of the tame quadrant `[0, ∞)ⁿ ⊕ W`,
`n ≥ 1`, is tame; its boundary ep-groupoid is tame, with nonempty object and morphism sets, and
the classes over the corner `0` have degeneracy index `n − 1` in `bX`. -/
theorem trivial_quadrant_boundaryEp_witness (n : ℕ) (W : ScBanach) (hn : 1 ≤ n) :
    ∃ hX : (trivial (quadrantPolyfold n W)).IsTame,
      ((trivial (quadrantPolyfold n W)).boundaryEpGroupoid hX).IsTame ∧
      Nonempty ((trivial (quadrantPolyfold n W)).bObj hX) ∧
      Nonempty ((trivial (quadrantPolyfold n W)).bMor hX) ∧
      ∀ p : (trivial (quadrantPolyfold n W)).bObj hX,
        bMap ((trivial (quadrantPolyfold n W)).cornerObj hX) p = ⟨0, zero_mem_quadrant n W⟩ →
        ((trivial (quadrantPolyfold n W)).boundaryEpGroupoid hX).PObj.degIndex p = n - 1 :=
  ⟨isTame_trivial _ (quadrantPolyfold_isTame n W), isTame_boundaryEpGroupoid _,
    quadrantPolyfold_tameBoundarySpace_nonempty n W hn,
    quadrantPolyfold_tameBoundarySpace_nonempty n W hn,
    fun p hp => quadrantPolyfold_degIndex_tameBoundary n W p hp⟩

end EpGroupoid

end Polyfold
