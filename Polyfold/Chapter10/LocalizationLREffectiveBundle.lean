import Polyfold.Chapter10.LocalizationLRCounterexample
import Polyfold.Chapter10.StrongBundleWeakFibredProduct

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10: **Theorem 10.5.7** (§10.5, p. 508; 2017: Theorem 10.10) for an effective
target, the strong bundle analogue of `EPLoc.theorem_10_3_19_of_isEffective`.  Numbers and pages
are the 2021 text's.

# Generalized strong bundle isomorphisms over an effective base

## The text, paraphrased

(Theorem 10.5.7) For strong bundles with the local regularity property (Definition 8.4.2),
generalized strong bundle isomorphisms `[D], [D']` with `|[D]| = |[D']|` are equal.

As stated it does not hold as we read it (`LocalizationLRCounterexample.not_theorem_10_5_7`: the
base `ℤ/3 × ℝ ⇉ ℝ` acts trivially and is not effective).

## What is formalized

* `StrongBundle.isOpenMap_proj`: the projection `P : W → X` of a strong bundle is open (through
  `w`, `u ↦ Φ⁻¹(R(u, e))` is a local section of `P` in a strong bundle chart, `(u, e) = Φ(w)`).
* `SEP.orbitMap_base_eq`: `|Φ| = |Ψ|` on the total spaces gives `|ϕ| = |ψ|` on the bases.
* `SEP.natEquiv_of_isEffective`: for strong bundle equivalences `F, G : W'' → W'` with
  `|F| = |G|`, (LR) for the base of `W''` and an effective base of `W'`, `F ≃ G` (Definition
  10.4.8).  The base transformation `τ : ϕ_F → ϕ_G` is that of
  `EpFunctor.naturallyEquivalent_of_isEffective`; then `G(w) = μ'(τ(P(w)), F(w))`, since both sides
  are continuous in `w` and agree over the regular points (`G_{ϕ_F(P(w))} = {1}` leaves one
  morphism `ϕ_F(P(w)) → ϕ_G(P(w))`), which are dense (Proposition 7.8, `P` open).
* **`SBLocalization.theorem_10_5_7_of_isEffective`**: Theorem 10.5.7 with, in addition, the base
  of the target effective and (LR) (Definition 7.4.19) for the base of the source or of the
  target.  Proof: for `D : W ←Φ W'' →Ψ W'`, `D' : W ←Φ' V'' →Ψ' W'` the weak fibred product
  `W'' ×_W V''` of `Φ, Φ'` (`SBWeakFibredProduct`) with `ΠX, ΠZ` refines `D` and `D'`: `Φ ∘ ΠX ≃
  Φ' ∘ ΠZ` is Theorem 10.2.2 and `Ψ ∘ ΠX ≃ Ψ' ∘ ΠZ` is `SEP.natEquiv_of_isEffective`.
* `SBLocalization.theorem_10_5_7_of_isEffective_hypotheses`: the hypotheses can be met
  (`ℝⁿ × ℝᵏ → ℝⁿ` over the trivial ep-groupoid of `ℝⁿ`, with `[1_W]`).

## The extra hypothesis, and the choices made

* Effectiveness is asked of the **base** `X'` of the target, not of the ep-groupoid `(W', 𝐖')`:
  morphisms `(φ, w)` of `𝐖'` are morphisms of `𝐗'`, the natural transformations of Definition
  10.4.8 cover one of the bases, and the fibre identity above only needs `X'_reg` dense.
* (LR) of a base (Definition 7.4.19) is added.  The hypotheses of Theorem 10.5.7 (Definition
  8.4.2 for both bundles) are kept but not used: as formalized (`EpStrongBundle.IsLR`),
  Definition 8.4.2 speaks of strong bundle maps `Φ : W → W` defined on all of `W`, so it cannot
  be applied to the local maps `G ∘ F⁻¹` from which the families of Proposition 10.1.10 (1)
  would be built, and we do not derive (LR) of the base from it.  (LR) of the base is the
  hypothesis of Theorem 10.3.19, of which Theorem 10.5.7 is the strong bundle version.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v

/-! ### The projection of a strong bundle is open -/

section OpenProj

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- **The projection of a strong bundle is an open map**: in a strong bundle chart
`Φ : P⁻¹(V) → K = R(U ◁ F)` around `w`, with `Φ(w) = (u₀, e)`, the map `u ↦ Φ⁻¹(R(u, e))` is
continuous on `U`, passes through `w` at `u₀` and is a section of `P` over `O = r(U)`. -/
theorem StrongBundle.isOpenMap_proj (B : StrongBundle PX P) : IsOpenMap P := by
  intro N hN
  refine isOpen_iff_mem_nhds.2 ?_
  rintro _ ⟨w, hwN, rfl⟩
  obtain ⟨c, -, hw⟩ := B.atlas.cover w
  have hkK : c w ∈ c.R '' (c.U ×ˢ univ) := c.target_eq ▸ c.toPartialEquiv.map_source hw
  set r := c.isRetraction.baseRetraction c.relOpen
  have hO : r.retract = c.φ.model.O := c.base_retract
  set e := (c w).2
  let g : c.φ.model.E 0 → Y := fun u => c.toPartialEquiv.symm (c.R (u, e))
  have hgK : ∀ u ∈ c.U, c.R (u, e) ∈ c.toPartialEquiv.target := fun u hu => by
    rw [c.target_eq]; exact ⟨(u, e), ⟨hu, mem_univ _⟩, rfl⟩
  have hgc : ContinuousOn g c.U := by
    have hR : ContinuousOn c.R (c.U ×ˢ univ) :=
      (c.isRetraction.isScSmooth_zero 0).continuousOn_base
    refine c.continuousOn_invFun.comp
      (hR.comp (continuous_id.prodMk continuous_const).continuousOn
        fun u hu => ⟨hu, mem_univ _⟩) fun u hu => hgK u hu
  have hRu : ∀ u ∈ c.φ.model.O, (c.R (u, e)).1 = u := fun u hu => by
    have hu' : u ∈ r.retract := hO ▸ hu
    rw [c.isRetraction.apply_fst (r.retract_subset hu') e]
    exact r.apply_eq_self_of_mem_retract hu'
  have hPg : ∀ u ∈ c.φ.model.O, P (g u) = c.φ.toPartialEquiv.symm u := fun u hu => by
    have hu' : u ∈ c.U := r.retract_subset (hO ▸ hu : u ∈ r.retract)
    have hs : g u ∈ c.toPartialEquiv.source := c.toPartialEquiv.map_target (hgK u hu')
    have hPs : P (g u) ∈ c.φ.toPartialEquiv.source := by
      rw [c.source_eq] at hs; exact hs
    have h1 := c.covers _ hs
    rw [c.toPartialEquiv.right_inv (hgK u hu'), hRu u hu] at h1
    have h2 := c.φ.toPartialEquiv.left_inv hPs
    rw [← h1] at h2
    exact h2.symm
  obtain ⟨hk1, hk2⟩ := (c.isRetraction.mem_image_iff c.relOpen).1 hkK
  have hk1U : (c w).1 ∈ c.U := r.retract_subset hk1
  have hgw : g (c w).1 = w := by
    have hRk : c.R ((c w).1, e) = c w := by
      refine Prod.ext ?_ hk2
      rw [c.isRetraction.apply_fst hk1U e]
      exact r.apply_eq_self_of_mem_retract hk1
    change c.toPartialEquiv.symm (c.R ((c w).1, e)) = w
    rw [hRk, c.toPartialEquiv.left_inv hw]
  obtain ⟨M, hMo, hM⟩ := continuousOn_iff'.1 hgc N hN
  have hVo : IsOpen (c.φ.toPartialEquiv.source ∩ c.φ ⁻¹' M) :=
    c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source hMo
  have hPw : P w ∈ c.φ.toPartialEquiv.source := by
    have := hw; rw [c.source_eq] at this; exact this
  refine mem_nhds_iff.2 ⟨_, ?_, hVo, hPw, ?_⟩
  · rintro x ⟨hxs, hxM⟩
    have hxO : c.φ x ∈ c.φ.model.O := c.φ.target_eq ▸ c.φ.toPartialEquiv.map_source hxs
    have hxU : c.φ x ∈ c.U := r.retract_subset (hO ▸ hxO : c.φ x ∈ r.retract)
    have hgN : c.φ x ∈ g ⁻¹' N ∩ c.U := hM ▸ ⟨hxM, hxU⟩
    exact ⟨g (c.φ x), hgN.1, by rw [hPg _ hxO, c.φ.toPartialEquiv.left_inv hxs]⟩
  · have : (c w).1 ∈ M ∩ c.U := hM ▸ ⟨show g (c w).1 ∈ N by rw [hgw]; exact hwN, hk1U⟩
    change c.φ (P w) ∈ M
    rw [← c.covers w hw]
    exact this.1

end OpenProj

/-! ### Natural equivalence of strong bundle equivalences over an effective base -/

namespace SEP

open EpStrongBundle

variable {C A : SEP.{u}}

/-- `|Φ| = |Ψ| : |W''| → |W'|` implies `|ϕ| = |ψ| : |X''| → |X'|` for the covered functors
(`|P'| ∘ |Φ| = |ϕ| ∘ |P''|`, `P''` onto). -/
theorem orbitMap_base_eq {F G : C ⟶ A} (h : (Hom.Φ F).orbitMap = (Hom.Φ G).orbitMap) :
    (Hom.ϕ F).orbitMap = (Hom.ϕ G).orbitMap := by
  funext q
  induction q using Quotient.inductionOn with | h x => ?_
  obtain ⟨w, rfl⟩ := C.B.surjective x
  have hw := congrArg A.E.projFunctor.orbitMap (congrFun h (C.E.toEpGroupoid.π w))
  rw [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π,
    GroupoidFunctor.orbitMap_π] at hw
  change (Hom.ϕ F).orbitMap (C.X.π (C.P w)) = (Hom.ϕ G).orbitMap (C.X.π (C.P w))
  rw [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π,
    ← (Hom.isStrongBundleFunctor F).isStrongBundleMap_obj.covers,
    ← (Hom.isStrongBundleFunctor G).isStrongBundleMap_obj.covers]
  exact hw

/-- **Natural equivalence from equal orbit maps over an effective base** (the strong bundle
version of `EpFunctor.naturallyEquivalent_of_isEffective`): if `F, G : W'' → W'` are strong
bundle equivalences with `|F| = |G| : |W''| → |W'|`, the base `X''` of `W''` has (LR) and the base
`X'` of `W'` is effective, then `F ≃ G` (Definition 10.4.8), with `T(w) = (τ(P(w)), F(w))` for the
natural transformation `τ : ϕ_F → ϕ_G` of the bases. -/
theorem natEquiv_of_isEffective {F G : C ⟶ A} (hF : SEP.equivalences F)
    (hG : SEP.equivalences G) (hFG : (Hom.Φ F).orbitMap = (Hom.Φ G).orbitMap) (hC : C.X.IsLR)
    (hA : A.X.IsEffective) : SEP.NatEquiv F G := by
  obtain ⟨τ⟩ := EpFunctor.naturallyEquivalent_of_isEffective hF.isEquivalence_base
    hG.isEquivalence_base (orbitMap_base_eq hFG) hC hA
  have hsF := Hom.isStrongBundleFunctor F
  have hsG := Hom.isStrongBundleFunctor G
  have hmem : ∀ w, (τ.app (C.P w), (Hom.Φ F).obj w) ∈ pullbackSpace A.P A.X.src := fun w => by
    change A.P _ = A.X.src _
    rw [τ.src_app, hsF.isStrongBundleMap_obj.covers]
  -- `G(w) = μ'(τ(P(w)), F(w))`: a closed condition holding on the dense set over `X'_reg`
  have hobj : ∀ w, (Hom.Φ G).obj w = A.E.μ ⟨_, hmem w⟩ := by
    have hτc : Continuous τ.app := continuousOn_univ.1 τ.isScSmoothMap_app.continuousOn
    have hc1 : Continuous fun w => A.E.μ ⟨_, hmem w⟩ :=
      A.E.continuous_μ.comp (((hτc.comp C.B.continuous).prodMk
        hsF.isStrongBundleMap_obj.continuous).subtype_mk _)
    have hcl : IsClosed {w | (Hom.Φ G).obj w = A.E.μ ⟨_, hmem w⟩} :=
      isClosed_eq hsG.isStrongBundleMap_obj.continuous hc1
    have hdense : Dense (C.P ⁻¹' ((Hom.ϕ F).obj ⁻¹' A.X.regularSet)) :=
      ((A.X.proposition_7_8 hA).2.preimage
        hF.isEquivalence_base.isLocalScDiffeo_obj.isOpenMap).preimage C.B.isOpenMap_proj
    have hsub : C.P ⁻¹' ((Hom.ϕ F).obj ⁻¹' A.X.regularSet) ⊆
        {w | (Hom.Φ G).obj w = A.E.μ ⟨_, hmem w⟩} := by
      intro w hw
      have hπ : A.E.toEpGroupoid.π ((Hom.Φ F).obj w) = A.E.toEpGroupoid.π ((Hom.Φ G).obj w) := by
        rw [← GroupoidFunctor.orbitMap_π, ← GroupoidFunctor.orbitMap_π]
        exact congrFun hFG _
      obtain ⟨m, hms, hmt⟩ := (GroupoidStr.π_eq_π_iff _).1 hπ
      have hms' : (m : A.Mor × A.W).2 = (Hom.Φ F).obj w := hms
      have hmt' : A.E.μ m = (Hom.Φ G).obj w := hmt
      -- `m.1` and `τ(P(w))` are morphisms `ϕ_F(P(w)) → ϕ_G(P(w))`, with `ϕ_F(P(w))` regular
      have hsa : A.X.src (m : A.Mor × A.W).1 = (Hom.ϕ F).obj (C.P w) := by
        rw [← m.2, hms', hsF.isStrongBundleMap_obj.covers]
      have hta : A.X.tgt (m : A.Mor × A.W).1 = (Hom.ϕ G).obj (C.P w) := by
        rw [← A.E.P_μ, hmt', hsG.isStrongBundleMap_obj.covers]
      have hc : A.X.src (A.X.inv (τ.app (C.P w))) = A.X.tgt (m : A.Mor × A.W).1 := by
        rw [A.X.src_inv, τ.tgt_app, hta]
      have hk := hw ⟨A.X.comp (A.X.inv (τ.app (C.P w))) (m : A.Mor × A.W).1,
        by rw [A.X.src_comp _ _ hc, hsa], by rw [A.X.tgt_comp _ _ hc, A.X.tgt_inv, τ.src_app]⟩
      have hk' := congrArg GroupoidStr.Isotropy.val hk
      change A.X.comp (A.X.inv (τ.app (C.P w))) (m : A.Mor × A.W).1 =
        A.X.unit ((Hom.ϕ F).obj (C.P w)) at hk'
      have heq := GroupoidStr.eq_inv_of_comp_eq_unit' (G := A.X.toGroupoidStr) hc
        (hk'.trans (by rw [A.X.tgt_inv, τ.src_app]))
      rw [GroupoidStr.inv_inv] at heq
      change (Hom.Φ G).obj w = A.E.μ ⟨_, hmem w⟩
      rw [← hmt']
      exact A.E.μ_congr (Prod.ext heq hms')
    have h := hcl.closure_subset_iff.2 hsub
    rw [hdense.closure_eq] at h
    exact fun w => h (mem_univ w)
  refine ⟨⟨fun w => ⟨_, hmem w⟩, fun _ => rfl, fun w => (hobj w).symm, fun q => ?_, τ,
    fun _ => rfl⟩⟩
  have hL : (Hom.Φ F).obj (C.E.μ q) = A.E.μ ((Hom.Φ F).mor q) := ((Hom.Φ F).tgt_mor q).symm
  have hR : ((Hom.Φ G).mor q : A.Mor × A.W).2 = A.E.μ ⟨_, hmem (q : C.Mor × C.W).2⟩ :=
    ((Hom.Φ G).src_mor q).trans (hobj _)
  have e₁ := A.E.morComp_val (q' := ⟨_, hmem (C.E.μ q)⟩) (q := (Hom.Φ F).mor q) hL
  have e₂ := A.E.morComp_val (q' := (Hom.Φ G).mor q) (q := ⟨_, hmem (q : C.Mor × C.W).2⟩) hR
  refine Subtype.ext (e₁.trans (Eq.trans ?_ e₂.symm))
  have hq : C.P (q : C.Mor × C.W).2 = C.X.src (q : C.Mor × C.W).1 := q.2
  rw [hsF.mor_val, hsG.mor_val]
  change (A.X.comp (τ.app (C.P (C.E.μ q))) ((Hom.ϕ F).mor (q : C.Mor × C.W).1),
      (Hom.Φ F).obj (q : C.Mor × C.W).2) =
    (A.X.comp ((Hom.ϕ G).mor (q : C.Mor × C.W).1) (τ.app (C.P (q : C.Mor × C.W).2)),
      (Hom.Φ F).obj (q : C.Mor × C.W).2)
  rw [C.E.P_μ, hq]
  exact Prod.ext (τ.naturality _) rfl

end SEP

/-! ### Theorem 10.5.7 for an effective base -/

namespace SBLocalization

open SEP

/-- **2021 Theorem 10.5.7, p. 508 (2017: Theorem 10.10), for an effective base** (the strong
bundle version of `EPLoc.theorem_10_3_19_of_isEffective`): if the strong bundles have the local
regularity property (Definition 8.4.2, kept from the text, not used), the base of one of them has
(LR) (Definition 7.4.19) and the base `X'` of the target is effective, generalized strong bundle
isomorphisms `[D], [D'] : W → W'` with `|[D]| = |[D']|` are equal. -/
theorem theorem_10_5_7_of_isEffective {A A' : SEP.{u}} (_hA : A.E.IsLR) (_hA' : A'.E.IsLR)
    (hLR : A.X.IsLR ∨ A'.X.IsLR) (hEff : A'.X.IsEffective) {f f' : GenSBMap A A'}
    (hf : f.IsGeneralizedIso) (hf' : f'.IsGeneralizedIso) (h : f.orbitMap = f'.orbitMap) :
    f = f' := by
  obtain ⟨D, rfl, hΨ⟩ := hf
  obtain ⟨D', rfl, hΨ'⟩ := hf'
  have h' : D.orbitMap = D'.orbitMap := h
  -- the weak fibred product `W'' ×_W V''` of `Φ` and `Φ'`
  obtain ⟨hZ, hnat, -, -⟩ := SBWeakFibredProduct.theorem_10_2_2 D.isEquivalence_Φ D'.Φ
  have hX := SBWeakFibredProduct.theorem_10_2_2_right D.isEquivalence_Φ D'.Φ D'.isEquivalence_Φ
  set pX := SBWeakFibredProduct.projX D.isEquivalence_Φ D'.Φ
  set pZ := SBWeakFibredProduct.projZ D.isEquivalence_Φ D'.Φ
  have hXΦ := SEP.equivalences.comp_mem _ _ hX D.isEquivalence_Φ
  have hXΨ := SEP.equivalences.comp_mem _ _ hX hΨ
  have hZΨ := SEP.equivalences.comp_mem _ _ hZ hΨ'
  have hCLR : (SBWeakFibredProduct.wfpSEP D.isEquivalence_Φ D'.Φ).X.IsLR :=
    hLR.elim (fun hL => (EpFunctor.proposition_10_1_9 hXΦ.isEquivalence_base).2 hL)
      (fun hL => (EpFunctor.proposition_10_1_9 hXΨ.isEquivalence_base).2 hL)
  have horb : (Hom.Φ (pX ≫ D.Ψ)).orbitMap = (Hom.Φ (pZ ≫ D'.Ψ)).orbitMap := by
    funext q
    induction q using Quotient.inductionOn with | h w => ?_
    have h₁ := congrFun hnat.orbitMap_eq ((SBWeakFibredProduct.wfpSEP D.isEquivalence_Φ
      D'.Φ).E.toEpGroupoid.π w)
    change (Hom.Φ D.Ψ).orbitMap ((Hom.Φ pX).orbitMap (GroupoidStr.π _ w)) =
      (Hom.Φ D'.Ψ).orbitMap ((Hom.Φ pZ).orbitMap (GroupoidStr.π _ w))
    change (Hom.Φ D.Φ).orbitMap ((Hom.Φ pX).orbitMap (GroupoidStr.π _ w)) =
      (Hom.Φ D'.Φ).orbitMap ((Hom.Φ pZ).orbitMap (GroupoidStr.π _ w)) at h₁
    rw [← D.orbitMap_orbitMap_Φ, ← D'.orbitMap_orbitMap_Φ, h₁, h']
  have key := SEP.natEquiv_of_isEffective hXΨ hZΨ horb hCLR hEff
  exact SDiagram.cls_eq_cls_of_equiv ⟨D.precomp pX hX, D.isRefinement_precomp pX hX,
    ⟨pZ, hZ, hnat.symm, key.symm⟩⟩

end SBLocalization

/-! ### Witness -/

namespace LocalizationLREffectiveBundleExamples

open StrongBundleEquivalenceExamples SBLocalization

/-- A trivial ep-groupoid (all morphisms units) has (LR): its orbits are points, so an
orbit-preserving `β` is the identity, the action of `1`. -/
theorem isLR_trivial {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z]
    (PZ : MPolyfold Z) : (EpGroupoid.trivial PZ).IsLR := by
  intro x O hO hxO
  obtain ⟨R, hRO⟩ := (EpGroupoid.trivial PZ).theorem_7_1 x hO hxO
  refine ⟨R, hRO, fun β β' _ hπ => ⟨1, fun y hy => ?_⟩⟩
  obtain ⟨φ, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 (hπ y hy)
  rw [R.Φ_one y hy]
  exact h1.symm.trans h2

/-- **Witness** for `SBLocalization.theorem_10_5_7_of_isEffective`: for `W = ℝⁿ × ℝᵏ → ℝⁿ` over
the trivial ep-groupoid of `ℝⁿ` (`epSEP n k`), the bundle has the local regularity property
(Definition 8.4.2), the base has (LR) and is effective, and `[1_W]` is a generalized strong bundle
isomorphism. -/
theorem theorem_10_5_7_of_isEffective_hypotheses (n k : ℕ) :
    (epSEP n k).E.IsLR ∧ (epSEP n k).X.IsLR ∧ (epSEP n k).X.IsEffective ∧
      (SDiagram.id (epSEP n k)).cls.IsGeneralizedIso :=
  ⟨EpStrongBundle.isLR_trivial _, isLR_trivial _, EpGroupoid.isEffective_trivial _,
    ⟨SDiagram.id _, rfl, SEP.equivalences.id_mem _⟩⟩

end LocalizationLREffectiveBundleExamples

end Polyfold
