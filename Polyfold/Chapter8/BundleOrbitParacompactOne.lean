import Polyfold.Chapter8.BundleOrbitParacompact2021
import Polyfold.Chapter8.TangentLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 8,
§8.4, **Proposition 8.4.1** (p. 380, new in the 2021 edition), statement (3).

# `|X|` is paracompact iff `|W[1]|` is

## The text, paraphrased

(Proposition 8.4.1) For a strong bundle `(P : W → X, μ)` over an ep-groupoid, `|X|`, `|W[0]|`
and `|W[1]|` are paracompact together.  `W[1]` is the ep-groupoid with object M-polyfold `W[1]`
(the points `W_{0,1}`, with the M-polyfold structure of Part I) and morphisms `𝐗 ₛ×_P W[1]`; the
zero section is a closed embedding `|X| → |W[1]|`, and (1) ⇒ (3) is proved as (1) ⇒ (2).

## What is formalized

* `EpStrongBundle.OrbitSpaceOne` (**the orbit space `|W[1]|`**): the quotient of the M-polyfold
  `W[1]` (`StrongBundle.One` with the topology of `toMPolyfold1`) by the relation "there is a
  morphism `(φ, w) ∈ 𝐗 ₛ×_P W[1]` from `w` to `w'`", i.e. `μ(φ, w) = w'`
  (`πOne_eq_πOne_iff`), with the quotient topology.  This is the orbit space of the groupoid
  `(W[1], 𝐗 ₛ×_P W[1])`; its ep-groupoid structure is not needed for the statement.
* `EpStrongBundle.isOpenMap_πOne` (Proposition 7.1.8 for `W[1]`), `continuous_μOne` (the
  structure map at level one, `b ↦ μ(a(b), b)`, is continuous for `a` sc-smooth), the action of
  `G_x` on `W[1]|U(x)` by homeomorphisms (`bundleOneMulAction`, `continuous_bundleOneSmul`),
  `isOpenEmbedding_bundleOneOrbitQuotientMap` (`G_x\(W[1]|U(x)) → |W[1]|`).
* `EpStrongBundle.metrizableSpace_orbitSpaceOne`: if `|X|` is paracompact, `|W[1]|` is
  metrizable.
* `EpStrongBundle.zeroOrbitMapOne` (`|0| : |X| → |W[1]|`) and `isClosedEmbedding_zeroOrbitMapOne`.
* **`EpStrongBundle.proposition_8_4_1_one_iff_three`** ((1) ⇔ (3)) and **`proposition_8_4_1`**
  (the three statements are equivalent, `List.TFAE`).  No hypothesis beyond the text's.

## The proof, and how it relates to the text's

(1) ⇒ (3) as in `BundleOrbitParacompact2021.lean`: `|X|` is metrizable, and Smirnov's theorem
pulled back along `|P[1]| : |W[1]| → |X|` applies, since `|P[1]|⁻¹(|U(x)|) ≅ G_x\(W[1]|U(x))`
is metrizable (`W[1]` is metrizable, `G_x` finite acting by homeomorphisms).  The continuity of
the action at level one comes from the sc-smoothness of `μ : 𝐗 ₛ×_P W[1] → W[1]` (part of "strong
bundle map") and the universal property of the pull-back at level one.  (3) ⇒ (1) is the text's:
the zero section is an sc⁺-section, so `|0| : |X| → |W[1]|` is continuous with continuous left
inverse `|P[1]|`, and its image (the classes of zero vectors) is closed.
-/

open Set Function Topology TopologicalSpace Filter

noncomputable section

namespace Polyfold

universe u

section Prop841Three

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B)

namespace EpStrongBundle

/-! ### The structure map at level one -/

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- `μ` maps `𝐗 ₛ×_P W_{0,1}` into `W_{0,1}`. -/
theorem μ_mem_oneSet {q : pullbackSpace P X.src} (hq : (q : Mor × W).2 ∈ B.oneSet) :
    E.μ q ∈ B.oneSet := by
  have := B.paracompactSpace_pullback X.PMor X.src
  exact E.isStrongBundleMap.mapsTo_oneSet ((B.mem_oneSet_pullback_iff X.isScSmoothMap_src _).2 hq)

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- `μ(a(b), b)` as a point of `W[1]`, for `b ∈ W[1]` and `s(a(b)) = P(b)`. -/
def μOne (φ : Mor) (b : B.One) (h : P (B.oneVal b) = X.src φ) : B.One :=
  B.oneMk (E.μ ⟨(φ, B.oneVal b), h⟩) (E.μ_mem_oneSet (B.oneVal_mem b))

omit [ParacompactSpace (pullbackSpace P X.src)] in
@[simp] lemma oneVal_μOne (φ : Mor) (b : B.One) (h : P (B.oneVal b) = X.src φ) :
    B.oneVal (E.μOne φ b h) = E.μ ⟨(φ, B.oneVal b), h⟩ := rfl

/-- **`μ` is continuous at level one**: for `a : W[1] → 𝐗` sc-smooth on an open `O` with
`s(a(b)) = P(b)`, `b ↦ μ(a(b), b) : O → W[1]` is continuous (`μ : 𝐗 ₛ×_P W[1] → W[1]` is
sc-smooth, and so is `b ↦ (a(b), b) : O → 𝐗 ₛ×_P W[1]` by the universal property of the
pull-back at level one). -/
theorem continuous_μOne {O : Set B.One} (hO : IsOpen O) {a : B.One → Mor}
    (ha : B.toMPolyfold1.IsScSmoothOn X.PMor a O) (has : ∀ b ∈ O, P (B.oneVal b) = X.src (a b)) :
    Continuous fun b : O => E.μOne (a b) b (has b b.2) := by
  rcases isEmpty_or_nonempty O with hO' | hO'
  · exact continuous_of_discreteTopology
  have := B.metrizableSpace_one
  have : ParacompactSpace O := paracompactSpace_of_metrizableSpace O
  have hf := X.isScSmoothMap_src
  let ι : O → (B.pullback hf).One := fun b =>
    (B.pullback hf).oneMk ⟨(a b, B.oneVal b), has b b.2⟩
      ((B.mem_oneSet_pullback_iff hf _).2 (B.oneVal_mem b))
  have hι : (B.toMPolyfold1.restrictOpen hO).IsScSmoothMap (B.pullback hf).toMPolyfold1 ι := by
    refine B.isScSmoothMap_to_pullback_one hf ?_ ?_
    · exact (ha.comp (MPolyfold.isScSmoothMap_subtypeVal hO) fun b _ => b.2).congr
        fun _ _ => rfl
    · exact (MPolyfold.isScSmoothMap_subtypeVal hO).congr fun _ _ => rfl
  have hμ := E.isStrongBundleMap.isScSmoothMap_one
  exact continuousOn_univ.1 (hμ.comp hι).continuousOn

/-! ### The orbit space `|W[1]|` -/

/-- The orbit relation of `W[1]`: `b ≃ b'` iff there is a morphism `(φ, b) ∈ 𝐗 ₛ×_P W[1]` with
`μ(φ, b) = b'` (the morphisms of `W` between points of `W_{0,1}`). -/
def orbitSetoidOne : Setoid B.One := Setoid.comap B.oneVal E.toEpGroupoid.orbitSetoid

/-- **The orbit space `|W[1]|`** of the ep-groupoid `W[1]` (§8.4, p. 380), with the quotient
topology of the M-polyfold `W[1]`. -/
def OrbitSpaceOne : Type u := Quotient E.orbitSetoidOne

instance : TopologicalSpace E.OrbitSpaceOne :=
  inferInstanceAs (TopologicalSpace (Quotient E.orbitSetoidOne))

/-- The quotient map `W[1] → |W[1]|`. -/
def πOne (b : B.One) : E.OrbitSpaceOne := Quotient.mk E.orbitSetoidOne b

theorem continuous_πOne : Continuous E.πOne := continuous_quot_mk

theorem isQuotientMap_πOne : IsQuotientMap E.πOne := isQuotientMap_quotient_mk'

theorem surjective_πOne : Surjective E.πOne := Quotient.mk_surjective

/-- `|b| = |b'|` in `|W[1]|` iff `μ(φ, b) = b'` for some `φ` with `s(φ) = P(b)`. -/
theorem πOne_eq_πOne_iff {b b' : B.One} :
    E.πOne b = E.πOne b' ↔
      ∃ (φ : Mor) (h : P (B.oneVal b) = X.src φ), E.μ ⟨(φ, B.oneVal b), h⟩ = B.oneVal b' := by
  change Quotient.mk _ b = Quotient.mk _ b' ↔ _
  rw [Quotient.eq]
  change E.toEpGroupoid.Isomorphic (B.oneVal b) (B.oneVal b') ↔ _
  constructor
  · rintro ⟨⟨⟨φ, w⟩, hq⟩, hs, ht⟩
    change w = B.oneVal b at hs
    subst hs
    exact ⟨φ, hq, ht⟩
  · rintro ⟨φ, h, hμ⟩
    exact ⟨⟨(φ, B.oneVal b), h⟩, rfl, hμ⟩

theorem πOne_eq_πOne_iff_π {b b' : B.One} :
    E.πOne b = E.πOne b' ↔ E.toEpGroupoid.π (B.oneVal b) = E.toEpGroupoid.π (B.oneVal b') :=
  Quotient.eq.trans (Quotient.eq (r := E.toEpGroupoid.orbitSetoid)).symm

/-- The continuous map `|W[1]| → |W|` induced by the inclusion `W[1] → W`. -/
def inclOrbitMapOne : E.OrbitSpaceOne → E.toEpGroupoid.OrbitSpace :=
  Quotient.lift (fun b => E.toEpGroupoid.π (B.oneVal b)) fun _ _ h =>
    (E.πOne_eq_πOne_iff_π).1 (Quotient.sound h)

theorem continuous_inclOrbitMapOne : Continuous E.inclOrbitMapOne :=
  continuous_quot_lift _ (E.toEpGroupoid.continuous_π.comp B.continuous_oneVal)

/-- **`|P[1]| : |W[1]| → |X|`**, continuous. -/
def projOrbitMapOne : E.OrbitSpaceOne → X.OrbitSpace :=
  E.projFunctor.orbitMap ∘ E.inclOrbitMapOne

theorem continuous_projOrbitMapOne : Continuous E.projOrbitMapOne :=
  E.continuous_orbitMap_projFunctor.comp E.continuous_inclOrbitMapOne

theorem projOrbitMapOne_πOne (b : B.One) : E.projOrbitMapOne (E.πOne b) = X.π (P (B.oneVal b)) :=
  rfl

/-- **Proposition 7.1.8 for `W[1]`: `W[1] → |W[1]|` is open.**  For `b ≃ a` with `a` in an open
`V`, say `μ(φ₀, b) = a`, take a local inverse `σ` of `s` near `φ₀`; then `b' ↦ μ(σ(P b'), b')`
is continuous near `b` (`continuous_μOne`), sends `b` to `a`, and each `b'` to a point of its
orbit, so a neighbourhood of `b` lies in the saturation of `V`. -/
theorem isOpenMap_πOne : IsOpenMap E.πOne := by
  intro V hV
  rw [← E.isQuotientMap_πOne.isOpen_preimage]
  refine isOpen_iff_mem_nhds.2 fun b hb => ?_
  obtain ⟨a, haV, hab⟩ := hb
  obtain ⟨φ₀, h₀, hμ₀⟩ := (E.πOne_eq_πOne_iff).1 hab.symm
  obtain ⟨U', V', σ, hφ₀, hd⟩ := X.isLocalScDiffeo_src φ₀
  have hP1 := B.isScSmoothMap_proj1
  set O : Set B.One := (P ∘ B.oneVal) ⁻¹' V' with hOdef
  have hO : IsOpen O := hd.isScSmoothOn_inv.isOpen.preimage
    (continuousOn_univ.1 hP1.continuousOn)
  have ha : B.toMPolyfold1.IsScSmoothOn X.PMor (σ ∘ P ∘ B.oneVal) O :=
    hd.isScSmoothOn_inv.comp (hP1.mono hO (subset_univ _)) fun b hb => hb
  have has : ∀ b ∈ O, P (B.oneVal b) = X.src ((σ ∘ P ∘ B.oneVal) b) := fun b hb =>
    (hd.right_inv _ hb).symm
  have hc := E.continuous_μOne hO ha has
  have hbO : b ∈ O := by
    change P (B.oneVal b) ∈ V'
    rw [h₀]; exact hd.mapsTo hφ₀
  have hσb : σ (P (B.oneVal b)) = φ₀ := by rw [h₀]; exact hd.left_inv _ hφ₀
  have hFb : E.μOne ((σ ∘ P ∘ B.oneVal) b) b (has b hbO) = a := by
    refine B.oneVal_injective ?_
    rw [oneVal_μOne, ← hμ₀]
    exact E.μ_congr (by simp only [Function.comp_apply, hσb])
  have hN : IsOpen (Subtype.val '' ((fun b : O => E.μOne ((σ ∘ P ∘ B.oneVal) b) b
      (has b b.2)) ⁻¹' V)) := hO.isOpenMap_subtype_val _ (hV.preimage hc)
  refine mem_of_superset (hN.mem_nhds ⟨⟨b, hbO⟩, by
    change E.μOne ((σ ∘ P ∘ B.oneVal) b) b (has b hbO) ∈ V
    rw [hFb]; exact haV, rfl⟩) ?_
  rintro _ ⟨b', hb', rfl⟩
  exact ⟨_, hb', ((E.πOne_eq_πOne_iff).2 ⟨_, has b'.1 b'.2, rfl⟩).symm⟩

/-! ### The action of `G_x` on `W[1]|U(x)` -/

variable {x : Obj} (R : X.NaturalRep x)

/-- **`W[1]|U(x) = P[1]⁻¹(U(x))`.** -/
def bundleOneU : Set B.One := B.oneVal ⁻¹' E.bundleU R

theorem isOpen_bundleOneU : IsOpen (E.bundleOneU R) :=
  (E.isOpen_bundleU R).preimage B.continuous_oneVal

omit [ParacompactSpace (pullbackSpace P X.src)] in
theorem natLift_mem_oneSet (g : X.Isotropy x) (b : B.One) (hb : P (B.oneVal b) ∈ R.U) :
    E.natLift R g (B.oneVal b) hb ∈ B.oneSet :=
  E.μ_mem_oneSet (B.oneVal_mem b)

/-- `g ∗ b` on `W[1]|U(x)`. -/
def bundleOneSmul (g : X.Isotropy x) (b : E.bundleOneU R) : E.bundleOneU R :=
  ⟨B.oneMk (E.natLift R g (B.oneVal b.1) b.2) (E.natLift_mem_oneSet R g b.1 b.2),
    E.natLift_mem R g _ b.2⟩

/-- **The lifted action of `G_x` on `W[1]|U(x)`**, `g ∗ b = μ(Γ(g, P b), b)`. -/
instance bundleOneMulAction : MulAction (X.Isotropy x) (E.bundleOneU R) where
  smul := E.bundleOneSmul R
  one_smul b := Subtype.ext (B.oneVal_injective (E.natLift_one R _ b.2))
  mul_smul g h b := Subtype.ext (B.oneVal_injective (E.natLift_mul R g h _ b.2))

@[simp] theorem oneVal_bundleOneSmul (g : X.Isotropy x) (b : E.bundleOneU R) :
    B.oneVal (g • b : E.bundleOneU R).1 = E.natLift R g (B.oneVal b.1) b.2 := rfl

/-- `G_x` acts on `W[1]|U(x)` by homeomorphisms (`continuous_μOne` with `a = Γ(g, P(·))`). -/
theorem continuous_bundleOneSmul (g : X.Isotropy x) :
    Continuous fun b : E.bundleOneU R => g • b := by
  have hO := E.isOpen_bundleOneU R
  have ha : B.toMPolyfold1.IsScSmoothOn X.PMor (fun b => R.Γ g (P (B.oneVal b)))
      (E.bundleOneU R) :=
    (R.isScSmoothOn_Γ g).comp (B.isScSmoothMap_proj1.mono hO (subset_univ _)) fun b hb => hb
  have has : ∀ b ∈ E.bundleOneU R, P (B.oneVal b) = X.src (R.Γ g (P (B.oneVal b))) :=
    fun b hb => (R.src_Γ g _ hb).symm
  exact (E.continuous_μOne hO ha has).subtype_mk _

/-- Two points of `W[1]|U(x)` have the same class in `|W[1]|` iff they are `G_x`-related. -/
theorem πOne_eq_πOne_iff_exists_smul {v w : E.bundleOneU R} :
    E.πOne v.1 = E.πOne w.1 ↔ ∃ g : X.Isotropy x, g • v = w := by
  rw [E.πOne_eq_πOne_iff_π]
  have := E.π_eq_π_iff_exists_smul R (v := ⟨B.oneVal v.1, v.2⟩) (w := ⟨B.oneVal w.1, w.2⟩)
  refine this.trans (exists_congr fun g => ?_)
  constructor
  · intro h
    have h0 := congrArg Subtype.val h
    have h' : B.oneVal (g • v).1 = B.oneVal w.1 := h0
    exact Subtype.ext (B.oneVal_injective h')
  · intro h
    exact Subtype.ext (by rw [bundleSmul_val, ← h]; rfl)

private theorem bundleOneOrbitRel_iff (v w : E.bundleOneU R) :
    MulAction.orbitRel (X.Isotropy x) (E.bundleOneU R) v w ↔ E.πOne v.1 = E.πOne w.1 := by
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, eq_comm, E.πOne_eq_πOne_iff_exists_smul]

/-- `G_x\(W[1]|U(x)) → |W[1]|`, `G_x ∗ b ↦ |b|`. -/
def bundleOneOrbitQuotientMap :
    MulAction.orbitRel.Quotient (X.Isotropy x) (E.bundleOneU R) → E.OrbitSpaceOne :=
  Quotient.lift (fun v : E.bundleOneU R => E.πOne v.1) fun v w h =>
    (E.bundleOneOrbitRel_iff R v w).1 h

/-- **`G_x\(W[1]|U(x)) → |W[1]|` is an open embedding.** -/
theorem isOpenEmbedding_bundleOneOrbitQuotientMap :
    IsOpenEmbedding (E.bundleOneOrbitQuotientMap R) := by
  refine .of_continuous_injective_isOpenMap
    ((E.continuous_πOne.comp continuous_subtype_val).quotient_lift _)
    (fun q q' h => ?_) fun S hS => ?_
  · induction q using Quotient.inductionOn with | h v => ?_
    induction q' using Quotient.inductionOn with | h w => ?_
    exact Quotient.sound ((E.bundleOneOrbitRel_iff R v w).2 h)
  · have himage : E.bundleOneOrbitQuotientMap R '' S =
        E.πOne '' (Subtype.val '' (Quotient.mk _ ⁻¹' S)) := by
      ext c
      constructor
      · rintro ⟨q, hq, rfl⟩
        induction q using Quotient.inductionOn with | h v => ?_
        exact ⟨v, ⟨v, hq, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨Quotient.mk _ v, hv, rfl⟩
    rw [himage]
    exact E.isOpenMap_πOne _ ((E.isOpen_bundleOneU R).isOpenMap_subtype_val _
      (hS.preimage continuous_quotient_mk'))

/-- The range of `G_x\(W[1]|U(x)) → |W[1]|` is `|P[1]|⁻¹(|U(x)|)`. -/
theorem range_bundleOneOrbitQuotientMap :
    range (E.bundleOneOrbitQuotientMap R) = E.projOrbitMapOne ⁻¹' (X.π '' R.U) := by
  ext c
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Quotient.inductionOn with | h v => ?_
    exact ⟨P (B.oneVal v.1), v.2, rfl⟩
  · intro hc
    obtain ⟨b, rfl⟩ := E.surjective_πOne c
    obtain ⟨y, hy, hyb⟩ := hc
    obtain ⟨w', hww', hw'⟩ := E.exists_isomorphic_of_isomorphic
      ((X.π_eq_π_iff).1 (hyb.trans (E.projOrbitMapOne_πOne b)).symm)
    obtain ⟨⟨⟨φ, w⟩, hq⟩, hs, ht⟩ := hww'
    change w = B.oneVal b at hs
    subst hs
    refine ⟨Quotient.mk _ ⟨E.μOne φ b hq, ?_⟩, ?_⟩
    · change P (E.μ _) ∈ R.U
      have ht' : E.μ ⟨(φ, B.oneVal b), hq⟩ = w' := ht
      rw [ht', hw']; exact hy
    · exact ((E.πOne_eq_πOne_iff).2 ⟨φ, hq, rfl⟩).symm

/-- **`|P[1]|⁻¹(|U(x)|)` is metrizable**: `W[1]|U(x)` is metrizable (an open subset of the
metrizable `W[1]`), so is its quotient by the finite group `G_x` acting by homeomorphisms. -/
theorem metrizableSpace_preimage_projOrbitMapOne :
    MetrizableSpace (E.projOrbitMapOne ⁻¹' (X.π '' R.U)) := by
  have := B.metrizableSpace_one
  have := metrizableSpace_orbitRel_quotient_finite (E.continuous_bundleOneSmul R)
  exact ((E.isOpenEmbedding_bundleOneOrbitQuotientMap R).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (E.range_bundleOneOrbitQuotientMap R))).symm.isEmbedding.metrizableSpace

/-! ### Proposition 8.4.1, (1) ⇔ (3) -/

/-- **`|W[1]|` is metrizable if `|X|` is paracompact** (Smirnov's theorem pulled back along
`|P[1]|`). -/
theorem metrizableSpace_orbitSpaceOne (h : X.HasParacompactOrbitSpace) :
    MetrizableSpace E.OrbitSpaceOne := by
  have := X.theorem_7_3_1_metrizable h
  have : ParacompactSpace X.OrbitSpace := h
  refine metrizableSpace_of_pullback E.projOrbitMapOne E.continuous_projOrbitMapOne fun z => ?_
  obtain ⟨y, rfl⟩ := X.surjective_π z
  obtain ⟨R, -⟩ := X.theorem_7_1_13 y isOpen_univ (mem_univ _)
  exact ⟨X.π '' R.U, X.proposition_7_1_8 _ R.isOpen_U, mem_image_of_mem _ R.mem_U,
    E.metrizableSpace_preimage_projOrbitMapOne R⟩

/-- **2021 Proposition 8.4.1, (1) ⇒ (3)**, p. 380: if `|X|` is paracompact, so is `|W[1]|`. -/
theorem proposition_8_4_1_one_imp_three (h : X.HasParacompactOrbitSpace) :
    ParacompactSpace E.OrbitSpaceOne :=
  have := E.metrizableSpace_orbitSpaceOne h
  paracompactSpace_of_metrizableSpace _

/-! ### Proposition 8.4.1, (3) ⇒ (1): the zero section -/

/-- The zero section as a map `X → W[1]` (the zero section is an sc⁺-section). -/
def zeroOne (y : Obj) : B.One :=
  B.oneMk (fiberZero P y) <| by
    obtain ⟨-, g, hg, -⟩ :=
      (B.isScPlusSection_iff (fiberZero P)).1 (StrongBundle.isScPlusSection_fiberZero (B := B))
    rw [← hg]; exact B.oneVal_mem (g y)

omit [ParacompactSpace (pullbackSpace P X.src)] in
theorem continuous_zeroOne : Continuous (zeroOne (B := B)) := by
  obtain ⟨-, g, hg, hgs⟩ :=
    (B.isScPlusSection_iff (fiberZero P)).1 (StrongBundle.isScPlusSection_fiberZero (B := B))
  have hgz : g = zeroOne (B := B) := funext fun y =>
    B.oneVal_injective (congrFun hg y)
  rw [← hgz]
  exact continuousOn_univ.1 hgs.continuousOn

/-- **The zero section on orbit spaces**, `|0| : |X| → |W[1]|`, `|y| ↦ |0_y|`. -/
def zeroOrbitMapOne : X.OrbitSpace → E.OrbitSpaceOne :=
  Quotient.lift (fun y => E.πOne (zeroOne y)) <| by
    rintro _ _ ⟨φ, rfl, rfl⟩
    exact (E.πOne_eq_πOne_iff).2 ⟨φ, isSection_fiberZero (X.src φ), E.μ_fiberZero φ⟩

theorem continuous_zeroOrbitMapOne : Continuous E.zeroOrbitMapOne :=
  continuous_quot_lift _ (E.continuous_πOne.comp continuous_zeroOne)

/-- `|P[1]| ∘ |0| = id`. -/
theorem leftInverse_zeroOrbitMapOne : LeftInverse E.projOrbitMapOne E.zeroOrbitMapOne := by
  intro z
  induction z using Quotient.ind with
  | _ y => exact congrArg X.π (isSection_fiberZero (P := P) y)

/-- The classes of zero vectors: `|b| ∈ |0|(|X|)` iff `b` is a zero vector. -/
theorem πOne_mem_range_zeroOrbitMapOne_iff (b : B.One) :
    E.πOne b ∈ range E.zeroOrbitMapOne ↔ B.oneVal b = fiberZero P (P (B.oneVal b)) := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨y, rfl⟩ := X.surjective_π z
    obtain ⟨φ, hφ, hμ⟩ := (E.πOne_eq_πOne_iff).1 hz
    have hy : y = X.src φ := (isSection_fiberZero (P := P) y).symm.trans hφ
    subst hy
    have h0 : E.μ ⟨(φ, B.oneVal (zeroOne (X.src φ))), hφ⟩ = fiberZero P (X.tgt φ) :=
      E.μ_fiberZero φ
    have hP : P (B.oneVal b) = X.tgt φ := by rw [← hμ, E.P_μ]
    rw [hP, ← hμ, h0]
  · intro h
    refine ⟨X.π (P (B.oneVal b)), congrArg E.πOne (B.oneVal_injective ?_)⟩
    exact h.symm

/-- **`|0|(|X|)` is closed in `|W[1]|`**: its preimage in `W[1]` is the set of zero vectors,
closed since `W[1]` is Hausdorff. -/
theorem isClosed_range_zeroOrbitMapOne : IsClosed (range E.zeroOrbitMapOne) := by
  rw [← E.isQuotientMap_πOne.isClosed_preimage]
  have hset : E.πOne ⁻¹' range E.zeroOrbitMapOne =
      {b : B.One | B.oneVal b = fiberZero P (P (B.oneVal b))} :=
    Set.ext E.πOne_mem_range_zeroOrbitMapOne_iff
  rw [hset]
  have hz : Continuous (fiberZero P : Obj → W) :=
    continuousOn_univ.1 (B.isScSmoothSection_fiberZero).2.continuousOn
  exact isClosed_eq B.continuous_oneVal (hz.comp (B.continuous.comp B.continuous_oneVal))

/-- **`|0| : |X| → |W[1]|` is a closed embedding** (the text: `|X| ⊂ |W[1]|` is closed). -/
theorem isClosedEmbedding_zeroOrbitMapOne : IsClosedEmbedding E.zeroOrbitMapOne :=
  ⟨E.leftInverse_zeroOrbitMapOne.isEmbedding E.continuous_projOrbitMapOne
    E.continuous_zeroOrbitMapOne, E.isClosed_range_zeroOrbitMapOne⟩

/-- **2021 Proposition 8.4.1, (3) ⇒ (1)**, p. 380: if `|W[1]|` is paracompact, so is `|X|`. -/
theorem proposition_8_4_1_three_imp_one (h : ParacompactSpace E.OrbitSpaceOne) :
    X.HasParacompactOrbitSpace :=
  E.isClosedEmbedding_zeroOrbitMapOne.paracompactSpace

/-- **2021 Proposition 8.4.1, (1) ⇔ (3)**, p. 380: `|X|` is paracompact iff `|W[1]|` is. -/
theorem proposition_8_4_1_one_iff_three :
    X.HasParacompactOrbitSpace ↔ ParacompactSpace E.OrbitSpaceOne :=
  ⟨E.proposition_8_4_1_one_imp_three, E.proposition_8_4_1_three_imp_one⟩

/-- **2021 Proposition 8.4.1**, p. 380 (new in the 2021 edition): for a strong bundle
`(P : W → X, μ)` over an ep-groupoid, (1) `|X|` is paracompact, (2) `|W[0]|` is paracompact,
(3) `|W[1]|` is paracompact, are equivalent. -/
theorem proposition_8_4_1 :
    List.TFAE [X.HasParacompactOrbitSpace, E.toEpGroupoid.HasParacompactOrbitSpace,
      ParacompactSpace E.OrbitSpaceOne] := by
  tfae_have 1 ↔ 2 := E.proposition_8_4_1_one_iff_two
  tfae_have 1 ↔ 3 := E.proposition_8_4_1_one_iff_three
  tfae_finish

end EpStrongBundle

end Prop841Three

end Polyfold
