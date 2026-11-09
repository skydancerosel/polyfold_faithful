import Polyfold.Chapter8.EpStrongBundle
import Polyfold.Chapter8.NonVacuityBundle
import Polyfold.Chapter8.GeometricLift
import Polyfold.Chapter5.AuxNorm

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 8 "Bundles and Covering Functors" (2021 edition): **Definition 8.3.5** (p. 379,
new in the 2021 edition), **Proposition 8.4.1** (p. 380, new), **Definition 8.5.5** (p. 388;
2017: Definition 8.9), **Example 8.5.6** (p. 388, new), **Definition 8.5.9** (p. 394; 2017:
Definition 8.10) and **Lemma 8.5.10** (p. 395, new).  Numbers and pages are the 2021 text's, the
2017 ones in parentheses.

# Chapter 8 in the 2021 edition: the changed and the new items

## The text, paraphrased

(Definition 8.3.5, p. 379) An auxiliary norm for a strong bundle `(P : W → X, μ)` over an
ep-groupoid is a continuous `N : W_{0,1} → [0, ∞)` which (1) is a complete norm on every fibre,
(2) has `h_k → 0_x` in `W_{0,1}` whenever `P(h_k) → x` and `N(h_k) → 0`, and (3) satisfies
`N(μ(φ, k)) = N(k)` for `s(φ) = P(k)`.

(Proposition 8.4.1, p. 380) For a strong bundle over an ep-groupoid, `W[0]` and `W[1]` are
ep-groupoids, and the following are equivalent: (1) `|X|` is paracompact; (2) `|W[0]|` is
paracompact; (3) `|W[1]|` is paracompact.  Proof of (2), (3) ⇒ (1): `|X|` is a closed retract of
`|W[i]|` through the zero section.  Proof of (1) ⇒ (2), (3): local bundle charts with
`G_x`-invariant metrics and a locally finite closed covering, as for `|TX|` (Theorem 8.1.15).

(Definition 8.5.5 and the text after it, p. 388) A covering functor `f : D → C` between finite
groupoids, `C` with one object `x`, is a functor with `ψ ↦ (f(ψ), s(ψ))` a bijection
`D → C × D`; then `f : G_d → G_x` is injective, in general not bijective.  (Example 8.5.6) `D`
has objects `a`, `b` and one morphism between any two of them, `C = {1_x, ε}` with `ε² = 1_x`,
and `f(φ) = f(φ⁻¹) = ε`: a covering functor, `x` has nontrivial isotropy, `a` and `b` have
trivial isotropy.

(Definition 8.5.9, p. 394; 2017: Definition 8.10) A proper strong bundle covering functor is a
strong bundle map `A : W → V` with `Q ∘ A = F ∘ P` satisfying, new in 2021, (0)
`τ(F(ψ), A(w)) = A(μ(ψ, w))`, and (1)–(3) as in 2017.  (Lemma 8.5.10, p. 395) With
`F*V = {(y, v) | F(y) = Q(v)}`, `μ_{F*V}(φ, (y, v)) = (t(φ), μ_X(F(φ), v))` and
`B(w) = (P(w), A(w))`, (8.23) `B(μ_Y(φ, w)) = μ_{F*V}(φ, B(w))`, and `B` is a strong bundle
isomorphism over `Y` covering the identity of `Y`; hence `A = Ā ∘ B` with `Ā(y, v) = v`.

## What is formalized

* `EpStrongBundle.IsAuxNorm` (**Definition 8.3.5**); `EpStrongBundle.exists_oneVal_eq_μ`
  (condition (3) is not vacuous); witnesses `EpStrongBundle.exists_isAuxNorm_trivial` and
  `TrivialBundle.exists_isAuxNorm_epBundle`.
* `EpStrongBundle.proposition_8_4_1_two_imp_one` (**Proposition 8.4.1, (2) ⇒ (1)**), with
  `μ_fiberZero`, `zeroOrbitMap` (`|0| : |X| → |W[0]|`), `continuous_zeroOrbitMap`,
  `leftInverse_zeroOrbitMap` and `isEmbedding_zeroOrbitMap`.
* `IsCoveringFunctor.injective_map_end` (**the remark after Definition 8.5.5**: `f : G_d → G_x` is
  injective); `Example856D`, `example856Functor` and `example_8_5_6` (**Example 8.5.6**,
  including that `f : G_d → G_x` is not surjective there).
* `EpStrongBundle.IsProperStrongBundleCovering2021` (**Definition 8.5.9**);
  `IsProperStrongBundleCovering.isProperStrongBundleCovering2021` and
  `isProperStrongBundleCovering2021_iff` (equivalence with the project's reading of 2017
  Definition 8.10); witnesses `EpStrongBundle.isProperStrongBundleCovering2021_id` and
  `TrivialBundle.epBundle_isProperStrongBundleCovering2021`.
* `EpStrongBundle.pullbackμ` (`μ_{F*V}`), `IsProperStrongBundleCovering2021.bundleB` (`B`),
  `bundleB_μ` (**(8.23)**), `bijective_bundleB`, `bundleBInv`, `isStrongBundleMap_bundleB`,
  `isStrongBundleMap_bundleBInv` and `lemma_8_5_10` (**Lemma 8.5.10**).  `bundleB_val`
  (`B(w) = (P(w), A(w))`) is the factorization `A = Ā ∘ B`.

## What the text leaves implicit, and the choices made

* Definition 8.3.5: (1), (2) and continuity are Part I's auxiliary norm (Definition 5.1.1, the
  project's `StrongBundle.IsAuxNorm`), so `N` is defined on `W_{0,1}` as the level-one space
  `B.One`; values in `[0, ∞)` follow from (1).  In (3), `h ∈ W_{0,1}` is given and `h = μ(φ, k)`
  is an equation in `W`.
* Proposition 8.4.1: only `W[0]` is formalized, since `W[1]` (the bundle `W_{0,1} → X` with the
  sc-structure shifted by one) is not built as an ep-groupoid in the project.  Our proof of
  (2) ⇒ (1) goes through metrizability (Theorem 7.3.1 and Smirnov's theorem) instead of "closed
  subsets of paracompact spaces are paracompact".  (1) ⇒ (2) needs `G_x`-equivariant bundle
  charts for `W` with invariant metrics on `K` and `O`; it is not formalized here.
* Definition 8.5.5: covering functors of the project (`IsCoveringFunctor`, Definition 8.5.5 (2017: 8.9) of 2017)
  are the 2021 ones.  Example 8.5.6 takes `C = ℤˣ` as a one-object category, `ε = −1`.
* Definition 8.5.9 is stated for the **object map** `A : W → V`, condition (0) being the field
  `isMap` (`EpStrongBundle.IsMap`, Definition 8.3.2; 2017: Definition 8.5); (1)–(3) are copied
  from the project's 2017 structure `IsProperStrongBundleCovering`.  That structure had read
  2017's "strong bundle map `A`" as a strong bundle functor, so it already contained (0);
  `isProperStrongBundleCovering2021_iff` proves the two readings equivalent.  The finiteness of
  `F⁻¹(x)` in (2) is in `F.IsProperCovering`.
* Lemma 8.5.10: "strong bundle isomorphism over the ep-groupoid `Y`" is read as a strong bundle
  isomorphism `W → F*V` (Part I's `IsStrongBundleIso`, both directions strong bundle maps covering
  the identity) together with (8.23).  The strong bundle `F*V → Y` is Part I's pull-back
  `BV.pullback`; the instance `ParacompactSpace (F*V)` is a hypothesis of that construction and
  always holds (`StrongBundle.paracompactSpace_pullback`).  That `μ_{F*V}` makes `F*V` an
  `EpStrongBundle` over `Y` (sc-smoothness, local sc-diffeomorphism, unit and composition laws) is
  not proved here; the lemma uses only its formula.  The inverse `B⁻¹` is sc-smooth because near
  every point it is `(y, v) ↦ Ψ(v)` for the inverse `Ψ` of a local strong bundle isomorphism given
  by Definition 8.5.9 (1).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology CategoryTheory

namespace Polyfold

universe u v

/-! ### Definition 8.5.9: proper strong bundle covering functors -/

section Def859

variable {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY] {Y : EpGroupoid ObjY MorY}
  {ObjX MorX : Type u} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX] {X : EpGroupoid ObjX MorX}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → ObjY}
  [∀ y, AddCommGroup (P ⁻¹' {y})] [∀ y, Module ℝ (P ⁻¹' {y})] {BW : StrongBundle Y.PObj P}
  [ParacompactSpace (pullbackSpace P Y.src)]
  {V : Type u} [TopologicalSpace V] [T2Space V] [ParacompactSpace V] {Q : V → ObjX}
  [∀ x, AddCommGroup (Q ⁻¹' {x})] [∀ x, Module ℝ (Q ⁻¹' {x})] {BV : StrongBundle X.PObj Q}
  [ParacompactSpace (pullbackSpace Q X.src)]

namespace EpStrongBundle

/-- **2021 Definition 8.5.9** (proper strong bundle covering functor), p. 394 (2017:
Definition 8.10, with condition (0) added): for strong bundles `(W, μ)` over `Y` and `(V, τ)` over
`X`, a strong bundle map `A : W → V` (fibrewise linear) with `Q ∘ A = F ∘ P` such that
(0) `τ(F(ψ), A(w)) = A(μ(ψ, w))` (with the strong bundle map property: `EpStrongBundle.IsMap`,
Definition 8.3.2; 2017: Definition 8.5), (1) `A` is surjective and a local strong bundle
isomorphism covering an sc-smooth proper covering functor `F`, (2) the even covering by strong
bundle isomorphisms `W|U(y) → V|U(x)`, (3) `(ψ, w) ↦ ((F(ψ), A(w)), w)` a strong bundle
isomorphism covering `ψ ↦ (F(ψ), s(ψ))`.  (1)–(3) are read as in the 2017 structure
`IsProperStrongBundleCovering`; `A` is here the map on objects. -/
structure IsProperStrongBundleCovering2021 (EW : EpStrongBundle Y BW) (EV : EpStrongBundle X BV)
    (F : EpFunctor Y X) (A : W → V) : Prop where
  isMap : EW.IsMap EV F A
  surjective : Surjective A
  isProperCovering : F.IsProperCovering
  isLocalStrongBundleIso : ∀ y : ObjY, ∃ (U : Set ObjY) (U' : Set ObjX), y ∈ U ∧
    BW.IsStrongBundleIsoOn BV isMap.isStrongBundleMap U U'
  evenlyCovered : ∀ x : ObjX, ∃ (U : Set ObjX) (U' : ObjY → Set ObjY), IsOpen U ∧ x ∈ U ∧
    (F.obj ⁻¹' {x}).PairwiseDisjoint U' ∧
    (∀ y ∈ F.obj ⁻¹' {x}, y ∈ U' y ∧
      BW.IsStrongBundleIsoOn BV isMap.isStrongBundleMap (U' y) U) ∧
    F.obj ⁻¹' U = ⋃ y ∈ F.obj ⁻¹' {x}, U' y
  isStrongBundleIso_fibredLift :
    letI := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
    letI := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
    letI := BW.paracompactSpace_pullback (MPolyfold.subPolyfold
      (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj))
      F.fibredSnd
    ∃ (g : MPolyfold.fibredProduct X.src F.obj → MorY)
      (Ψ : pullbackSpace P F.fibredSnd → pullbackSpace P Y.src),
      (BW.pullback Y.isScSmoothMap_src).IsStrongBundleIso (BW.pullback F.isScSmoothMap_fibredSnd)
        F.fibredMap (fibredLift P F) g Ψ

variable {EW : EpStrongBundle Y BW} {EV : EpStrongBundle X BV} {F : EpFunctor Y X}

/-- **The 2017 reading of Definition 8.5.9 (2017: 8.10) gives the 2021 Definition 8.5.9 for the object map**:
condition (0) holds for the object map of a strong bundle functor
(`IsStrongBundleFunctor.μ_comm`, the computation of §8.5.2). -/
theorem IsProperStrongBundleCovering.isProperStrongBundleCovering2021
    {Ψ : EpFunctor EW.toEpGroupoid EV.toEpGroupoid} (h : EW.IsProperStrongBundleCovering EV F Ψ) :
    EW.IsProperStrongBundleCovering2021 EV F Ψ.obj where
  isMap := h.isStrongBundleFunctor.isMap
  surjective := h.surjective
  isProperCovering := h.isProperCovering
  isLocalStrongBundleIso := h.isLocalStrongBundleIso
  evenlyCovered := h.evenlyCovered
  isStrongBundleIso_fibredLift := h.isStrongBundleIso_fibredLift

/-- **2021 Definition 8.5.9 and the project's reading of 2017 Definition 8.10 agree**: a map
`A : W → V` is a proper strong bundle covering functor in the 2021 sense iff it is the object map
of a (unique) strong bundle functor which is one in the 2017 sense.  (The project read 2017's "a
strong bundle map `A`" as a strong bundle functor (Definition 8.3.3 (2017: 8.6)), which already contains the
2021 condition (0).) -/
theorem isProperStrongBundleCovering2021_iff {A : W → V} :
    EW.IsProperStrongBundleCovering2021 EV F A ↔
      ∃! Ψ : EpFunctor EW.toEpGroupoid EV.toEpGroupoid,
        Ψ.obj = A ∧ EW.IsProperStrongBundleCovering EV F Ψ := by
  constructor
  · intro h
    obtain ⟨Ψ, ⟨hΨ, hΨA⟩, huniq⟩ := (isMap_iff_strongBundleFunctor).1 h.isMap
    refine ⟨Ψ, ⟨hΨA, ?_⟩, fun Ψ' hΨ' => huniq Ψ' ⟨hΨ'.2.isStrongBundleFunctor, hΨ'.1⟩⟩
    subst hΨA
    exact { isStrongBundleFunctor := hΨ
            surjective := h.surjective
            isProperCovering := h.isProperCovering
            isLocalStrongBundleIso := h.isLocalStrongBundleIso
            evenlyCovered := h.evenlyCovered
            isStrongBundleIso_fibredLift := h.isStrongBundleIso_fibredLift }
  · rintro ⟨Ψ, ⟨rfl, h⟩, -⟩
    exact h.isProperStrongBundleCovering2021

end EpStrongBundle

end Def859

section Def859Witness

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

/-- **2021 Definition 8.5.9 is satisfiable**: the identity of every strong bundle over an
ep-groupoid is a proper strong bundle covering functor covering the identity functor. -/
theorem EpStrongBundle.isProperStrongBundleCovering2021_id (E : EpStrongBundle X B) :
    E.IsProperStrongBundleCovering2021 E (EpFunctor.id X) id :=
  E.isProperStrongBundleCovering_id.isProperStrongBundleCovering2021

end Def859Witness

/-- **2021 Definition 8.5.9, a concrete instance**: the identity of Part I's trivial strong bundle
`ℝⁿ × ℝᵏ → ℝⁿ` over the trivial ep-groupoid of `ℝⁿ`. -/
theorem TrivialBundle.epBundle_isProperStrongBundleCovering2021 (n k : ℕ) :
    (TrivialBundle.epBundle n k).IsProperStrongBundleCovering2021 (TrivialBundle.epBundle n k)
      (EpFunctor.id (EpGroupoid.trivial (rnPolyfold n))) id :=
  (TrivialBundle.epBundle n k).isProperStrongBundleCovering2021_id

/-! ### Definition 8.5.5 and Example 8.5.6: covering functors -/

section CoveringFunctor

/-- For a covering functor `f : D → C` (2021 Definition 8.5.5; 2017: Definition 8.9) and
`d ∈ D`, **`f : G_d → G_x` is injective** (p. 388: "necessarily an injection"). -/
theorem IsCoveringFunctor.injective_map_end {D : Type} [Groupoid.{0} D] {G : Type} [Group G]
    {f : D ⥤ SingleObj G} (hf : IsCoveringFunctor f) (d : D) :
    Injective (β := G) fun ψ : d ⟶ d => f.map ψ := by
  intro ψ ψ' h
  have h' : coveringMap f ⟨d, d, ψ⟩ = coveringMap f ⟨d, d, ψ'⟩ := Prod.ext h rfl
  have h1 := Sigma.mk.inj_iff.1 (hf.1 h')
  have h2 := Sigma.mk.inj_iff.1 (eq_of_heq h1.2)
  exact eq_of_heq h2.2

/-- The groupoid `D` of **2021 Example 8.5.6** (p. 388): two objects `a = false`, `b = true` and
exactly one morphism between any two objects (`1_a`, `1_b`, `φ : a → b`, `φ⁻¹ : b → a`). -/
def Example856D : Type := Bool

instance : DecidableEq Example856D := inferInstanceAs (DecidableEq Bool)

/-- The groupoid structure of `D`: `Hom a b = Unit`. -/
instance : Groupoid.{0} Example856D where
  Hom _ _ := Unit
  id _ := ()
  comp _ _ := ()
  inv _ := ()

theorem example856_sign_comp : ∀ a b c : Bool, (if a = c then 1 else -1 : ℤˣ) =
    (if b = c then 1 else -1 : ℤˣ) * (if a = b then 1 else -1 : ℤˣ) := by
  decide

theorem example856_sign_inj : ∀ a b b' : Bool,
    (if a = b then 1 else -1 : ℤˣ) = (if a = b' then 1 else -1) → b = b' := by
  decide

theorem example856_sign_not : ∀ a : Bool, (if a = !a then 1 else -1 : ℤˣ) = -1 := by
  decide

/-- The functor `f : D → C = {1_x, ε}` (`ℤˣ = {1, −1}`, `ε = −1`) of **2021 Example 8.5.6**:
`f(1_a) = f(1_b) = 1_x`, `f(φ) = f(φ⁻¹) = ε`. -/
def example856Functor : Example856D ⥤ SingleObj ℤˣ where
  obj _ := SingleObj.star ℤˣ
  map {a b} _ := (if a = b then 1 else -1 : ℤˣ)
  map_id a := by
    change (if a = a then 1 else -1 : ℤˣ) = 1
    rw [if_pos rfl]
  map_comp {a b c} _ _ := by
    change (if a = c then 1 else -1 : ℤˣ) =
      (if b = c then 1 else -1 : ℤˣ) * (if a = b then 1 else -1 : ℤˣ)
    exact example856_sign_comp a b c

/-- **2021 Example 8.5.6**, p. 388 (new in the 2021 edition): `f : D → C` is a covering functor
(`ψ ↦ (f(ψ), s(ψ))` is a bijection `D → C × D`), the isotropy groups `G_a`, `G_b` are trivial while
`G_x = C = ℤˣ` is not, and `f : G_d → G_x` is injective but not surjective. -/
theorem example_8_5_6 :
    IsCoveringFunctor example856Functor ∧
      (∀ d : Example856D, Subsingleton (d ⟶ d)) ∧ Nontrivial ℤˣ ∧
      (∀ d : Example856D, Injective (β := ℤˣ) fun ψ : d ⟶ d => example856Functor.map ψ) ∧
      (∀ d : Example856D, ¬ Surjective (β := ℤˣ) fun ψ : d ⟶ d => example856Functor.map ψ) := by
  have hcov : IsCoveringFunctor example856Functor := by
    constructor
    · rintro ⟨a, b, u⟩ ⟨a', b', u'⟩ h
      have h' : ((if a = b then 1 else -1 : ℤˣ), a) = ((if a' = b' then 1 else -1 : ℤˣ), a') := h
      obtain ⟨h1, rfl⟩ := Prod.mk_inj.1 h'
      have hb : b = b' := example856_sign_inj a b b' h1
      subst hb
      rfl
    · rintro ⟨g, a⟩
      rcases Int.units_eq_one_or g with rfl | rfl
      · exact ⟨⟨a, a, ()⟩, by
          change ((if a = a then 1 else -1 : ℤˣ), a) = (1, a)
          rw [if_pos rfl]⟩
      · exact ⟨⟨a, (Bool.not (a : Bool) : Example856D), ()⟩, Prod.ext (example856_sign_not a) rfl⟩
  refine ⟨hcov, fun d => ⟨fun _ _ => rfl⟩, ⟨⟨1, -1, by decide⟩⟩, hcov.injective_map_end,
    fun d h => ?_⟩
  obtain ⟨ψ, hψ⟩ := h (-1)
  change (if d = d then 1 else -1 : ℤˣ) = -1 at hψ
  rw [if_pos rfl] at hψ
  exact absurd hψ (by decide)

end CoveringFunctor

/-! ### Definition 8.3.5: auxiliary norms -/

section AuxNorm

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

/-- **2021 Definition 8.3.5** (auxiliary norm), p. 379 (new in the 2021 edition): for a strong
bundle `(P : W → X, μ)` over an ep-groupoid, a continuous `N : W_{0,1} → [0, ∞)` with (1) a
complete norm on every fibre, (2) `P(h_k) → x`, `N(h_k) → 0` imply `h_k → 0_x` in `W_{0,1}`
((1), (2) and continuity are Part I's Definition 5.1.1 (2017: 5.1), `StrongBundle.IsAuxNorm`; the values are
`≥ 0` by `IsAuxNorm.nonneg`), and (3) `N(h) = N(k)` whenever `h = μ(φ, k)`, `s(φ) = P(k)`. -/
structure IsAuxNorm (E : EpStrongBundle X B) (N : B.One → ℝ) : Prop where
  isAuxNorm : B.IsAuxNorm N
  map_μ : ∀ (h k : B.One) (φ : Mor) (hk : P (B.oneVal k) = X.src φ),
    B.oneVal h = E.μ ⟨(φ, B.oneVal k), hk⟩ → N h = N k

/-- Condition (3) is not vacuous: `μ` maps `𝐗 ₛ×_P W_{0,1}` into `W_{0,1}`, so for every
`k ∈ W_{0,1}` and `φ` with `s(φ) = P(k)` there is `h ∈ W_{0,1}` with `h = μ(φ, k)`. -/
theorem exists_oneVal_eq_μ (E : EpStrongBundle X B) (k : B.One) (φ : Mor)
    (hk : P (B.oneVal k) = X.src φ) : ∃ h : B.One, B.oneVal h = E.μ ⟨(φ, B.oneVal k), hk⟩ := by
  have := B.paracompactSpace_pullback X.PMor X.src
  have hmem : (⟨(φ, B.oneVal k), hk⟩ : pullbackSpace P X.src) ∈
      (B.pullback X.isScSmoothMap_src).oneSet :=
    (B.mem_oneSet_pullback_iff X.isScSmoothMap_src _).2 (B.oneVal_mem k)
  exact ⟨B.oneMk _ (E.isStrongBundleMap.mapsTo_oneSet hmem), rfl⟩

end EpStrongBundle

end AuxNorm

section AuxNormWitness

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Z}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- **2021 Definition 8.3.5 is satisfiable**: over the trivial ep-groupoid (`μ(z, w) = w`) every
auxiliary norm of Part I (Proposition 5.3 gives one) satisfies (3). -/
theorem EpStrongBundle.exists_isAuxNorm_trivial (B : StrongBundle PZ P) :
    ∃ N : B.One → ℝ, (EpStrongBundle.trivial B).IsAuxNorm N := by
  obtain ⟨N, hN⟩ := proposition_5_1_3_exists (B := B)
  exact ⟨N, hN, fun h k _ _ hhk => by rw [B.oneVal_injective hhk]⟩

/-- A concrete instance: Part I's trivial strong bundle `ℝⁿ × ℝᵏ → ℝⁿ` over the trivial
ep-groupoid of `ℝⁿ`. -/
theorem TrivialBundle.exists_isAuxNorm_epBundle (n k : ℕ) :
    ∃ N : (TrivialBundle.bundle n k).One → ℝ, (TrivialBundle.epBundle n k).IsAuxNorm N :=
  EpStrongBundle.exists_isAuxNorm_trivial (TrivialBundle.bundle n k)

end AuxNormWitness

/-! ### Proposition 8.4.1: paracompactness of `|W[0]|` implies paracompactness of `|X|` -/

section Prop841

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B)

namespace EpStrongBundle

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- `μ(φ, 0_{s(φ)}) = 0_{t(φ)}`: `μ(φ, ·)` is linear on the fibres. -/
theorem μ_fiberZero (φ : Mor) :
    E.μ ⟨(φ, fiberZero P (X.src φ)), isSection_fiberZero (X.src φ)⟩ = fiberZero P (X.tgt φ) := by
  have h0 := congrArg Subtype.val ((E.fiberMor φ).map_zero)
  rw [fiberMor_apply] at h0
  exact h0

/-- **The zero section on orbit spaces**, `|0| : |X| → |W|`, `|x| ↦ |0_x|` (the zero section
`X → W[0]` is a functor: the morphism `(φ, 0_x) : 0_x → μ(φ, 0_x) = 0_y` lies over `φ : x → y`). -/
noncomputable def zeroOrbitMap : X.OrbitSpace → E.toEpGroupoid.OrbitSpace :=
  Quotient.lift (fun x => E.toEpGroupoid.π (fiberZero P x)) <| by
    rintro _ _ ⟨φ, rfl, rfl⟩
    exact E.toEpGroupoid.π_eq_π_iff.2
      ⟨⟨(φ, fiberZero P (X.src φ)), isSection_fiberZero (X.src φ)⟩, rfl, E.μ_fiberZero φ⟩

theorem continuous_zeroOrbitMap : Continuous E.zeroOrbitMap :=
  continuous_quot_lift _ (E.toEpGroupoid.continuous_π.comp
    (continuousOn_univ.1 (B.isScSmoothSection_fiberZero).2.continuousOn))

/-- `|P| ∘ |0| = id`. -/
theorem leftInverse_zeroOrbitMap : LeftInverse E.projFunctor.orbitMap E.zeroOrbitMap := by
  intro z
  induction z using Quotient.ind with
  | _ x => exact congrArg X.π (isSection_fiberZero (P := P) x)

/-- `|0| : |X| → |W|` is a topological embedding (it has the continuous left inverse `|P|`). -/
theorem isEmbedding_zeroOrbitMap : IsEmbedding E.zeroOrbitMap :=
  E.leftInverse_zeroOrbitMap.isEmbedding E.continuous_orbitMap_projFunctor
    E.continuous_zeroOrbitMap

/-- **2021 Proposition 8.4.1, (2) ⇒ (1)**, p. 380 (new in the 2021 edition): if the orbit space
`|W[0]|` of the ep-groupoid `(W, 𝐖)` (the functorial picture) is paracompact, so is `|X|`: `|W|`
is metrizable (Theorem 7.3.1 and Smirnov's theorem, `theorem_7_3_1_metrizable`), `|X|` embeds into
it by the zero section (the text's proof: "`|X|` is homeomorphic to the image of the zero
section"), hence is metrizable, hence paracompact. -/
theorem proposition_8_4_1_two_imp_one (h : E.toEpGroupoid.HasParacompactOrbitSpace) :
    X.HasParacompactOrbitSpace := by
  have := E.toEpGroupoid.theorem_7_3_1_metrizable h
  have := E.isEmbedding_zeroOrbitMap.metrizableSpace
  exact paracompactSpace_of_metrizableSpace _

end EpStrongBundle

end Prop841

/-! ### Lemma 8.5.10: `W ≅ F*V` -/

section Lemma8510

variable {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY] {Y : EpGroupoid ObjY MorY}
  {ObjX MorX : Type u} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX] {X : EpGroupoid ObjX MorX}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → ObjY}
  [∀ y, AddCommGroup (P ⁻¹' {y})] [∀ y, Module ℝ (P ⁻¹' {y})] {BW : StrongBundle Y.PObj P}
  [ParacompactSpace (pullbackSpace P Y.src)]
  {V : Type u} [TopologicalSpace V] [T2Space V] [ParacompactSpace V] {Q : V → ObjX}
  [∀ x, AddCommGroup (Q ⁻¹' {x})] [∀ x, Module ℝ (Q ⁻¹' {x})] {BV : StrongBundle X.PObj Q}
  [ParacompactSpace (pullbackSpace Q X.src)]
  {EW : EpStrongBundle Y BW} {EV : EpStrongBundle X BV} {F : EpFunctor Y X} {A : W → V}

namespace EpStrongBundle

/-- **The structure map of `F*V`** (p. 395): `μ_{F*V}(φ, (y, v)) = (t(φ), μ_X(F(φ), v))` for
`y = s(φ)`, on the pull-back `F*V = {(y, v) | F(y) = Q(v)} ⊆ Y × V`. -/
def pullbackμ (EV : EpStrongBundle X BV) (F : EpFunctor Y X) (φ : MorY)
    (q : pullbackSpace Q F.obj) (hq : (q : ObjY × V).1 = Y.src φ) : pullbackSpace Q F.obj :=
  ⟨(Y.tgt φ, EV.μ ⟨(F.mor φ, (q : ObjY × V).2), by
      change Q (q : ObjY × V).2 = X.src (F.mor φ)
      rw [show Q (q : ObjY × V).2 = F.obj (q : ObjY × V).1 from q.2, hq, F.src_mor]⟩), by
    change Q (EV.μ _) = F.obj (Y.tgt φ)
    rw [EV.P_μ, F.tgt_mor]⟩

namespace IsProperStrongBundleCovering2021

variable (h : EW.IsProperStrongBundleCovering2021 EV F A)

/-- **The map `B : W → F*V`, `B(w) = (P(w), A(w))`** (p. 395). -/
def bundleB : W → pullbackSpace Q F.obj :=
  pullbackPair Q F.obj P A h.isMap.isStrongBundleMap.covers

omit [ParacompactSpace (pullbackSpace Q X.src)] in
@[simp] lemma bundleB_val (w : W) : (h.bundleB w : ObjY × V) = (P w, A w) := rfl

omit [ParacompactSpace (pullbackSpace Q X.src)] in
/-- **(8.23)**: `B(μ_Y(φ, w)) = μ_{F*V}(φ, B(w))`. -/
theorem bundleB_μ (φ : MorY) (w : W) (hw : P w = Y.src φ) :
    h.bundleB (EW.μ ⟨(φ, w), hw⟩) = pullbackμ EV F φ (h.bundleB w) hw := by
  apply Subtype.ext
  change (P (EW.μ ⟨(φ, w), hw⟩), A (EW.μ ⟨(φ, w), hw⟩)) =
    (Y.tgt φ, EV.μ ⟨(F.mor φ, A w), _⟩)
  rw [EW.P_μ, h.isMap.map_μ φ w hw]

omit [ParacompactSpace (pullbackSpace Q X.src)] in
/-- Over a local strong bundle isomorphism `W|U → V|U'` covering `F : U → U'`, `F` is injective
on `U`, so `P(w) = y` when `P(w), y ∈ U` and `Q(A(w)) = F(y)`. -/
theorem eq_of_isStrongBundleIsoOn {U : Set ObjY} {U' : Set ObjX}
    (hi : BW.IsStrongBundleIsoOn BV h.isMap.isStrongBundleMap U U') {w : W} {y : ObjY}
    (hw : P w ∈ U) (hy : y ∈ U) (hQ : Q (A w) = F.obj y) : P w = y := by
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  exact hg.injOn hw hy ((h.isMap.isStrongBundleMap.covers w).symm.trans hQ)

omit [ParacompactSpace (pullbackSpace Q X.src)] in
/-- **`B` is bijective** (the proof of Lemma 8.5.10: `A_y : W_y → V_{F(y)}` is a linear
isomorphism). -/
theorem bijective_bundleB : Bijective h.bundleB := by
  refine ⟨fun w w' hww => ?_, fun q => ?_⟩
  · have h1 : P w = P w' := congrArg (fun q : pullbackSpace Q F.obj => (q : ObjY × V).1) hww
    have h2 : A w = A w' := congrArg (fun q : pullbackSpace Q F.obj => (q : ObjY × V).2) hww
    obtain ⟨U, U', hy, hi⟩ := h.isLocalStrongBundleIso (P w)
    have e := (hi.fiberEquiv hy).injective (a₁ := ⟨w, rfl⟩) (a₂ := ⟨w', h1.symm⟩)
      (Subtype.ext h2)
    exact congrArg Subtype.val e
  · obtain ⟨U, U', hy, hi⟩ := h.isLocalStrongBundleIso (q : ObjY × V).1
    set e := hi.fiberEquiv hy
    let v : Q ⁻¹' {F.obj (q : ObjY × V).1} := ⟨(q : ObjY × V).2, q.2⟩
    refine ⟨(e.symm v : W), Subtype.ext (Prod.ext (e.symm v).2 ?_)⟩
    exact congrArg Subtype.val (e.apply_symm_apply v)

/-- The inverse `B⁻¹ : F*V → W`. -/
noncomputable def bundleBInv : pullbackSpace Q F.obj → W :=
  surjInv h.bijective_bundleB.2

omit [ParacompactSpace (pullbackSpace Q X.src)] in
theorem bundleB_bundleBInv (q : pullbackSpace Q F.obj) : h.bundleB (h.bundleBInv q) = q :=
  surjInv_eq _ q

omit [ParacompactSpace (pullbackSpace Q X.src)] in
theorem bundleBInv_bundleB (w : W) : h.bundleBInv (h.bundleB w) = w :=
  leftInverse_surjInv h.bijective_bundleB w

omit [ParacompactSpace (pullbackSpace Q X.src)] in
theorem P_bundleBInv (q : pullbackSpace Q F.obj) : P (h.bundleBInv q) = (q : ObjY × V).1 :=
  congrArg (fun q : pullbackSpace Q F.obj => (q : ObjY × V).1) (h.bundleB_bundleBInv q)

omit [ParacompactSpace (pullbackSpace Q X.src)] in
/-- Over a local strong bundle isomorphism at `q.1`: `B⁻¹(q) = w` as soon as `P(w) ∈ U` and
`A(w) = q.2`. -/
theorem bundleBInv_eq_of {U : Set ObjY} {U' : Set ObjX}
    (hi : BW.IsStrongBundleIsoOn BV h.isMap.isStrongBundleMap U U') {q : pullbackSpace Q F.obj}
    (hq : (q : ObjY × V).1 ∈ U) {w : W} (hw : P w ∈ U) (hA : A w = (q : ObjY × V).2) :
    h.bundleBInv q = w := by
  have hP : P w = (q : ObjY × V).1 := h.eq_of_isStrongBundleIsoOn hi hw hq (by
    rw [hA]; exact q.2)
  rw [← h.bundleBInv_bundleB w]
  exact congrArg h.bundleBInv (Subtype.ext (Prod.ext hP.symm hA.symm))

omit [ParacompactSpace (pullbackSpace Q X.src)] in
theorem mem_tgt_of_mem {U : Set ObjY} {U' : Set ObjX}
    (hi : BW.IsStrongBundleIsoOn BV h.isMap.isStrongBundleMap U U') {q : pullbackSpace Q F.obj}
    (hq : (q : ObjY × V).1 ∈ U) : Q (q : ObjY × V).2 ∈ U' := by
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  rw [show Q (q : ObjY × V).2 = F.obj (q : ObjY × V).1 from q.2]
  exact hg.mapsTo hq

variable [ParacompactSpace (pullbackSpace Q F.obj)]

omit [ParacompactSpace (pullbackSpace Q X.src)] in
/-- **`B` is a strong bundle map covering the identity of `Y`**: `(P, A)` is sc-smooth at the
levels `[0]` and `[1]` by the universal properties of the pull-back, and fibrewise linear since
`A` is. -/
theorem isStrongBundleMap_bundleB :
    BW.IsStrongBundleMap (BV.pullback F.isScSmoothMap_obj) id h.bundleB where
  covers _ := rfl
  fiber_linear y := by
    let L : P ⁻¹' {y} →ₗ[ℝ] pullbackProj Q F.obj ⁻¹' {y} :=
      (pullbackFiberLinearEquiv Q F.obj y).symm.toLinearMap.comp
        (h.isMap.isStrongBundleMap.fiber_linear y).mk'
    have hL : fiberRestrict P (pullbackProj Q F.obj) id h.bundleB (fun _ => rfl) y = L := by
      funext v
      apply Subtype.ext; apply Subtype.ext
      have hv : P v = y := v.2
      change (P v, A v) = (y, A v)
      rw [hv]
    rw [hL]; exact L.isLinear
  isScSmoothMap := BV.isScSmoothMap_pullbackPair F.isScSmoothMap_obj BW.isScSmoothMap_proj
    h.isMap.isStrongBundleMap.isScSmoothMap h.isMap.isStrongBundleMap.covers
  mapsTo_oneSet w hw := (BV.mem_oneSet_pullback_iff F.isScSmoothMap_obj _).2
    (h.isMap.isStrongBundleMap.mapsTo_oneSet hw)
  isScSmoothMap_one := BV.isScSmoothMap_to_pullback_one F.isScSmoothMap_obj
    (BW.isScSmoothMap_proj.comp BW.isScSmoothMap_oneVal) h.isMap.isStrongBundleMap.isScSmoothMap_one

omit [ParacompactSpace (pullbackSpace Q X.src)] in
/-- `B⁻¹` maps `(F*V)_{0,1}` into `W_{0,1}` (through the local strong bundle isomorphisms at
level `[1]`). -/
theorem mapsTo_oneSet_bundleBInv :
    MapsTo h.bundleBInv (BV.pullback F.isScSmoothMap_obj).oneSet BW.oneSet := by
  intro q hq
  have hq2 := (BV.mem_oneSet_pullback_iff F.isScSmoothMap_obj q).1 hq
  obtain ⟨U, U', hy, hi⟩ := h.isLocalStrongBundleIso (q : ObjY × V).1
  obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
  have hv1 : BV.oneMk _ hq2 ∈ (Q ∘ BV.oneVal) ⁻¹' U' := h.mem_tgt_of_mem hi hy
  have hw1 := hΨ₁.mapsTo_inv hv1
  have hA1 := congrArg BV.oneVal (hΨ₁.right_inv _ hv1)
  rw [h.bundleBInv_eq_of hi hy hw1 hA1]
  exact BW.oneVal_mem _

omit [ParacompactSpace (pullbackSpace Q X.src)] in
/-- **`B⁻¹` is a strong bundle map covering the identity**: near every point it is
`(y, v) ↦ Ψ(v)` (resp. `Ψ₁(v)` at level `[1]`) for the inverse `Ψ` of a local strong bundle
isomorphism `A : W|U → V|U'`. -/
theorem isStrongBundleMap_bundleBInv :
    (BV.pullback F.isScSmoothMap_obj).IsStrongBundleMap BW id h.bundleBInv where
  covers := h.P_bundleBInv
  fiber_linear y := by
    have hB := (h.isStrongBundleMap_bundleB).fiber_linear y
    set f := fiberRestrict P (pullbackProj Q F.obj) id h.bundleB (fun _ => rfl) y with hf
    set g := fiberRestrict (pullbackProj Q F.obj) P id h.bundleBInv h.P_bundleBInv y with hg
    have hfg : ∀ a, f (g a) = a := fun a => Subtype.ext (h.bundleB_bundleBInv a)
    have hgf : ∀ b, g (f b) = b := fun b => Subtype.ext (h.bundleBInv_bundleB b)
    have hinj : Injective f := fun b b' hbb => by rw [← hgf b, hbb, hgf]
    refine ⟨fun a a' => hinj ?_, fun c a => hinj ?_⟩
    · rw [hB.map_add, hfg, hfg, hfg]
    · rw [hB.map_smul, hfg, hfg]
  isScSmoothMap := by
    refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun q _ => ?_
    obtain ⟨U, U', hy, hi⟩ := h.isLocalStrongBundleIso (q : ObjY × V).1
    obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
    obtain ⟨Ψ, hΨ⟩ := hi.isScDiffeoOn_zero
    have hO : IsOpen (pullbackProj Q F.obj ⁻¹' U) :=
      hg.isScSmoothOn.isOpen.preimage (continuousOn_univ.1
        (BV.isScSmoothMap_pullbackProj F.isScSmoothMap_obj).continuousOn)
    refine ⟨_, hO, hy, subset_univ _, ?_⟩
    refine (MPolyfold.IsScSmoothOn.comp hΨ.isScSmoothOn_inv
      ((BV.isScSmoothMap_pullbackProj' F.isScSmoothMap_obj).mono hO (subset_univ _))
      fun q' hq' => h.mem_tgt_of_mem hi hq').congr fun q' hq' => ?_
    exact (h.bundleBInv_eq_of hi hq' (hΨ.mapsTo_inv (h.mem_tgt_of_mem hi hq'))
      (hΨ.right_inv _ (h.mem_tgt_of_mem hi hq'))).symm
  mapsTo_oneSet := h.mapsTo_oneSet_bundleBInv
  isScSmoothMap_one := by
    refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun q1 _ => ?_
    set q := (BV.pullback F.isScSmoothMap_obj).oneVal q1
    obtain ⟨U, U', hy, hi⟩ := h.isLocalStrongBundleIso (q : ObjY × V).1
    obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
    obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
    have hO : IsOpen ((pullbackProj Q F.obj ∘ (BV.pullback F.isScSmoothMap_obj).oneVal) ⁻¹' U) :=
      hg.isScSmoothOn.isOpen.preimage ((continuousOn_univ.1
        (BV.isScSmoothMap_pullbackProj F.isScSmoothMap_obj).continuousOn).comp
        (BV.pullback F.isScSmoothMap_obj).continuous_oneVal)
    have hmaps : MapsTo (BV.pullbackProj'One F.isScSmoothMap_obj)
        ((pullbackProj Q F.obj ∘ (BV.pullback F.isScSmoothMap_obj).oneVal) ⁻¹' U)
        ((Q ∘ BV.oneVal) ⁻¹' U') := fun q' hq' => h.mem_tgt_of_mem hi hq'
    refine ⟨_, hO, hy, subset_univ _, ?_⟩
    refine (MPolyfold.IsScSmoothOn.comp hΨ₁.isScSmoothOn_inv
      ((BV.isScSmoothMap_one_pullbackProj' F.isScSmoothMap_obj).mono hO (subset_univ _))
      hmaps).congr fun q' hq' => ?_
    apply BW.oneVal_injective
    have hA1 := congrArg BV.oneVal (hΨ₁.right_inv _ (hmaps hq'))
    exact (h.bundleBInv_eq_of hi hq' (hΨ₁.mapsTo_inv (hmaps hq')) hA1).symm

omit [ParacompactSpace (pullbackSpace Q X.src)] in
/-- **2021 Lemma 8.5.10**, p. 395 (new in the 2021 edition): for a proper strong bundle covering
functor `A : W → V` covering `F : Y → X` (Definition 8.5.9), `B(w) = (P(w), A(w))` is a strong
bundle isomorphism `W → F*V` over `Y` covering the identity of `Y` (with inverse `B⁻¹`), and it
is compatible with the structure maps: `B(μ_Y(φ, w)) = μ_{F*V}(φ, B(w))` (8.23). -/
theorem lemma_8_5_10 :
    BW.IsStrongBundleIso (BV.pullback F.isScSmoothMap_obj) id h.bundleB id h.bundleBInv ∧
      (∀ w, pullbackProj Q F.obj (h.bundleB w) = P w) ∧
      ∀ (φ : MorY) (w : W) (hw : P w = Y.src φ),
        h.bundleB (EW.μ ⟨(φ, w), hw⟩) = pullbackμ EV F φ (h.bundleB w) hw :=
  ⟨⟨h.isStrongBundleMap_bundleB, h.isStrongBundleMap_bundleBInv, h.bundleBInv_bundleB,
    h.bundleB_bundleBInv⟩, fun _ => rfl, h.bundleB_μ⟩

end IsProperStrongBundleCovering2021

end EpStrongBundle

end Lemma8510

end Polyfold
