import Polyfold.Chapter8.Basic
import Polyfold.Chapter8.StrongBundleMap
import Polyfold.Chapter3.TameGermsG

set_option maxSynthPendingDepth 3

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II, §8.3,
"Strong Bundles over Ep-Groupoids", pp. 270–275: **Definitions 8.3.1, 8.3.2 and 8.3.4 (2017: 8.4, 8.5 and 8.7)** (the lead's
definitions; the functorial picture and Definition 8.3.3 (2017: 8.6) follow below them).  Also §8.4, p. 285:
**Definition 8.5.9 (2017: 8.10)** (proper strong bundle covering functors), and Appendix **§8.5.2**, "The
Structure of Strong Bundle Coverings", pp. 288–289.

# Strong bundles over ep-groupoids

## The text, paraphrased

(pp. 270–271) Let `X = (X, 𝐗)` be an ep-groupoid and `P : W → X` a strong M-polyfold bundle over
the object M-polyfold.  Since `s : 𝐗 → X` is a local sc-diffeomorphism, the fibred product
`𝐗 ₛ×_P W = {(ψ, w) ∈ 𝐗 × W | s(ψ) = P(w)}` is an M-polyfold and, as the pull-back of `P`, a
strong bundle `π₁ : 𝐗 ₛ×_P W → 𝐗`.

(Definition 8.3.1 (2017: 8.4)) A strong bundle over `X` is a pair `(P, μ)`: `P : W → X` a strong bundle over the
object M-polyfold and `μ : 𝐗 ₛ×_P W → W` a strong bundle map covering `t`, `P ∘ μ(ψ, w) = t(ψ)`,
with (1) `μ` a surjective local sc-diffeomorphism, linear on the fibres; (2) `μ(1_x, w) = w`;
(3) `μ(ψ ∘ γ, w) = μ(ψ, μ(γ, w))` whenever `s(γ) = P(w)` and `t(γ) = s(ψ) = P(μ(γ, w))`.

(Definition 8.3.2 (2017: 8.5)) A strong bundle map between `(P : W → X, μ)` and `(P' : W' → X', μ')` is a
strong bundle map `Φ : W → W'` covering an sc-smooth functor `ϕ : X → X'` with
`Φ(μ(γ, w)) = μ'(ϕ(γ), Φ(w))` for `s(γ) = P(w)`.

(Definition 8.3.4 (2017: 8.7)) For a strong bundle `(P, μ)` over `X`: (1) an sc-smooth section functor is an
sc-smooth section `f` of `P` with `f(y) = μ(φ, f(x))` for `φ : x → y`; `Γ(P, μ)` the vector space
of these; (2) an sc⁺-section functor is one with values in `W_{0,1}`, sc-smooth as a section of
`W[1] → X`, `Γ⁺(P, μ)`; (3) an sc-Fredholm section functor is one which is an sc-Fredholm section
of `W → X`, `Fred(P, μ)`.

(pp. 271–272, the functorial picture) `μ(ψ, ·) : W_x → W_y` is a linear isomorphism for
`ψ : x → y`.  With `𝐖 = 𝐗 ₛ×_P W` "we can define the ep-groupoid" `(W, 𝐖)`: `s_𝐖(ψ, w) = w`,
`t_𝐖(ψ, w) = μ(ψ, w)` (fibrewise linear local sc-diffeomorphisms covering `s`, `t`),
`1_w = (1_x, w)`, `(ψ, w)⁻¹ = (ψ⁻¹, μ(ψ, w))`, `(ψ, w') ∘ (γ, w) = (ψ ∘ γ, w)` for
`w' = μ(γ, w)`.  The orbit of `w` covers that of `P(w)`, so `|P| : |W| → |X|` is surjective and
continuous; `(P, π₁) : (W, 𝐖) → (X, 𝐗)` is an sc-smooth functor.  (pp. 273–274) A strong bundle
map `Φ` of Definition 8.3.2 (2017: 8.5) lifts to `Φ(γ, w) = (ϕ(γ), Φ(w))`, a strong bundle map `𝐖 → 𝐖'`
covering `ϕ : 𝐗 → 𝐗'` with `s' ∘ Φ = Φ ∘ s`, `t' ∘ Φ = Φ ∘ t`; conversely a functor covering `ϕ`
and linear on the fibres gives a strong bundle map with the properties of Definition 8.3.2 (2017: 8.5), and
"from the strong bundle map we can recover the functor completely".  (Definition 8.3.3 (2017: 8.6)) A strong
bundle functor is a functor `Φ : (W, 𝐖) → (W', 𝐖')`, linear on the fibres, covering an sc-smooth
functor `ϕ : X → X'` and inducing strong bundle maps `W → W'` and `𝐖 → 𝐖'` with
`P' ∘ Φ = ϕ ∘ P`.

(Definition 8.5.9 (2017: 8.10), p. 394 (2017 p. 285)) For strong bundles `P : W → Y` (structure map `μ`) and `Q : V → X`
(`τ`) over ep-groupoids, a proper strong bundle covering functor is a strong bundle map `A`
(fibrewise linear) with `Q ∘ A = F ∘ P` and (1) `A` is surjective and a local strong bundle
isomorphism covering an sc-smooth proper covering functor `F : Y → X`; (2) `F⁻¹(x)` is finite and
there are open `U(x)` and mutually disjoint open `U(y)`, `y ∈ F⁻¹(x)`, with
`A : W|U(y) → V|U(x)` strong bundle isomorphisms and `F⁻¹(U(x)) = ⋃ U(y)`; (3) the map
`𝐖 → 𝐕 ₛ×_A W`, `(ψ, w) ↦ ((F(ψ), A(w)), w)`, is a strong bundle isomorphism covering the
sc-diffeomorphism `𝐘 → 𝐗 ₛ×_F Y`, `ψ ↦ (F(ψ), s(ψ))`, the projection `𝐕 ₛ×_A W → 𝐗 ₛ×_F Y`
being `((φ, v), w) ↦ (φ, P(w))`.  (§8.5.2, pp. 288–289) On morphisms
`A(φ, w) = (F(φ), A_{s(φ)}(w))`, `A_y : P⁻¹(y) → Q⁻¹(F(y))` the topological linear isomorphism
induced by `A`; from `t(A(φ, w)) = A(t(φ, w))`, `μ_X(F(φ)) ∘ A_{s(φ)} = A_{t(φ)} ∘ μ_Y(φ)`, so
that, viewing `μ_Y`, `μ_X` as functors into the category `Ban` of Banach spaces and topological
linear isomorphisms, `y ↦ A_y` is a natural transformation `μ_Y → μ_X ∘ F`.

## What is formalized

* `EpStrongBundle X B` (**Definition 8.3.1 (2017: 8.4)**) for a strong bundle `B : StrongBundle X.PObj P`: the
  structure map `μ` on Part I's pull-back `pullbackSpace P X.src` (whose points are the pairs
  `((ψ, w), s(ψ) = P(w))`) with its strong bundle structure `B.pullback X.isScSmoothMap_src`
  (Proposition 2.6.8 (2017: 2.16) [2.54]); `μ` a strong bundle map covering `t` in the sense of
  `StrongBundle.IsStrongBundleMap` (`StrongBundleMap.lean`; this contains `P ∘ μ = t ∘ π₁` and
  the linearity on the fibres), a surjective local sc-diffeomorphism of the `[0]`-M-polyfolds,
  and (2), (3).
* `EpStrongBundle.IsMap` (**Definition 8.3.2 (2017: 8.5)**).
* `EpStrongBundle.IsScSmoothSectionFunctor`, `IsScPlusSectionFunctor`,
  `IsScFredholmSectionFunctor` (**Definition 8.3.4 (2017: 8.7)**) and the sets `Γ`, `Γ⁺`, `Fred`.
* **The fibre maps** (p. 271): `EpStrongBundle.fiberMor ψ : W_{s(ψ)} →L W_{t(ψ)}`, `μ_add`,
  `μ_smul`, and `fiberMorEquiv ψ : W_{s(ψ)} ≃L W_{t(ψ)}` (**`μ(ψ, ·)` is a linear isomorphism**,
  inverse `μ(ψ⁻¹, ·)`: `μ_inv_μ`, `μ_μ_inv`); `continuous_μ`, `μ_congr`.
* **The functorial picture** (pp. 271–272): `EpStrongBundle.morInv`, `morComp` (`morComp_val`,
  `μ_morComp`, `μ_morInv`), the groupoid `toGroupoidStr`, and **the ep-groupoid
  `E.toEpGroupoid : EpGroupoid W (pullbackSpace P X.src)`** (objects `W[0]`, morphisms
  `𝐖[0] = 𝐗 ₛ×_P W`), with Definition 7.1.3 (2017: 7.3) (3) `exists_isProperMap_tgt` and (4)
  `isScSmoothCompSheet_toGroupoidStr`; `isStrongBundleMap_src`, `isStrongBundleMap_tgt`
  (`s_𝐖`, `t_𝐖` strong bundle maps covering `s`, `t`); the sc-smooth functor
  `projFunctor : EpFunctor E.toEpGroupoid X` (`(P, π₁)`); `exists_isomorphic_of_isomorphic` (the
  orbit of `w` covers that of `P(w)`), `surjective_orbitMap_projFunctor`,
  `continuous_orbitMap_projFunctor` (`|P|`).
* The pull-back at level `[1]`: `StrongBundle.pullbackProj'One`,
  `StrongBundle.isScSmoothMap_to_pullback_one` (**the universal property of `f*Y[1]`**);
  `pullbackFiberLinearEquiv`, `fiberCast`, `isLinearMap_fiberRestrict_pullbackMap` (maps
  `(z, y) ↦ (g(z), Φ(y))` of pull-backs are linear on the fibres).
* **Definition 8.3.3 (2017: 8.6)**: `EpStrongBundle.IsStrongBundleFunctor E E' ϕ Φ`; `projFunctor_comp`
  (`(P', π₁') ∘ Φ = ϕ ∘ (P, π₁)`), `IsStrongBundleFunctor.mor_val` (`Φ(γ, w) = (ϕ(γ), Φ(w))`),
  `IsStrongBundleFunctor.isMap` (8.6 ⇒ 8.5), `liftMor`, `IsMap.liftFunctor` and
  `IsMap.isStrongBundleFunctor_liftFunctor` (8.5 ⇒ 8.6), `IsStrongBundleFunctor.eq_liftFunctor`,
  and **`EpStrongBundle.isMap_iff_strongBundleFunctor`** (the equivalence, with uniqueness of the
  functor).
* **Definition 8.3.4 (2017: 8.7), the claims**: Part I's operations:
  `StrongBundle.isScSmoothSection_of_principal`,
  `IsScSmoothSection.sectionAdd_of_isScSmoothSection` (the sum of two sc-smooth sections),
  `IsScSmoothSection.sectionSmul_const`, `isScSmoothSection_fiberZero`; then
  `fiberZero_mem_sectionFunctors`, `sectionAdd_mem_sectionFunctors`,
  `sectionSmul_mem_sectionFunctors` (**`Γ(P, μ)` is a vector space** of sections),
  `plusSectionFunctors_subset`, `fiberZero_mem_plusSectionFunctors`,
  `sectionAdd_mem_plusSectionFunctors`, `sectionSmul_mem_plusSectionFunctors` (**`Γ⁺ ⊆ Γ` a
  subspace**), `fredholmSectionFunctors_subset`.
* **Definition 8.5.9 (2017: 8.10)**: `StrongBundle.IsStrongBundleIsoOn` (a strong bundle map restricting to a
  strong bundle isomorphism `Y|U → Y'|U'`) with `IsStrongBundleIsoOn.fiberEquiv`;
  `EpFunctor.fibredSnd`, `isScSmoothMap_fibredSnd`, `EpStrongBundle.fibredLift`,
  `fibredBundleEquiv` (the text's `𝐕 ₛ×_A W` as a pull-back), `pullbackProj_fibredLift`,
  `pullbackProj_fibredBundleEquiv`, `fibredBundleEquiv_symm_fibredLift`, and
  **`EpStrongBundle.IsProperStrongBundleCovering EW EV F A`**.
* **§8.5.2**: `IsProperStrongBundleCovering.mor_val` (`A(φ, w) = (F(φ), A_{s(φ)}(w))`),
  `IsProperStrongBundleCovering.fiberEquiv` (`A_y` a topological linear isomorphism),
  `IsStrongBundleFunctor.μ_comm`, and **`EpStrongBundle.section_8_5_2`**
  (`μ_X(F(φ)) ∘ A_{s(φ)} = A_{t(φ)} ∘ μ_Y(φ)`).

## What the text leaves implicit, and the choices made

* "Strong bundle map" between strong bundles over M-polyfolds is not defined in Part I (only
  between local models, Definition 2.6.1 (2017: 2.22) [2.47]); we use `StrongBundle.IsStrongBundleMap`: covering,
  linear on the fibres, sc-smooth on `[0]` and on `[1]` (a reading; `StrongBundleMap.lean`).
* The M-polyfold structure of `𝐗 ₛ×_P W` is that of the pull-back strong bundle (`[0]`).
* The membership proofs `s(ψ) = P(w)` are carried by the points of `pullbackSpace P X.src`; in
  (2) and (3) they are supplied from the laws of `X` and from `P ∘ μ = t ∘ π₁`.
* **"We can define the ep-groupoid"** (p. 271) is asserted without proof; Definition 7.1.3 (2017: 7.3) is proved
  here for `(W, 𝐖)` (`toEpGroupoid`): (1) `s_𝐖` is the pull-back projection along the local
  sc-diffeomorphism `s` (`isLocalScDiffeo_pullbackProj'`), `t_𝐖 = μ` is one by Definition 8.3.1 (2017: 8.4) (1);
  (2) `u_𝐖`, `ι_𝐖` by the universal property of the pull-back; (3) with `V = P⁻¹(V(P w))`, by
  sequences, the properness of `X`, the continuity of `μ` and `w = μ(ψ⁻¹, μ(ψ, w))`; (4) in sheet
  form, through a sheet of `s` near each point and condition (4) of `X`.  The groupoid laws use
  Definition 8.3.1 (2017: 8.4) (2), (3).  The multiplication of `𝐖` is total, with the junk value `(γ, w)` off
  composable pairs (as Chapter 7's `GroupoidStr.comp`); it does not involve `μ`.
* **Universes**: an `EpGroupoid` has objects and morphisms in one universe, so from the functorial
  picture on `W` lives in the universe of the objects and morphisms of `X` (Definitions 8.3.1, 8.3.2 (2017: 8.4, 8.5),
  8.7 above are universe polymorphic).  The paracompactness of `𝐗 ₛ×_P W` is an instance argument
  `[ParacompactSpace (pullbackSpace P X.src)]` there, supplied by
  `B.paracompactSpace_pullback X.PMor X.src`; it is a `Prop`, so it agrees with the instance used
  inside `EpStrongBundle`.
* **Definition 8.3.3 (2017: 8.6)**: "linear on the fibers", "covers `ϕ`" and "induces strong bundle maps" are read
  together as the two conditions `IsStrongBundleMap` on objects (`P`, `P'`, covering `ϕ` on
  objects; this is the square `P' ∘ Φ = ϕ ∘ P`) and on morphisms (the pull-back bundles
  `𝐖 → 𝐗`, `𝐖' → 𝐗'`, covering `ϕ` on morphisms).  The `[1]`-smoothness of the lifted morphism
  map needs the universal property of the pull-back at level `[1]`, proved here.  "Strong bundle
  functor" (Definition 8.3.3 (2017: 8.6)) and "strong bundle map" (Definition 8.3.2 (2017: 8.5)) are identical notions in the
  text; the equivalence is `isMap_iff_strongBundleFunctor`.
* **Definition 8.3.4 (2017: 8.7), "the vector space `Γ(P, μ)`"**: the operations are Part I's fibrewise
  `sectionAdd`, `sectionSmul` (by a constant) and the zero section `fiberZero`; the closure of `Γ`,
  `Γ⁺` under them is proved, no `Module` structure on the set is built.  Part I proves the sum of an
  sc-smooth and an sc⁺-section (Theorem 3.15); the sum of two sc-smooth sections and constant
  multiples are proved here, in the charts.
* **Definition 8.5.9 (2017: 8.10)**: `A` is taken in the functorial picture, an sc-smooth functor
  `(W, 𝐖) → (V, 𝐕)` which is a strong bundle functor covering `F` (Definition 8.3.3 (2017: 8.6); equivalently,
  by `isMap_iff_strongBundleFunctor`, its object map is a strong bundle map of Definition 8.3.2 (2017: 8.5)).
  "A local strong bundle isomorphism" is: every `y` has an open `U ∋ y` and an open `U'` with
  `A : W|U → V|U'` a strong bundle isomorphism covering `F : U → U'`; "`A : W|U(y) → V|U(x)` is a
  strong bundle isomorphism" is `IsStrongBundleIsoOn` (`F : U(y) → U(x)` an sc-diffeomorphism and
  `A : P⁻¹(U(y)) → Q⁻¹(U(x))` an sc-diffeomorphism on `[0]` and on `[1]`; the inverse is then
  linear on the fibres).  The finiteness of `F⁻¹(x)` in (2) is part of `F.IsProperCovering`
  (Definition 8.5.1 (2017: 8.8) (2)) and is not repeated.  In (3) the text does not say which strong bundle
  structure `𝐕 ₛ×_A W → 𝐗 ₛ×_F Y` carries: it is read as the pull-back of `P : W → Y` along
  `pr₂ : 𝐗 ₛ×_F Y → Y`, `(φ, y) ↦ y`, on Part I's sub-M-polyfold `𝐗 ₛ×_F Y` of `𝐗 × Y` (as in
  Definition 8.5.1 (2017: 8.8) (3)); its points `((φ, y), w)` with `P(w) = y` correspond to the text's
  `((φ, v), w)` with `v = A(w)` (`fibredBundleEquiv`; under it the map is `fibredLift` and the
  projection is `((φ, v), w) ↦ (φ, P(w))`).  "Strong bundle isomorphism" is
  `StrongBundle.IsStrongBundleIso` (two inverse strong bundle maps, on `[0]` and `[1]`).
* **§8.5.2**: the natural transformation `μ_Y → μ_X ∘ F` of functors into `Ban` is stated as its
  naturality identity (`section_8_5_2`), the fibres `Q⁻¹(F(s φ))` and `Q⁻¹(s(F φ))` being
  identified through their values in `V`.  Only the strong bundle functor part of Definition 8.5.9 (2017: 8.10)
  enters (`IsStrongBundleFunctor.μ_comm`); (1) makes the `A_y` topological linear isomorphisms
  (`IsProperStrongBundleCovering.fiberEquiv`, through `IsStrongBundleIsoOn.fiberEquiv`).

## Not formalized

* No example of a proper strong bundle covering functor (Definition 8.5.9 (2017: 8.10)) is constructed in this
  file.
-/

open Set Function

noncomputable section

namespace Polyfold

universe u v

section Defs

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The point `(1_{P w}, w)` of `𝐗 ₛ×_P W`. -/
def EpGroupoid.unitPair (w : W) : pullbackSpace P X.src :=
  ⟨(X.unit (P w), w), (X.src_unit (P w)).symm⟩

/-- **Definition 8.3.1 (2017: 8.4) (strong bundle over an ep-groupoid)**: for a strong bundle `B` over the
object M-polyfold, a structure map `μ : 𝐗 ₛ×_P W → W` which is a strong bundle map covering `t`
(from the pull-back strong bundle `𝐗 ₛ×_P W → 𝐗`), with (1) `μ` a surjective local
sc-diffeomorphism (and linear on the fibres, part of `IsStrongBundleMap`), (2) `μ(1_x, w) = w`,
(3) `μ(ψ ∘ γ, w) = μ(ψ, μ(γ, w))` for `s(γ) = P(w)`, `t(γ) = s(ψ)`. -/
structure EpStrongBundle (B : StrongBundle X.PObj P) where
  /-- The structure map `μ(ψ, w) ∈ W_{t(ψ)}` for `w ∈ W_{s(ψ)}`. -/
  μ : pullbackSpace P X.src → W
  isStrongBundleMap :
    haveI := B.paracompactSpace_pullback X.PMor X.src
    (B.pullback X.isScSmoothMap_src).IsStrongBundleMap B X.tgt μ
  surjective : Surjective μ
  isLocalScDiffeo :
    haveI := B.paracompactSpace_pullback X.PMor X.src
    (B.pullback X.isScSmoothMap_src).toMPolyfold0.IsLocalScDiffeo B.toMPolyfold0 μ
  μ_unit : ∀ w, μ (X.unitPair w) = w
  μ_comp : ∀ (ψ γ : Mor) (w : W) (h₁ : P w = X.src γ) (h₂ : X.src ψ = X.tgt γ),
    μ ⟨(X.comp ψ γ, w), h₁.trans (X.src_comp ψ γ h₂).symm⟩ =
      μ ⟨(ψ, μ ⟨(γ, w), h₁⟩), by
        have := B.paracompactSpace_pullback X.PMor X.src
        exact (isStrongBundleMap.covers ⟨(γ, w), h₁⟩).trans h₂.symm⟩

namespace EpStrongBundle

variable {X} {B : StrongBundle X.PObj P} (E : EpStrongBundle X B)

/-- `P ∘ μ = t ∘ π₁`. -/
theorem P_μ (q : pullbackSpace P X.src) : P (E.μ q) = X.tgt q.1.1 := by
  have := B.paracompactSpace_pullback X.PMor X.src
  exact E.isStrongBundleMap.covers q

/-- The pair `(ψ, f(s ψ))` for a section `f` of `P`. -/
def sectionPair {f : Obj → W} (hf : IsSection P f) (ψ : Mor) : pullbackSpace P X.src :=
  ⟨(ψ, f (X.src ψ)), hf (X.src ψ)⟩

/-- The functorial condition of Definition 8.3.4 (2017: 8.7): `f(t φ) = μ(φ, f(s φ))` for every morphism. -/
def IsFunctorialSection {f : Obj → W} (hf : IsSection P f) : Prop :=
  ∀ φ : Mor, f (X.tgt φ) = E.μ (sectionPair hf φ)

/-- **Definition 8.3.4 (2017: 8.7) (1)**: an sc-smooth section functor. -/
def IsScSmoothSectionFunctor (f : Obj → W) : Prop :=
  ∃ hf : B.IsScSmoothSection f, E.IsFunctorialSection hf.1

/-- **Definition 8.3.4 (2017: 8.7) (2)**: an sc⁺-section functor: an sc-smooth section functor with values in
`W_{0,1}`, sc-smooth as a section of `W[1] → X` (Part I's `IsScPlusSection`). -/
def IsScPlusSectionFunctor (f : Obj → W) : Prop :=
  E.IsScSmoothSectionFunctor f ∧ B.IsScPlusSection f

/-- **Definition 8.3.4 (2017: 8.7) (3)**: an sc-Fredholm section functor: an sc-smooth section functor which is
an sc-Fredholm section of `W → X` (Part I's Definition 3.14 [3.8], germ reading). -/
def IsScFredholmSectionFunctor (f : Obj → W) : Prop :=
  E.IsScSmoothSectionFunctor f ∧ B.IsScFredholmSection f

/-- `Γ(P, μ)`, the sc-smooth section functors (Definition 8.3.4 (2017: 8.7) (1)). -/
def sectionFunctors : Set (Obj → W) := {f | E.IsScSmoothSectionFunctor f}

/-- `Γ⁺(P, μ)` (Definition 8.3.4 (2017: 8.7) (2)). -/
def plusSectionFunctors : Set (Obj → W) := {f | E.IsScPlusSectionFunctor f}

/-- `Fred(P, μ)` (Definition 8.3.4 (2017: 8.7) (3)). -/
def fredholmSectionFunctors : Set (Obj → W) := {f | E.IsScFredholmSectionFunctor f}

end EpStrongBundle

end Defs

section Maps

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type v} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}

/-- **Definition 8.3.2 (2017: 8.5) (strong bundle map)** between strong bundles `(P, μ)` over `X` and
`(P', μ')` over `X'`: a strong bundle map `Φ : W → W'` covering the object map of an sc-smooth
functor `ϕ : X → X'` with `Φ(μ(γ, w)) = μ'(ϕ(γ), Φ(w))` for `s(γ) = P(w)`. -/
structure EpStrongBundle.IsMap (E : EpStrongBundle X B) (E' : EpStrongBundle X' B')
    (ϕ : EpFunctor X X') (Φ : W → W') : Prop where
  isStrongBundleMap : B.IsStrongBundleMap B' ϕ.obj Φ
  map_μ : ∀ (γ : Mor) (w : W) (h : P w = X.src γ),
    Φ (E.μ ⟨(γ, w), h⟩) = E'.μ ⟨(ϕ.mor γ, Φ w), by
      change P' (Φ w) = X'.src (ϕ.mor γ)
      rw [isStrongBundleMap.covers w, h, ϕ.src_mor γ]⟩

end Maps

/-! ### The pull-back at level `[1]` -/

section PullbackOne

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {f : Z → X} [ParacompactSpace (pullbackSpace P f)]
  {V : Type*} [TopologicalSpace V] [T2Space V] [ParacompactSpace V] {Q : MPolyfold V}

namespace StrongBundle

variable (B : StrongBundle PX P) (hf : PZ.IsScSmoothMap PX f)

/-- `P'[1] : f*Y[1] → Y[1]`, `(z, y) ↦ y`. -/
abbrev pullbackProj'One : (B.pullback hf).One → B.One :=
  oneRestrict (B.pullback hf) B (pullbackProj' P f) (B.mapsTo_oneSet_pullbackProj' hf)

/-- **The universal property of the pull-back at level `[1]`**: a map `ι : V → f*Y[1]` is
sc-smooth as soon as its components `P_f ∘ ι : V → Z` and `P'[1] ∘ ι : V → Y[1]` are (in the
charts, `Φ_f[1] ∘ ι = (ψ ∘ P_f ∘ ι, pr_{F¹} Φ[1] ∘ P'[1] ∘ ι)`). -/
theorem isScSmoothMap_to_pullback_one {ι : V → (B.pullback hf).One}
    (ha : Q.IsScSmoothMap PZ (pullbackProj P f ∘ (B.pullback hf).oneVal ∘ ι))
    (hb : Q.IsScSmoothMap B.toMPolyfold1 (B.pullbackProj'One hf ∘ ι)) :
    Q.IsScSmoothMap (B.pullback hf).toMPolyfold1 ι := by
  refine MPolyfold.isScSmoothMap_of_forall_charts fun v => ?_
  obtain ⟨d, hd, hq⟩ := PullbackChartData.exists_mem_atlas B hf ((B.pullback hf).oneVal (ι v))
  have hmem := B.toChart_mem_pullback_atlas hf hd ((B.pullback hf).oneVal (ι v))
  obtain ⟨φ, hφ, hvφ⟩ := Q.exists_isChart_mem_source v
  have hac : Continuous (pullbackProj P f ∘ (B.pullback hf).oneVal ∘ ι) :=
    continuousOn_univ.1 ha.continuousOn
  have hso : IsOpen (φ.source ∩ (pullbackProj P f ∘ (B.pullback hf).oneVal ∘ ι) ⁻¹' d.ψ.source) :=
    φ.isOpen_source.inter (d.ψ.isOpen_source.preimage hac)
  set φ' := φ.restrict inter_subset_left hso with hφ'def
  have hφ' : Q.IsChart φ' := MPolyfold.IsChart.restrict Q hφ inter_subset_left hso
  set y' := B.pullbackProj'One hf (ι v)
  refine ⟨φ', oneChart hmem (ι v), hφ', (B.pullback hf).isChart_oneChart hmem (ι v), ⟨hvφ, hq⟩,
    fun x hx => hx.2, ?_⟩
  have h1 := ha.smooth φ' d.ψ hφ' d.isChart φ'.source φ'.isOpen_source
    (fun x hx => ⟨mem_univ _, hx⟩) fun x hx => hx.2
  have h2 := hb.smooth φ' (oneChart hd y') hφ' (B.isChart_oneChart hd y') φ'.source
    φ'.isOpen_source (fun x hx => ⟨mem_univ _, hx⟩) fun x hx => d.mem_c_source hx.2
  have h3 : IsScSmoothRetractMap (d.c.φ.model.E.prod d.c.F.shift) (d.c.φ.model.C ×ˢ univ)
      (strongShiftOne d.c.K) d.c.F.shift univ univ Prod.snd :=
    (d.c.φ.model.E.prodSndOp d.c.F.shift).isScSmoothRetractMap d.c.isScRetract_one
      (mapsTo_univ _ _)
  have h4 := h3.comp h2 d.c.isScRetract_one
  rw [φ'.image_source] at h1 h4
  refine (IsScSmoothRetractMap.scPair h1 h4 ?_).congr fun _ _ => rfl
  intro z hz
  obtain ⟨x, hx, rfl⟩ : z ∈ φ' '' φ'.source := by rw [φ'.image_source]; exact hz
  change (oneChart hmem (ι v)) (ι (φ'.symm (φ' x))) ∈ strongShiftOne (d.toChart _).K
  rw [φ'.symm_apply_apply hx]
  exact (oneChart hmem (ι v)).toPartialEquiv.map_source
    (show ι x ∈ (oneChart hmem (ι v)).source from hx.2)

end StrongBundle

end PullbackOne

/-! ### The fibre maps `μ(ψ, ·) : W_{s(ψ)} → W_{t(ψ)}` -/

section FiberMaps

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  (E : EpStrongBundle X B)

namespace EpStrongBundle

/-- `μ` only depends on the underlying pair. -/
theorem μ_congr {q q' : pullbackSpace P X.src} (h : (q : Mor × W) = q') : E.μ q = E.μ q' :=
  congrArg E.μ (Subtype.ext h)

theorem continuous_μ : Continuous E.μ := by
  have := B.paracompactSpace_pullback X.PMor X.src
  exact E.isStrongBundleMap.continuous

/-- `μ(ψ⁻¹, μ(ψ, w)) = w`. -/
theorem μ_inv_μ (q : pullbackSpace P X.src) (h : P (E.μ q) = X.src (X.inv (q : Mor × W).1)) :
    E.μ ⟨(X.inv (q : Mor × W).1, E.μ q), h⟩ = (q : Mor × W).2 := by
  obtain ⟨⟨ψ, w⟩, hq⟩ := q
  have hq' : P w = X.src ψ := hq
  rw [← E.μ_comp (X.inv ψ) ψ w hq' (X.src_inv ψ)]
  refine (E.μ_congr ?_).trans (E.μ_unit w)
  change (X.comp (X.inv ψ) ψ, w) = (X.unit (P w), w)
  rw [X.inv_comp, hq']

/-- `μ(ψ, μ(ψ⁻¹, w)) = w`. -/
theorem μ_μ_inv (ψ : Mor) (w : W) (h : P w = X.src (X.inv ψ)) (h' : P (E.μ ⟨(X.inv ψ, w), h⟩) =
    X.src ψ) : E.μ ⟨(ψ, E.μ ⟨(X.inv ψ, w), h⟩), h'⟩ = w := by
  rw [← E.μ_comp ψ (X.inv ψ) w h (X.tgt_inv ψ).symm]
  refine (E.μ_congr ?_).trans (E.μ_unit w)
  change (X.comp ψ (X.inv ψ), w) = (X.unit (P w), w)
  rw [X.comp_inv, h, X.src_inv]

/-- **The fibre map `μ(ψ, ·) : W_{s(ψ)} → W_{t(ψ)}`** (p. 271), a bounded linear operator: the
fibre map of the strong bundle map `μ` over `ψ`, after the identification of the fibre of
`𝐗 ₛ×_P W → 𝐗` over `ψ` with `W_{s(ψ)}`. -/
def fiberMor (ψ : Mor) : P ⁻¹' {X.src ψ} →L[ℝ] P ⁻¹' {X.tgt ψ} :=
  haveI := B.paracompactSpace_pullback X.PMor X.src
  (E.isStrongBundleMap.fiberMap ψ).comp
    ((pullbackFiberCLE (P := P) (f := X.src) ψ).symm : P ⁻¹' {X.src ψ} →L[ℝ] _)

@[simp] lemma fiberMor_apply (ψ : Mor) (v : P ⁻¹' {X.src ψ}) :
    (E.fiberMor ψ v : W) = E.μ ⟨(ψ, v), v.2⟩ := rfl

/-- `μ(ψ, v + v') = μ(ψ, v) + μ(ψ, v')` in `W_{t(ψ)}`. -/
theorem μ_add (ψ : Mor) (v v' : P ⁻¹' {X.src ψ}) :
    E.μ ⟨(ψ, ((v + v' : P ⁻¹' {X.src ψ}) : W)), (v + v').2⟩ =
      ((⟨E.μ ⟨(ψ, v), v.2⟩, (E.fiberMor ψ v).2⟩ + ⟨E.μ ⟨(ψ, v'), v'.2⟩, (E.fiberMor ψ v').2⟩ :
        P ⁻¹' {X.tgt ψ}) : W) :=
  congrArg Subtype.val ((E.fiberMor ψ).map_add v v')

/-- `μ(ψ, a • v) = a • μ(ψ, v)` in `W_{t(ψ)}`. -/
theorem μ_smul (ψ : Mor) (a : ℝ) (v : P ⁻¹' {X.src ψ}) :
    E.μ ⟨(ψ, ((a • v : P ⁻¹' {X.src ψ}) : W)), (a • v).2⟩ =
      ((a • ⟨E.μ ⟨(ψ, v), v.2⟩, (E.fiberMor ψ v).2⟩ : P ⁻¹' {X.tgt ψ}) : W) :=
  congrArg Subtype.val ((E.fiberMor ψ).map_smul a v)

/-- **`μ(ψ, ·) : W_x → W_y` is a linear isomorphism for `ψ : x → y`** (p. 271, "it follows, in
particular"), with inverse `μ(ψ⁻¹, ·)`, by (2) and (3) of Definition 8.3.1 (2017: 8.4). -/
def fiberMorEquiv (ψ : Mor) : P ⁻¹' {X.src ψ} ≃L[ℝ] P ⁻¹' {X.tgt ψ} where
  toLinearMap := (E.fiberMor ψ).toLinearMap
  invFun v := ⟨E.μ ⟨(X.inv ψ, v), v.2.trans (X.src_inv ψ).symm⟩, by
    change P (E.μ _) = X.src ψ; rw [E.P_μ]; exact X.tgt_inv ψ⟩
  left_inv v := Subtype.ext (E.μ_inv_μ ⟨(ψ, v), v.2⟩ _)
  right_inv v := Subtype.ext (E.μ_μ_inv ψ v _ _)
  continuous_toFun := (E.fiberMor ψ).continuous
  continuous_invFun := by
    refine (E.continuous_μ.comp ?_).subtype_mk _
    exact ((continuous_const.prodMk continuous_subtype_val).subtype_mk _)

@[simp] lemma fiberMorEquiv_apply (ψ : Mor) (v : P ⁻¹' {X.src ψ}) :
    (E.fiberMorEquiv ψ v : W) = E.μ ⟨(ψ, v), v.2⟩ := rfl

end EpStrongBundle

end FiberMaps

/-! ### The functorial picture: the ep-groupoid `(W, 𝐖)` (pp. 271–272) -/

section Functorial

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  (E : EpStrongBundle X B)

namespace EpStrongBundle

/-- The inverse `ι_𝐖(ψ, w) = (ψ⁻¹, μ(ψ, w))` (p. 272). -/
def morInv (q : pullbackSpace P X.src) : pullbackSpace P X.src :=
  ⟨(X.inv (q : Mor × W).1, E.μ q), (E.P_μ q).trans (X.src_inv _).symm⟩

open scoped Classical in
/-- The multiplication `(ψ, w') ∘ (γ, w) = (ψ ∘ γ, w)` for `w' = μ(γ, w)` (p. 272); the junk
value `(γ, w)` off composable pairs (as Chapter 7's total `GroupoidStr.comp`); it does not
involve `μ`. -/
def morComp (q' q : pullbackSpace P X.src) : pullbackSpace P X.src :=
  if h : P (q : Mor × W).2 = X.src (X.comp (q' : Mor × W).1 (q : Mor × W).1) then
    ⟨(X.comp (q' : Mor × W).1 (q : Mor × W).1, (q : Mor × W).2), h⟩
  else q

variable {E}

/-- For `w' = μ(γ, w)`, `s(ψ) = t(γ)`. -/
theorem src_eq_tgt_of_eq_μ {q' q : pullbackSpace P X.src} (h : (q' : Mor × W).2 = E.μ q) :
    X.src (q' : Mor × W).1 = X.tgt (q : Mor × W).1 := by
  rw [← (q'.2 : P (q' : Mor × W).2 = X.src (q' : Mor × W).1), h, E.P_μ]

theorem morComp_val {q' q : pullbackSpace P X.src} (h : (q' : Mor × W).2 = E.μ q) :
    (morComp q' q : Mor × W) = (X.comp (q' : Mor × W).1 (q : Mor × W).1, (q : Mor × W).2) := by
  have hc : P (q : Mor × W).2 = X.src (X.comp (q' : Mor × W).1 (q : Mor × W).1) :=
    (q.2 : P (q : Mor × W).2 = X.src (q : Mor × W).1).trans
      (X.src_comp _ _ (src_eq_tgt_of_eq_μ h)).symm
  unfold morComp; rw [dif_pos hc]

/-- `t_𝐖((ψ, w') ∘ (γ, w)) = μ(ψ ∘ γ, w) = μ(ψ, μ(γ, w)) = t_𝐖(ψ, w')` (Definition 8.3.1 (2017: 8.4) (3)). -/
theorem μ_morComp {q' q : pullbackSpace P X.src} (h : (q' : Mor × W).2 = E.μ q) :
    E.μ (morComp q' q) = E.μ q' := by
  obtain ⟨⟨γ, w⟩, hq⟩ := q
  obtain ⟨⟨ψ, w'⟩, hq'⟩ := q'
  have h' : w' = E.μ ⟨(γ, w), hq⟩ := h
  subst h'
  have hq₁ : P w = X.src γ := hq
  calc E.μ (morComp _ _) = E.μ ⟨(X.comp ψ γ, w),
        hq₁.trans (X.src_comp ψ γ (src_eq_tgt_of_eq_μ h)).symm⟩ := E.μ_congr (morComp_val h)
    _ = _ := E.μ_comp ψ γ w hq₁ (src_eq_tgt_of_eq_μ h)

theorem μ_morInv (q : pullbackSpace P X.src) : E.μ (E.morInv q) = (q : Mor × W).2 :=
  E.μ_inv_μ q _

variable (E)

/-- **The groupoid `(W, 𝐖)`** (p. 272): objects `W`, morphisms `𝐖 = 𝐗 ₛ×_P W`,
`s_𝐖(ψ, w) = w`, `t_𝐖(ψ, w) = μ(ψ, w)`, `1_w = (1_{P(w)}, w)`, `(ψ, w)⁻¹ = (ψ⁻¹, μ(ψ, w))`,
`(ψ, w') ∘ (γ, w) = (ψ ∘ γ, w)` for `w' = μ(γ, w)`. -/
def toGroupoidStr : GroupoidStr W (pullbackSpace P X.src) where
  src := pullbackProj' P X.src
  tgt := E.μ
  comp := morComp
  unit := X.unitPair
  inv := E.morInv
  src_comp φ ψ h := by
    change (morComp φ ψ : Mor × W).2 = (ψ : Mor × W).2
    rw [morComp_val h]
  tgt_comp φ ψ h := μ_morComp h
  comp_assoc φ ψ χ h₁ h₂ := by
    have h₁' : (φ : Mor × W).2 = E.μ ψ := h₁
    have h₂' : (ψ : Mor × W).2 = E.μ χ := h₂
    have h₃ : (morComp φ ψ : Mor × W).2 = E.μ χ := by rw [morComp_val h₁']; exact h₂'
    have h₄ : (φ : Mor × W).2 = E.μ (morComp ψ χ) := by rw [μ_morComp h₂']; exact h₁'
    apply Subtype.ext
    rw [morComp_val h₃, morComp_val h₁', morComp_val h₄, morComp_val h₂',
      X.comp_assoc _ _ _ (src_eq_tgt_of_eq_μ h₁') (src_eq_tgt_of_eq_μ h₂')]
  src_unit _ := rfl
  tgt_unit w := E.μ_unit w
  comp_unit φ := by
    have h0 : (φ : Mor × W).2 = E.μ (X.unitPair (pullbackProj' P X.src φ)) := (E.μ_unit _).symm
    apply Subtype.ext
    rw [morComp_val h0]
    change (X.comp (φ : Mor × W).1 (X.unit (P (φ : Mor × W).2)), (φ : Mor × W).2) = φ
    rw [GroupoidStr.comp_unit_of_eq (φ.2 : P (φ : Mor × W).2 = X.src (φ : Mor × W).1).symm]
  unit_comp φ := by
    apply Subtype.ext
    rw [morComp_val rfl]
    change (X.comp (X.unit (P (E.μ φ))) (φ : Mor × W).1, (φ : Mor × W).2) = φ
    rw [GroupoidStr.unit_comp_of_eq (E.P_μ φ).symm]
  src_inv _ := rfl
  tgt_inv φ := μ_morInv φ
  comp_inv φ := by
    apply Subtype.ext
    rw [morComp_val (μ_morInv φ).symm]
    change (X.comp (φ : Mor × W).1 (X.inv (φ : Mor × W).1), E.μ φ) = (X.unit (P (E.μ φ)), E.μ φ)
    rw [X.comp_inv, E.P_μ]
  inv_comp φ := by
    apply Subtype.ext
    rw [morComp_val rfl]
    change (X.comp (X.inv (φ : Mor × W).1) (φ : Mor × W).1, (φ : Mor × W).2) =
      (X.unit (P (φ : Mor × W).2), (φ : Mor × W).2)
    rw [X.inv_comp, (φ.2 : P (φ : Mor × W).2 = X.src (φ : Mor × W).1)]

@[simp] lemma toGroupoidStr_src : E.toGroupoidStr.src = pullbackProj' P X.src := rfl
@[simp] lemma toGroupoidStr_tgt : E.toGroupoidStr.tgt = E.μ := rfl
@[simp] lemma toGroupoidStr_comp : E.toGroupoidStr.comp = morComp := rfl
@[simp] lemma toGroupoidStr_unit : E.toGroupoidStr.unit = X.unitPair := rfl
@[simp] lemma toGroupoidStr_inv : E.toGroupoidStr.inv = E.morInv := rfl

end EpStrongBundle

end Functorial

section FunctorialEp

open Filter Topology

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B)

namespace EpStrongBundle

/-- Definition 7.1.3 (2017: 7.3) (3) for `(W, 𝐖)`: for `V = P⁻¹(V(P w))`, `t_𝐖 : s_𝐖⁻¹(cl V) → W` is proper.  A
sequence `(ψ_n, w_n)` with `w_n ∈ cl V` and `μ(ψ_n, w_n) → y` has `t(ψ_n) → P(y)` and
`s(ψ_n) ∈ cl V(P w)`, so a subsequence `ψ_n → ψ₀` by properness of `X`, and then
`w_n = μ(ψ_n⁻¹, μ(ψ_n, w_n)) → μ(ψ₀⁻¹, y)`. -/
theorem exists_isProperMap_tgt (w : W) : ∃ V : Set W, IsOpen V ∧ w ∈ V ∧
    IsProperMap ((pullbackProj' P X.src ⁻¹' closure V).domRestrict E.μ) := by
  obtain ⟨V, hVo, hxV, hprop⟩ := X.exists_isProperMap (P w)
  refine ⟨P ⁻¹' V, hVo.preimage B.continuous, hxV, ?_⟩
  have hμc := E.continuous_μ
  rw [MPolyfold.isProperMap_domRestrict_iff (B.pullback X.isScSmoothMap_src).toMPolyfold0
    B.toMPolyfold0 hμc]
  intro φ y hφ hy
  have hcl : closure (P ⁻¹' V) ⊆ P ⁻¹' closure V :=
    closure_minimal (preimage_mono subset_closure) (isClosed_closure.preimage B.continuous)
  have hs : ∀ n, X.src ((φ n : Mor × W).1) ∈ closure V := fun n => by
    rw [← ((φ n).2 : P (φ n : Mor × W).2 = X.src (φ n : Mor × W).1)]; exact hcl (hφ n)
  have ht : Tendsto (X.tgt ∘ fun n => (φ n : Mor × W).1) atTop (𝓝 (P y)) :=
    ((B.continuous.tendsto y).comp hy).congr fun n => E.P_μ (φ n)
  obtain ⟨ψ₀, -, hψ₀t, k, hk, hkt⟩ :=
    MPolyfold.exists_tendsto_subseq_of_isProperMap_domRestrict X.PMor hprop hs ht
  let q₀ : pullbackSpace P X.src := ⟨(X.inv ψ₀, y), by
    change P y = X.src (X.inv ψ₀); rw [X.src_inv, hψ₀t]⟩
  have hq : Tendsto (fun n => E.morInv (φ (k n))) atTop (𝓝 q₀) := by
    rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
    exact ((X.continuous_inv.tendsto ψ₀).comp hkt).prodMk_nhds (hy.comp hk.tendsto_atTop)
  have hw : Tendsto (fun n => (φ (k n) : Mor × W).2) atTop (𝓝 (E.μ q₀)) :=
    ((hμc.tendsto q₀).comp hq).congr fun n => μ_morInv (φ (k n))
  let r₀ : pullbackSpace P X.src := ⟨(ψ₀, E.μ q₀), by
    change P (E.μ q₀) = X.src ψ₀; rw [E.P_μ]; exact X.tgt_inv ψ₀⟩
  refine ⟨r₀, ?_, k, hk, ?_⟩
  · exact isClosed_closure.mem_of_tendsto hw (Eventually.of_forall fun n => hφ (k n))
  · rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
    exact hkt.prodMk_nhds hw

/-- Definition 7.1.3 (2017: 7.3) (4) for `(W, 𝐖)`, in sheet form: for a sheet `σ` of `s_𝐖`,
`(ψ, w) ↦ σ(μ(ψ, w)) ∘ (ψ, w) = (σ(μ(ψ, w))₁ ∘ ψ, w)` is sc-smooth on `μ⁻¹(V)`.  Near a point,
`σ(μ(ψ, w))₁` lies in a sheet `U'` of `s` with inverse `σ'`, so equals `σ'(t ψ)`, and
`ψ ↦ σ'(t ψ) ∘ ψ` is sc-smooth by condition (4) of `X`. -/
theorem isScSmoothCompSheet_toGroupoidStr :
    IsScSmoothCompSheet B.toMPolyfold0 (B.pullback X.isScSmoothMap_src).toMPolyfold0
      (pullbackProj' P X.src) E.μ morComp := by
  intro σ U V hd
  have hμc := E.continuous_μ
  have hVo : IsOpen (E.μ ⁻¹' V) := hd.isScSmoothOn_inv.isOpen.preimage hμc
  have hσc : ContinuousOn (fun q => (σ (E.μ q) : Mor × W).1) (E.μ ⁻¹' V) :=
    (continuous_fst.comp continuous_subtype_val).comp_continuousOn
      (hd.isScSmoothOn_inv.continuousOn.comp hμc.continuousOn fun q hq => hq)
  refine MPolyfold.IsScSmoothOn.of_locally hVo fun q hq => ?_
  obtain ⟨U', V', σ', hU', hd'⟩ := X.isLocalScDiffeo_src (σ (E.μ q) : Mor × W).1
  have hNo := hσc.isOpen_inter_preimage hVo hd'.isScSmoothOn.isOpen
  refine ⟨_, hNo, ⟨hq, hU'⟩, inter_subset_left, ?_⟩
  have hX := X.isScSmoothCompSheet σ' U' V' hd'
  have hmaps : MapsTo (pullbackProj P X.src) (E.μ ⁻¹' V ∩
      (fun q => (σ (E.μ q) : Mor × W).1) ⁻¹' U') (X.tgt ⁻¹' V') := fun r hr => by
    change X.tgt (r : Mor × W).1 ∈ V'
    rw [← src_eq_tgt_of_eq_μ (hd.right_inv _ hr.1)]
    exact hd'.mapsTo hr.2
  refine B.isScSmoothOn_to_pullback_of_eqOn X.isScSmoothMap_src
    (a := fun r => X.comp (σ' (X.tgt (r : Mor × W).1)) (r : Mor × W).1)
    (b := fun r => (r : Mor × W).2)
    (MPolyfold.IsScSmoothOn.comp hX
      ((B.isScSmoothMap_pullbackProj X.isScSmoothMap_src).mono hNo (subset_univ _)) hmaps)
    ((B.isScSmoothMap_pullbackProj' X.isScSmoothMap_src).mono hNo (subset_univ _)) ?_
  intro r hr
  have h1 : (σ (E.μ r) : Mor × W).2 = E.μ r := hd.right_inv _ hr.1
  rw [morComp_val h1]
  have h3 : σ' (X.tgt (r : Mor × W).1) = (σ (E.μ r) : Mor × W).1 := by
    rw [← src_eq_tgt_of_eq_μ h1]; exact hd'.left_inv _ hr.2
  rw [h3]

/-- **The ep-groupoid `(W, 𝐖)` of a strong bundle over an ep-groupoid** (pp. 271–272; "we can
define the ep-groupoid", stated without proof in the text): the groupoid `toGroupoidStr` with the
M-polyfolds `W[0]` and `𝐖[0] = 𝐗 ₛ×_P W[0]` (the pull-back strong bundle). -/
def toEpGroupoid : EpGroupoid W (pullbackSpace P X.src) where
  toGroupoidStr := E.toGroupoidStr
  PObj := B.toMPolyfold0
  PMor := (B.pullback X.isScSmoothMap_src).toMPolyfold0
  isLocalScDiffeo_src :=
    B.isLocalScDiffeo_pullbackProj' X.isScSmoothMap_src X.isLocalScDiffeo_src
  isLocalScDiffeo_tgt := E.isLocalScDiffeo
  isScSmoothMap_unit :=
    B.isScSmoothMap_pullbackPair X.isScSmoothMap_src (a := X.unit ∘ P) (b := id)
      (X.isScSmoothMap_unit.comp B.isScSmoothMap_proj) MPolyfold.isScSmoothMap_id
      fun w => (X.src_unit (P w)).symm
  isScSmoothMap_inv :=
    B.isScSmoothMap_pullbackPair X.isScSmoothMap_src (a := X.inv ∘ pullbackProj P X.src)
      (b := E.μ) (X.isScSmoothMap_inv.comp (B.isScSmoothMap_pullbackProj X.isScSmoothMap_src))
      E.isStrongBundleMap.isScSmoothMap fun q => (E.P_μ q).trans (X.src_inv _).symm
  exists_isProperMap := E.exists_isProperMap_tgt
  isScSmoothComp := (isScSmoothComp_iff_sheet _ _).2 E.isScSmoothCompSheet_toGroupoidStr

@[simp] lemma toEpGroupoid_src : E.toEpGroupoid.src = pullbackProj' P X.src := rfl
@[simp] lemma toEpGroupoid_tgt : E.toEpGroupoid.tgt = E.μ := rfl
@[simp] lemma toEpGroupoid_comp : E.toEpGroupoid.comp = morComp := rfl
@[simp] lemma toEpGroupoid_unit : E.toEpGroupoid.unit = X.unitPair := rfl
@[simp] lemma toEpGroupoid_inv : E.toEpGroupoid.inv = E.morInv := rfl
lemma toEpGroupoid_PObj : E.toEpGroupoid.PObj = B.toMPolyfold0 := rfl
lemma toEpGroupoid_PMor :
    E.toEpGroupoid.PMor = (B.pullback X.isScSmoothMap_src).toMPolyfold0 := rfl

/-- **The sc-smooth functor `P = (P, π₁) : (W, 𝐖) → (X, 𝐗)`** (p. 272). -/
def projFunctor : EpFunctor E.toEpGroupoid X where
  obj := P
  mor := pullbackProj P X.src
  src_mor q := (q.2 : P (q : Mor × W).2 = X.src (q : Mor × W).1).symm
  tgt_mor q := (E.P_μ q).symm
  mor_comp φ ψ h := by
    change (morComp φ ψ : Mor × W).1 = X.comp (φ : Mor × W).1 (ψ : Mor × W).1
    rw [morComp_val h]
  mor_unit _ := rfl
  isScSmoothMap_obj := B.isScSmoothMap_proj
  isScSmoothMap_mor := B.isScSmoothMap_pullbackProj X.isScSmoothMap_src

@[simp] lemma projFunctor_obj : E.projFunctor.obj = P := rfl
@[simp] lemma projFunctor_mor : E.projFunctor.mor = pullbackProj P X.src := rfl

/-- **`s_𝐖` and `t_𝐖` are strong bundle maps covering `s` and `t`** (p. 272: "fiberwise linear
local sc-diffeomorphisms covering the source and target maps"; the local sc-diffeomorphism
property is part of `toEpGroupoid`). -/
theorem isStrongBundleMap_src :
    (B.pullback X.isScSmoothMap_src).IsStrongBundleMap B X.src E.toEpGroupoid.src :=
  B.isStrongBundleMap_pullbackProj' X.isScSmoothMap_src

theorem isStrongBundleMap_tgt :
    (B.pullback X.isScSmoothMap_src).IsStrongBundleMap B X.tgt E.toEpGroupoid.tgt :=
  E.isStrongBundleMap

/-- **The orbit of `w` covers the orbit of `P(w)`** (p. 272): every `ψ : P(w) → x` lifts to the
morphism `(ψ, w) : w → μ(ψ, w)` over `ψ`. -/
theorem exists_isomorphic_of_isomorphic {w : W} {x : Obj} (h : X.Isomorphic (P w) x) :
    ∃ w', E.toEpGroupoid.Isomorphic w w' ∧ P w' = x := by
  obtain ⟨ψ, hs, rfl⟩ := h
  exact ⟨E.μ ⟨(ψ, w), hs.symm⟩, ⟨⟨(ψ, w), hs.symm⟩, rfl, rfl⟩, E.P_μ _⟩

/-- **`|P| : |W| → |X|` is surjective** (p. 272). -/
theorem surjective_orbitMap_projFunctor : Surjective E.projFunctor.orbitMap := by
  intro c
  induction c using Quotient.ind with
  | _ x =>
    obtain ⟨w, rfl⟩ := B.surjective x
    exact ⟨E.toEpGroupoid.π w, rfl⟩

/-- **`|P| : |W| → |X|` is continuous** (p. 272). -/
theorem continuous_orbitMap_projFunctor : Continuous E.projFunctor.orbitMap :=
  continuous_quot_lift _ (X.continuous_π.comp B.continuous)

end EpStrongBundle

end FunctorialEp

/-! ### Maps of pull-backs are linear on the fibres -/

section PullbackMapLinear

variable {X Y Z X' Y' Z' : Type*} {P : Y → X} {f : Z → X} {P' : Y' → X'} {f' : Z' → X'}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]

/-- The identification `P⁻¹(a) = P⁻¹(b)` for `a = b`, as a linear map. -/
def fiberCast (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {a b : X} (h : a = b) : P ⁻¹' {a} →ₗ[ℝ] P ⁻¹' {b} := by
  subst h; exact LinearMap.id

@[simp] lemma fiberCast_val {a b : X} (h : a = b) (v : P ⁻¹' {a}) :
    (fiberCast P h v : Y) = v := by
  subst h; rfl

variable (P f) in
/-- The fibre identification `P_f⁻¹(z) ≅ P⁻¹(f(z))` as a linear equivalence (Part I's
`pullbackFiberCLE` without the topologies). -/
def pullbackFiberLinearEquiv (z : Z) : (pullbackProj P f ⁻¹' {z}) ≃ₗ[ℝ] (P ⁻¹' {f z}) where
  toFun := pullbackFiberEquiv P f z
  invFun := (pullbackFiberEquiv P f z).symm
  map_add' := pullbackFiberEquiv_add P f z
  map_smul' := pullbackFiberEquiv_smul P f z
  left_inv := (pullbackFiberEquiv P f z).left_inv
  right_inv := (pullbackFiberEquiv P f z).right_inv

/-- A map of pull-backs `(z, y) ↦ (g(z), Φ(y))`, for `Φ` linear on the fibres covering `h` and
`f' ∘ g = h ∘ f`, is linear on the fibres of `P_f`, `P'_{f'}`. -/
theorem isLinearMap_fiberRestrict_pullbackMap {h : X → X'} {g : Z → Z'} {Φ : Y → Y'}
    (hΦ : ∀ y, P' (Φ y) = h (P y)) (hlin : ∀ x, IsLinearMap ℝ (fiberRestrict P P' h Φ hΦ x))
    (hg : ∀ z, f' (g z) = h (f z)) (Ψ : pullbackSpace P f → pullbackSpace P' f')
    (hΨ : ∀ q, (Ψ q : Z' × Y') = (g (q : Z × Y).1, Φ (q : Z × Y).2))
    (hcov : ∀ q, pullbackProj P' f' (Ψ q) = g (pullbackProj P f q)) (z : Z) :
    IsLinearMap ℝ (fiberRestrict (pullbackProj P f) (pullbackProj P' f') g Ψ hcov z) := by
  let L : pullbackProj P f ⁻¹' {z} →ₗ[ℝ] pullbackProj P' f' ⁻¹' {g z} :=
    ((pullbackFiberLinearEquiv P' f' (g z)).symm.toLinearMap).comp
      ((fiberCast P' (hg z).symm).comp
        ((hlin (f z)).mk'.comp (pullbackFiberLinearEquiv P f z).toLinearMap))
  have hL : fiberRestrict (pullbackProj P f) (pullbackProj P' f') g Ψ hcov z = L := by
    funext v
    apply Subtype.ext; apply Subtype.ext
    have hv : ((v : pullbackSpace P f) : Z × Y).1 = z := v.2
    rw [fiberRestrict_val, hΨ, hv]
    change (g z, Φ _) = (g z, ((fiberCast P' (hg z).symm _ : P' ⁻¹' {f' (g z)}) : Y'))
    rw [fiberCast_val]
    rfl
  rw [hL]; exact L.isLinear

end PullbackMapLinear

/-! ### Definition 8.3.3 (2017: 8.6): strong bundle functors, and the equivalence with Definition 8.3.2 (2017: 8.5) -/

section BundleFunctor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type u} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {ϕ : EpFunctor X X'}

namespace EpStrongBundle

variable (E E' ϕ) in
/-- **Definition 8.3.3 (2017: 8.6) (strong bundle functor)**: a functor `Φ : (W, 𝐖) → (W', 𝐖')` between the
ep-groupoids of the functorial picture which covers the sc-smooth functor `ϕ : X → X'` and induces
strong bundle maps `Φ : W → W'` (covering `ϕ` on objects, for `P`, `P'`) and `Φ : 𝐖 → 𝐖'`
(covering `ϕ` on morphisms, for the pull-back bundles `𝐖 → 𝐗`, `𝐖' → 𝐗'`).  Covering and the
linearity on the fibres are part of `IsStrongBundleMap`; the square `P' ∘ Φ = ϕ ∘ P` is
`isStrongBundleMap_obj.covers`. -/
structure IsStrongBundleFunctor (Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid) : Prop where
  isStrongBundleMap_obj : B.IsStrongBundleMap B' ϕ.obj Φ.obj
  isStrongBundleMap_mor :
    (B.pullback X.isScSmoothMap_src).IsStrongBundleMap (B'.pullback X'.isScSmoothMap_src) ϕ.mor
      Φ.mor

/-- `Φ` covers `ϕ` as a functor: `(P', π₁) ∘ Φ = ϕ ∘ (P, π₁)`. -/
theorem IsStrongBundleFunctor.projFunctor_comp {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (h : E.IsStrongBundleFunctor E' ϕ Φ) : E'.projFunctor.comp Φ = ϕ.comp E.projFunctor :=
  EpFunctor.ext (funext h.isStrongBundleMap_obj.covers) (funext h.isStrongBundleMap_mor.covers)

/-- **A strong bundle functor is determined by its object map** (p. 274, "from the strong bundle
map we can recover the functor completely"): `Φ(γ, w) = (ϕ(γ), Φ(w))`. -/
theorem IsStrongBundleFunctor.mor_val {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (h : E.IsStrongBundleFunctor E' ϕ Φ) (q : pullbackSpace P X.src) :
    (Φ.mor q : Mor' × W') = (ϕ.mor (q : Mor × W).1, Φ.obj (q : Mor × W).2) :=
  Prod.ext (h.isStrongBundleMap_mor.covers q) (Φ.src_mor q)

/-- **Definition 8.3.3 (2017: 8.6) ⇒ Definition 8.3.2 (2017: 8.5)** (p. 274): the object map of a strong bundle functor is a
strong bundle map in the sense of Definition 8.3.2 (2017: 8.5): `Φ(μ(γ, w)) = Φ(t(γ, w)) = t'(Φ(γ, w)) =
μ'(ϕ(γ), Φ(w))`. -/
theorem IsStrongBundleFunctor.isMap {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (h : E.IsStrongBundleFunctor E' ϕ Φ) : E.IsMap E' ϕ Φ.obj where
  isStrongBundleMap := h.isStrongBundleMap_obj
  map_μ γ w hw := by
    have h1 : E'.μ (Φ.mor ⟨(γ, w), hw⟩) = Φ.obj (E.μ ⟨(γ, w), hw⟩) := Φ.tgt_mor ⟨(γ, w), hw⟩
    rw [← h1]
    exact E'.μ_congr (h.mor_val _)

variable (ϕ) in
/-- The morphism map `(γ, w) ↦ (ϕ(γ), Φ(w))` of the lift of `Φ : W → W'` (p. 273). -/
def liftMor {Φ : W → W'} (hΦ : ∀ w, P' (Φ w) = ϕ.obj (P w)) (q : pullbackSpace P X.src) :
    pullbackSpace P' X'.src :=
  ⟨(ϕ.mor (q : Mor × W).1, Φ (q : Mor × W).2), by
    change P' (Φ (q : Mor × W).2) = X'.src (ϕ.mor (q : Mor × W).1)
    rw [hΦ, show P (q : Mor × W).2 = X.src (q : Mor × W).1 from q.2, ϕ.src_mor]⟩

omit [TopologicalSpace W] [T2Space W] [ParacompactSpace W] [∀ x, AddCommGroup (P ⁻¹' {x})]
  [∀ x, Module ℝ (P ⁻¹' {x})] [ParacompactSpace (pullbackSpace P X.src)] [TopologicalSpace W']
  [T2Space W'] [ParacompactSpace W'] [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  [ParacompactSpace (pullbackSpace P' X'.src)] in
@[simp] lemma liftMor_val {Φ : W → W'} (hΦ : ∀ w, P' (Φ w) = ϕ.obj (P w))
    (q : pullbackSpace P X.src) :
    (liftMor ϕ hΦ q : Mor' × W') = (ϕ.mor (q : Mor × W).1, Φ (q : Mor × W).2) := rfl

/-- **Definition 8.3.2 (2017: 8.5) ⇒ the functorial picture** (p. 273): a strong bundle map `Φ` in the sense of
Definition 8.3.2 (2017: 8.5) lifts to the functor `(W, 𝐖) → (W', 𝐖')` with `Φ(γ, w) = (ϕ(γ), Φ(w))`; the two
squares `s' ∘ Φ = Φ ∘ s` and `t' ∘ Φ = Φ ∘ t` are its `src_mor`, `tgt_mor`. -/
def IsMap.liftFunctor {Φ : W → W'} (h : E.IsMap E' ϕ Φ) :
    EpFunctor E.toEpGroupoid E'.toEpGroupoid where
  obj := Φ
  mor := liftMor ϕ h.isStrongBundleMap.covers
  src_mor _ := rfl
  tgt_mor q := (h.map_μ (q : Mor × W).1 (q : Mor × W).2 q.2).symm
  mor_comp φ ψ hc := by
    have hc' : (φ : Mor × W).2 = E.μ ψ := hc
    have hc'' : (liftMor ϕ h.isStrongBundleMap.covers φ : Mor' × W').2 =
        E'.μ (liftMor ϕ h.isStrongBundleMap.covers ψ) := by
      change Φ (φ : Mor × W).2 = _
      rw [hc', h.map_μ (ψ : Mor × W).1 (ψ : Mor × W).2 ψ.2]; rfl
    apply Subtype.ext
    change (liftMor ϕ h.isStrongBundleMap.covers (morComp φ ψ) : Mor' × W') =
      (morComp (liftMor ϕ h.isStrongBundleMap.covers φ) (liftMor ϕ h.isStrongBundleMap.covers ψ) :
        Mor' × W')
    rw [morComp_val hc'', liftMor_val, morComp_val hc', liftMor_val, liftMor_val,
      ϕ.mor_comp _ _ (src_eq_tgt_of_eq_μ hc')]
  mor_unit w := by
    apply Subtype.ext
    change (ϕ.mor (X.unit (P w)), Φ w) = (X'.unit (P' (Φ w)), Φ w)
    rw [ϕ.mor_unit, h.isStrongBundleMap.covers]
  isScSmoothMap_obj := h.isStrongBundleMap.isScSmoothMap
  isScSmoothMap_mor :=
    B'.isScSmoothMap_pullbackPair X'.isScSmoothMap_src
      (a := ϕ.mor ∘ pullbackProj P X.src) (b := Φ ∘ pullbackProj' P X.src)
      (ϕ.isScSmoothMap_mor.comp (B.isScSmoothMap_pullbackProj X.isScSmoothMap_src))
      (h.isStrongBundleMap.isScSmoothMap.comp (B.isScSmoothMap_pullbackProj' X.isScSmoothMap_src))
      fun q => (liftMor ϕ h.isStrongBundleMap.covers q).2

@[simp] lemma IsMap.liftFunctor_obj {Φ : W → W'} (h : E.IsMap E' ϕ Φ) :
    h.liftFunctor.obj = Φ := rfl

@[simp] lemma IsMap.liftFunctor_mor {Φ : W → W'} (h : E.IsMap E' ϕ Φ) :
    h.liftFunctor.mor = liftMor ϕ h.isStrongBundleMap.covers := rfl

/-- **The lift is a strong bundle functor** (p. 273: "`Φ : 𝐖 → 𝐖'` is a strong bundle map
covering the map `ϕ : 𝐗 → 𝐗'`"): on morphisms, `(γ, w) ↦ (ϕ(γ), Φ(w))` is linear on the fibres
(those of `Φ`), sc-smooth on `𝐖[0]` and on `𝐖[1]` (the universal properties of the pull-backs). -/
theorem IsMap.isStrongBundleFunctor_liftFunctor {Φ : W → W'} (h : E.IsMap E' ϕ Φ) :
    E.IsStrongBundleFunctor E' ϕ h.liftFunctor where
  isStrongBundleMap_obj := h.isStrongBundleMap
  isStrongBundleMap_mor :=
    { covers := fun _ => rfl
      fiber_linear := isLinearMap_fiberRestrict_pullbackMap h.isStrongBundleMap.covers
        h.isStrongBundleMap.fiber_linear ϕ.src_mor _ (fun _ => rfl) _
      isScSmoothMap := h.liftFunctor.isScSmoothMap_mor
      mapsTo_oneSet := fun q hq => by
        rw [B'.mem_oneSet_pullback_iff]
        exact h.isStrongBundleMap.mapsTo_oneSet ((B.mem_oneSet_pullback_iff _ q).1 hq)
      isScSmoothMap_one := by
        refine B'.isScSmoothMap_to_pullback_one X'.isScSmoothMap_src ?_ ?_
        · exact ϕ.isScSmoothMap_mor.comp (B.pullback X.isScSmoothMap_src).isScSmoothMap_proj1
        · exact h.isStrongBundleMap.isScSmoothMap_one.comp
            (B.isScSmoothMap_one_pullbackProj' X.isScSmoothMap_src) }

/-- **A strong bundle functor is the lift of its object map** (p. 274). -/
theorem IsStrongBundleFunctor.eq_liftFunctor {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (h : E.IsStrongBundleFunctor E' ϕ Φ) : Φ = h.isMap.liftFunctor :=
  EpFunctor.ext rfl (funext fun q => Subtype.ext (h.mor_val q))

/-- **Definitions 8.3.2 and 8.3.3 (2017: 8.5 and 8.6) are equivalent** (pp. 273–274): `Φ : W → W'` is a strong bundle map
covering `ϕ` in the sense of Definition 8.3.2 (2017: 8.5) iff it is the object map of a strong bundle functor
covering `ϕ` (Definition 8.3.3 (2017: 8.6)), and that functor is then unique (`Φ(γ, w) = (ϕ(γ), Φ(w))`). -/
theorem isMap_iff_strongBundleFunctor {Φ : W → W'} :
    E.IsMap E' ϕ Φ ↔
      ∃! Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid, E.IsStrongBundleFunctor E' ϕ Ψ ∧
        Ψ.obj = Φ := by
  constructor
  · intro h
    refine ⟨h.liftFunctor, ⟨h.isStrongBundleFunctor_liftFunctor, rfl⟩, ?_⟩
    rintro Ψ ⟨hΨ, rfl⟩
    exact hΨ.eq_liftFunctor
  · rintro ⟨Ψ, ⟨hΨ, rfl⟩, -⟩
    exact hΨ.isMap

end EpStrongBundle

end BundleFunctor

/-! ### Sums and scalar multiples of sc-smooth sections (Part I) -/

section SectionAlgebra

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f s : X → Y}

namespace StrongBundle

/-- A section is sc-smooth as soon as its local representatives `z ↦ (z, ĝ(z)) : O → K` are
sc-smooth in the charts of the atlas (Definition 2.6.6 (preprint 2.52) read in the charts; the continuity of `g`
follows from the charts). -/
theorem isScSmoothSection_of_principal {g : X → Y} (hg : IsSection P g)
    (h : ∀ c ∈ B.atlas.charts, IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O
      (c.φ.model.E.prod c.F) (c.φ.model.C ×ˢ univ) c.K (fun z => (z, c.principal g z))) :
    B.IsScSmoothSection g := by
  refine ⟨hg, MPolyfold.isScSmoothMap_of_forall_charts fun x => ?_⟩
  obtain ⟨c, hc, hx⟩ := B.exists_chart_mem x
  refine ⟨c.φ, c.toMChart B.continuous, c.isChart, B.isChart_toMChart hc, hx,
    fun y hy => c.mem_source_of_proj (by rw [hg y]; exact hy), ?_⟩
  exact (h c hc).congr fun z hz => (c.apply_section hg hz).symm

/-- **The sum of two sc-smooth sections is sc-smooth** (in a chart, `(f + s)^ = f̂ + ŝ`). -/
theorem IsScSmoothSection.sectionAdd_of_isScSmoothSection (hf : B.IsScSmoothSection f)
    (hs : B.IsScSmoothSection s) : B.IsScSmoothSection (Polyfold.sectionAdd P f s) := by
  refine isScSmoothSection_of_principal (hf.1.sectionAdd hs.1) fun c hc => ?_
  have hc' := B.isChart_of_mem hc
  have hrep : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F)
      (c.φ.model.C ×ˢ univ) c.K (fun z => (z, c.principal f z + c.principal s z)) :=
    { mapsTo := fun z hz => c.add_mem_K ((hf.isScSmoothRetractMap hc').mapsTo hz)
        ((hs.isScSmoothRetractMap hc').mapsTo hz)
      comp_isScSmooth := fun R hR => by
        have hU := R.isScDomain
        have h1 : IsScSmooth R.U fun u => c.principal f (R u) :=
          (((hf.isScSmoothRetractMap hc').comp_isScSmooth R hR).snd hU).congr hU fun _ _ => rfl
        have h2 : IsScSmooth R.U fun u => c.principal s (R u) :=
          (((hs.isScSmoothRetractMap hc').comp_isScSmooth R hR).snd hU).congr hU fun _ _ => rfl
        exact (R.isScSmooth.scPair hU (h1.add hU h2)).congr hU fun _ _ => rfl }
  exact hrep.congr fun z hz => by rw [c.principal_sectionAdd hf.1 hs.1 hz]

/-- **A constant multiple of an sc-smooth section is sc-smooth** (in a chart,
`(a·f)^ = a·f̂`). -/
theorem IsScSmoothSection.sectionSmul_const (a : ℝ) (hf : B.IsScSmoothSection f) :
    B.IsScSmoothSection (Polyfold.sectionSmul P (fun _ => a) f) := by
  refine isScSmoothSection_of_principal hf.1.sectionSmul fun c hc => ?_
  have hc' := B.isChart_of_mem hc
  have hrep : IsScSmoothRetractMap c.φ.model.E c.φ.model.C c.φ.model.O (c.φ.model.E.prod c.F)
      (c.φ.model.C ×ˢ univ) c.K (fun z => (z, a • c.principal f z)) :=
    { mapsTo := fun z hz => c.smul_mem_K ((hf.isScSmoothRetractMap hc').mapsTo hz) a
      comp_isScSmooth := fun R hR => by
        have hU := R.isScDomain
        have h1 : IsScSmooth R.U fun u => c.principal f (R u) :=
          (((hf.isScSmoothRetractMap hc').comp_isScSmooth R hR).snd hU).congr hU fun _ _ => rfl
        have h2 : IsScSmooth R.U fun u => a • c.principal f (R u) :=
          (IsScSmooth.comp hU (isScDomain_univ _)
            ((ScOperator.smulOp c.F a).isScSmooth (isScDomain_univ _)) h1
            (mapsTo_univ _ _)).congr hU fun _ _ => rfl
        exact (R.isScSmooth.scPair hU h2).congr hU fun _ _ => rfl }
  refine hrep.congr fun z hz => ?_
  have hzs := c.φ.symm_mapsTo hz
  refine Prod.ext rfl ?_
  change a • (c (f (c.φ.symm z))).2 = (c (sectionSmul P (fun _ => a) f (c.φ.symm z))).2
  rw [sectionSmul_apply hf.1]
  exact ((c.fiber_linear _ hzs).map_smul a ⟨f (c.φ.symm z), hf.1 _⟩).symm

/-- **The zero section is sc-smooth** (it is an sc⁺-section, Part I). -/
theorem isScSmoothSection_fiberZero : B.IsScSmoothSection (fiberZero P) := by
  obtain ⟨-, g, hg, hgs⟩ :=
    (B.isScPlusSection_iff (fiberZero P)).1 (StrongBundle.isScPlusSection_fiberZero (B := B))
  exact ⟨isSection_fiberZero, by rw [← hg]; exact B.isScSmoothMap_oneVal.comp hgs⟩

end StrongBundle

end SectionAlgebra

/-! ### Definition 8.3.4 (2017: 8.7): `Γ(P, μ)` and `Γ⁺(P, μ)` are vector spaces -/

section SectionFunctors

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  (E : EpStrongBundle X B) {f g : Obj → W}

namespace EpStrongBundle

theorem isFunctorialSection_fiberZero : E.IsFunctorialSection (isSection_fiberZero (P := P)) :=
  fun φ => (congrArg Subtype.val ((E.fiberMor φ).map_zero)).symm

theorem IsFunctorialSection.sectionAdd {hf : IsSection P f} {hg : IsSection P g}
    (hf' : E.IsFunctorialSection hf) (hg' : E.IsFunctorialSection hg) :
    E.IsFunctorialSection (hf.sectionAdd hg) := fun φ => by
  have hs : ((φ, ((⟨f (X.src φ), hf _⟩ + ⟨g (X.src φ), hg _⟩ : P ⁻¹' {X.src φ}) : W)) :
      Mor × W) = (φ, Polyfold.sectionAdd P f g (X.src φ)) := by rw [sectionAdd_apply hf hg]
  calc Polyfold.sectionAdd P f g (X.tgt φ)
      = ((⟨f (X.tgt φ), hf _⟩ + ⟨g (X.tgt φ), hg _⟩ : P ⁻¹' {X.tgt φ}) : W) :=
        sectionAdd_apply hf hg _
    _ = ((⟨E.μ ⟨(φ, f (X.src φ)), hf _⟩, (E.fiberMor φ ⟨f (X.src φ), hf _⟩).2⟩ +
          ⟨E.μ ⟨(φ, g (X.src φ)), hg _⟩, (E.fiberMor φ ⟨g (X.src φ), hg _⟩).2⟩ :
            P ⁻¹' {X.tgt φ}) : W) := by
        congr 2
        · exact Subtype.ext (hf' φ)
        · exact Subtype.ext (hg' φ)
    _ = E.μ ⟨(φ, ((⟨f (X.src φ), hf _⟩ + ⟨g (X.src φ), hg _⟩ : P ⁻¹' {X.src φ}) : W)),
          by exact (⟨f (X.src φ), hf _⟩ + ⟨g (X.src φ), hg _⟩ : P ⁻¹' {X.src φ}).2⟩ :=
        (E.μ_add φ ⟨f (X.src φ), hf _⟩ ⟨g (X.src φ), hg _⟩).symm
    _ = E.μ (sectionPair (hf.sectionAdd hg) φ) := E.μ_congr hs

theorem IsFunctorialSection.sectionSmul {hf : IsSection P f} (a : ℝ)
    (hf' : E.IsFunctorialSection hf) :
    E.IsFunctorialSection (hf.sectionSmul (f := fun _ => a)) := fun φ => by
  have hs : ((φ, ((a • ⟨f (X.src φ), hf _⟩ : P ⁻¹' {X.src φ}) : W)) : Mor × W) =
      (φ, Polyfold.sectionSmul P (fun _ => a) f (X.src φ)) := by rw [sectionSmul_apply hf]
  calc Polyfold.sectionSmul P (fun _ => a) f (X.tgt φ)
      = ((a • ⟨f (X.tgt φ), hf _⟩ : P ⁻¹' {X.tgt φ}) : W) := sectionSmul_apply hf _
    _ = ((a • ⟨E.μ ⟨(φ, f (X.src φ)), hf _⟩, (E.fiberMor φ ⟨f (X.src φ), hf _⟩).2⟩ :
            P ⁻¹' {X.tgt φ}) : W) := by
        congr 2
        exact Subtype.ext (hf' φ)
    _ = E.μ ⟨(φ, ((a • ⟨f (X.src φ), hf _⟩ : P ⁻¹' {X.src φ}) : W)),
          by exact (a • ⟨f (X.src φ), hf _⟩ : P ⁻¹' {X.src φ}).2⟩ :=
        (E.μ_smul φ a ⟨f (X.src φ), hf _⟩).symm
    _ = E.μ (sectionPair (hf.sectionSmul (f := fun _ => a)) φ) := E.μ_congr hs

/-- **`Γ(P, μ)` contains the zero section** (Definition 8.3.4 (2017: 8.7) (1), "the vector space"). -/
theorem fiberZero_mem_sectionFunctors : fiberZero P ∈ E.sectionFunctors :=
  ⟨StrongBundle.isScSmoothSection_fiberZero, E.isFunctorialSection_fiberZero⟩

/-- **`Γ(P, μ)` is closed under sums**: by the linearity of `μ(φ, ·)` (Definition 8.3.1 (2017: 8.4) (1)) and
Part I's sum of sc-smooth sections. -/
theorem sectionAdd_mem_sectionFunctors (hf : f ∈ E.sectionFunctors)
    (hg : g ∈ E.sectionFunctors) : sectionAdd P f g ∈ E.sectionFunctors := by
  obtain ⟨hf, hf'⟩ := hf
  obtain ⟨hg, hg'⟩ := hg
  exact ⟨hf.sectionAdd_of_isScSmoothSection hg, hf'.sectionAdd E hg'⟩

/-- **`Γ(P, μ)` is closed under scalar multiplication.** -/
theorem sectionSmul_mem_sectionFunctors (a : ℝ) (hf : f ∈ E.sectionFunctors) :
    sectionSmul P (fun _ => a) f ∈ E.sectionFunctors := by
  obtain ⟨hf, hf'⟩ := hf
  exact ⟨hf.sectionSmul_const a, hf'.sectionSmul E a⟩

/-- `Γ⁺(P, μ) ⊆ Γ(P, μ)` (Definition 8.3.4 (2017: 8.7) (2)). -/
theorem plusSectionFunctors_subset : E.plusSectionFunctors ⊆ E.sectionFunctors :=
  fun _ hf => hf.1

/-- **`Γ⁺(P, μ)` is a vector subspace**: the zero section, sums and scalar multiples. -/
theorem fiberZero_mem_plusSectionFunctors : fiberZero P ∈ E.plusSectionFunctors :=
  ⟨E.fiberZero_mem_sectionFunctors, StrongBundle.isScPlusSection_fiberZero⟩

theorem sectionAdd_mem_plusSectionFunctors (hf : f ∈ E.plusSectionFunctors)
    (hg : g ∈ E.plusSectionFunctors) : sectionAdd P f g ∈ E.plusSectionFunctors :=
  ⟨E.sectionAdd_mem_sectionFunctors hf.1 hg.1, hf.2.add hg.2⟩

theorem sectionSmul_mem_plusSectionFunctors (a : ℝ) (hf : f ∈ E.plusSectionFunctors) :
    sectionSmul P (fun _ => a) f ∈ E.plusSectionFunctors :=
  ⟨E.sectionSmul_mem_sectionFunctors a hf.1,
    hf.2.smul_left (isScSmoothMap_real_const a)⟩

/-- `Fred(P, μ) ⊆ Γ(P, μ)` (Definition 8.3.4 (2017: 8.7) (3)). -/
theorem fredholmSectionFunctors_subset : E.fredholmSectionFunctors ⊆ E.sectionFunctors :=
  fun _ hf => hf.1

end EpStrongBundle

end SectionFunctors

/-! ### Strong bundle isomorphisms over open subsets -/

section IsoOn

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]

namespace StrongBundle

/-- **A strong bundle map restricts to a strong bundle isomorphism `Y|U → Y'|U'`** covering
`f : U → U'` (a reading of "`A : W|U(y) → V|U(x)` is a strong bundle isomorphism", Definition
8.10): `f : U → U'` is an sc-diffeomorphism, and `Φ : P⁻¹(U) → P'⁻¹(U')` is an sc-diffeomorphism
on `[0]` and on `[1]`.  The inverse is then linear on the fibres (`Φ` is, being a strong bundle
map, and is bijective on the fibres), so it is a strong bundle map over `U'`. -/
structure IsStrongBundleIsoOn (B : StrongBundle PX P) (B' : StrongBundle PX' P') {f : X → X'}
    {Φ : Y → Y'} (h : B.IsStrongBundleMap B' f Φ) (U : Set X) (U' : Set X') : Prop where
  isScDiffeoOn_base : ∃ g : X' → X, PX.IsScDiffeoOn PX' f g U U'
  isScDiffeoOn_zero : ∃ Ψ : Y' → Y,
    B.toMPolyfold0.IsScDiffeoOn B'.toMPolyfold0 Φ Ψ (P ⁻¹' U) (P' ⁻¹' U')
  isScDiffeoOn_one : ∃ Ψ₁ : B'.One → B.One,
    B.toMPolyfold1.IsScDiffeoOn B'.toMPolyfold1 (oneRestrict B B' Φ h.mapsTo_oneSet) Ψ₁
      ((P ∘ B.oneVal) ⁻¹' U) ((P' ∘ B'.oneVal) ⁻¹' U')

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {f : X → X'} {Φ : Y → Y'}
  {h : B.IsStrongBundleMap B' f Φ} {U : Set X} {U' : Set X'}

/-- **The fibre maps of a local strong bundle isomorphism are topological linear isomorphisms**:
for `x ∈ U`, `Φ : P⁻¹(x) → P'⁻¹(f(x))` is bijective with continuous inverse. -/
def IsStrongBundleIsoOn.fiberEquiv (hi : B.IsStrongBundleIsoOn B' h U U') {x : X}
    (hx : x ∈ U) : P ⁻¹' {x} ≃L[ℝ] P' ⁻¹' {f x} :=
  haveI hΨ := Classical.choose_spec hi.isScDiffeoOn_zero
  haveI hg := Classical.choose_spec hi.isScDiffeoOn_base
  { toLinearMap := (h.fiberMap x).toLinearMap
    invFun := fun v => ⟨Classical.choose hi.isScDiffeoOn_zero v, by
      have hv : (v : Y') ∈ P' ⁻¹' U' := by
        change P' v ∈ U'; rw [show P' v = f x from v.2]; exact hg.mapsTo hx
      have h1 := hΨ.mapsTo_inv hv
      have h2 : f (P (Classical.choose hi.isScDiffeoOn_zero v)) = f x := by
        rw [← h.covers, hΨ.right_inv _ hv]; exact v.2
      change P _ = x
      rw [← hg.left_inv _ h1, h2, hg.left_inv _ hx]⟩
    left_inv := fun v => Subtype.ext (hΨ.left_inv v (by
      change P v ∈ U; rw [show P v = x from v.2]; exact hx))
    right_inv := fun v => Subtype.ext (hΨ.right_inv v (by
      change P' v ∈ U'; rw [show P' v = f x from v.2]; exact hg.mapsTo hx))
    continuous_toFun := (h.fiberMap x).continuous
    continuous_invFun := by
      refine (hΨ.isScSmoothOn_inv.continuousOn.comp_continuous continuous_subtype_val
        fun v => ?_).subtype_mk _
      change P' v ∈ U'; rw [show P' v = f x from v.2]; exact hg.mapsTo hx }

@[simp] lemma IsStrongBundleIsoOn.fiberEquiv_apply (hi : B.IsStrongBundleIsoOn B' h U U')
    {x : X} (hx : x ∈ U) (v : P ⁻¹' {x}) : (hi.fiberEquiv hx v : Y') = Φ v := rfl

end StrongBundle

end IsoOn

/-! ### Definition 8.5.9 (2017: 8.10): proper strong bundle covering functors -/

section ProperBundleCovering

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

/-- `pr₂ : 𝐗 ₛ×_F Y → Y`, `(φ, y) ↦ y`. -/
def EpFunctor.fibredSnd (F : EpFunctor Y X) (p : MPolyfold.fibredProduct X.src F.obj) : ObjY :=
  (p : MorX × ObjY).2

/-- `pr₂ : 𝐗 ₛ×_F Y → Y` is sc-smooth on Part I's sub-M-polyfold `𝐗 ₛ×_F Y` of `𝐗 × Y`. -/
theorem EpFunctor.isScSmoothMap_fibredSnd (F : EpFunctor Y X) [ParacompactSpace (MorX × ObjY)]
    [ParacompactSpace (MPolyfold.fibredProduct X.src F.obj)] :
    (MPolyfold.subPolyfold (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src
      F.isScSmoothMap_obj)).IsScSmoothMap Y.PObj F.fibredSnd :=
  (MPolyfold.isScSmoothMap_snd X.PMor Y.PObj).comp
    (MPolyfold.subPolyfold_inclusion_isScSmooth _)

namespace EpStrongBundle

variable (P) in
/-- The map `𝐖 = 𝐘 ₛ×_P W → (𝐗 ₛ×_F Y) ×_{pr₂} W`, `(ψ, w) ↦ ((F(ψ), s(ψ)), w)` of Definition 8.5.9 (2017: 8.10)
(3), read on the pull-back of `P` along `pr₂` (see `fibredBundleEquiv` for the text's
`𝐕 ₛ×_A W`). -/
def fibredLift (F : EpFunctor Y X) (q : pullbackSpace P Y.src) : pullbackSpace P F.fibredSnd :=
  ⟨(F.fibredMap (q : MorY × W).1, (q : MorY × W).2), q.2⟩

omit [TopologicalSpace W] [T2Space W] [ParacompactSpace W] [∀ y, AddCommGroup (P ⁻¹' {y})]
  [∀ y, Module ℝ (P ⁻¹' {y})] [ParacompactSpace (pullbackSpace P Y.src)] in
/-- The projection of `(𝐗 ₛ×_F Y) ×_{pr₂} W → 𝐗 ₛ×_F Y` is `((φ, y), w) ↦ (φ, y) = (φ, P(w))`;
over `fibredLift` it is `ψ ↦ (F(ψ), s(ψ))`. -/
theorem pullbackProj_fibredLift (F : EpFunctor Y X) (q : pullbackSpace P Y.src) :
    pullbackProj P F.fibredSnd (fibredLift P F q) = F.fibredMap (pullbackProj P Y.src q) := rfl

variable {F : EpFunctor Y X} {A : W → V} (hA : ∀ w, Q (A w) = F.obj (P w))

include hA in
/-- **The text's `𝐕 ₛ×_A W = {((φ, v), w) ∈ 𝐕 × W | s_𝐕(φ, v) = A(w)}`** (Definition 8.5.9 (2017: 8.10) (3))
is the pull-back `(𝐗 ₛ×_F Y) ×_{pr₂} W = {((φ, y), w) | s(φ) = F(y), P(w) = y}`:
`((φ, v), w) ↦ ((φ, P(w)), w)`, with inverse `((φ, y), w) ↦ ((φ, A(w)), w)` (`v = A(w)` is
determined by `w`). -/
def fibredBundleEquiv :
    MPolyfold.fibredProduct (pullbackProj' Q X.src) A ≃ pullbackSpace P F.fibredSnd where
  toFun p := ⟨(⟨(((p : pullbackSpace Q X.src × W).1 : MorX × V).1,
      P (p : pullbackSpace Q X.src × W).2), by
        change X.src _ = F.obj _
        rw [← hA, ← (show pullbackProj' Q X.src (p : pullbackSpace Q X.src × W).1 =
          A (p : pullbackSpace Q X.src × W).2 from p.2)]
        exact ((p : pullbackSpace Q X.src × W).1.2).symm⟩,
      (p : pullbackSpace Q X.src × W).2), rfl⟩
  invFun r := ⟨(⟨((((r : MPolyfold.fibredProduct X.src F.obj × W).1 : MorX × ObjY)).1,
      A (r : MPolyfold.fibredProduct X.src F.obj × W).2), by
        change Q (A _) = X.src _
        rw [hA, show P (r : MPolyfold.fibredProduct X.src F.obj × W).2 =
          ((r : MPolyfold.fibredProduct X.src F.obj × W).1 : MorX × ObjY).2 from r.2]
        exact ((r : MPolyfold.fibredProduct X.src F.obj × W).1.2).symm⟩,
      (r : MPolyfold.fibredProduct X.src F.obj × W).2), rfl⟩
  left_inv p := by
    obtain ⟨⟨⟨⟨φ, v⟩, hv⟩, w⟩, hp⟩ := p
    have hp' : v = A w := hp
    subst hp'
    rfl
  right_inv r := by
    obtain ⟨⟨⟨⟨φ, y⟩, hy⟩, w⟩, hr⟩ := r
    have hr' : P w = y := hr
    subst hr'
    rfl

omit [TopologicalSpace W] [T2Space W] [ParacompactSpace W] [∀ y, AddCommGroup (P ⁻¹' {y})]
  [∀ y, Module ℝ (P ⁻¹' {y})] [TopologicalSpace V] [T2Space V] [ParacompactSpace V]
  [∀ x, AddCommGroup (Q ⁻¹' {x})] [∀ x, Module ℝ (Q ⁻¹' {x})]
  [ParacompactSpace (pullbackSpace P Y.src)] [ParacompactSpace (pullbackSpace Q X.src)] in
/-- Through `fibredBundleEquiv`, the projection `(𝐗 ₛ×_F Y) ×_{pr₂} W → 𝐗 ₛ×_F Y` is the text's
`((φ, v), w) ↦ (φ, P(w))`. -/
theorem pullbackProj_fibredBundleEquiv (p : MPolyfold.fibredProduct (pullbackProj' Q X.src) A) :
    ((pullbackProj P F.fibredSnd (fibredBundleEquiv hA p) : MPolyfold.fibredProduct X.src F.obj) :
      MorX × ObjY) =
      (((p : pullbackSpace Q X.src × W).1 : MorX × V).1, P (p : pullbackSpace Q X.src × W).2) :=
  rfl

omit [TopologicalSpace W] [T2Space W] [ParacompactSpace W] [∀ y, AddCommGroup (P ⁻¹' {y})]
  [∀ y, Module ℝ (P ⁻¹' {y})] [TopologicalSpace V] [T2Space V] [ParacompactSpace V]
  [∀ x, AddCommGroup (Q ⁻¹' {x})] [∀ x, Module ℝ (Q ⁻¹' {x})]
  [ParacompactSpace (pullbackSpace P Y.src)] [ParacompactSpace (pullbackSpace Q X.src)] in
/-- Through `fibredBundleEquiv`, `fibredLift` is the text's map `(ψ, w) ↦ ((F(ψ), A(w)), w)`. -/
theorem fibredBundleEquiv_symm_fibredLift (q : pullbackSpace P Y.src) :
    (((fibredBundleEquiv hA).symm (fibredLift P F q) : pullbackSpace Q X.src × W).1 : MorX × V) =
        (F.mor (q : MorY × W).1, A (q : MorY × W).2) ∧
      ((fibredBundleEquiv hA).symm (fibredLift P F q) : pullbackSpace Q X.src × W).2 =
        (q : MorY × W).2 :=
  ⟨rfl, rfl⟩

end EpStrongBundle

end ProperBundleCovering

section ProperBundleCovering'

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

/-- **Definition 8.5.9 (2017: 8.10) (proper strong bundle covering functor)** for strong bundles `(W, μ)` over
`Y` and `(V, τ)` over `X`: a strong bundle functor `A : (W, 𝐖) → (V, 𝐕)` (Definition 8.3.3 (2017: 8.6), "a strong
bundle map `A`, in particular fibrewise linear", `Q ∘ A = F ∘ P`) covering `F : Y → X`, with
(1) `A` surjective and a local strong bundle isomorphism, `F` an sc-smooth proper covering
functor (Definition 8.5.1 (2017: 8.8)); (2) for every `x ∈ X` (whose `F⁻¹(x)` is finite by Definition 8.5.1 (2017: 8.8) (2))
an open `U(x) ∋ x` and mutually disjoint `U(y) ∋ y`, `y ∈ F⁻¹(x)`, with
`A : W|U(y) → V|U(x)` strong bundle isomorphisms and `F⁻¹(U(x)) = ⋃ U(y)`; (3)
`(ψ, w) ↦ ((F(ψ), A(w)), w)` is a strong bundle isomorphism `𝐖 → 𝐕 ₛ×_A W` covering the
sc-diffeomorphism `𝐘 → 𝐗 ₛ×_F Y`, `ψ ↦ (F(ψ), s(ψ))`; `𝐕 ₛ×_A W` is read as the pull-back
`(𝐗 ₛ×_F Y) ×_{pr₂} W` of `P` (`fibredBundleEquiv`), the map as `fibredLift`. -/
structure IsProperStrongBundleCovering (EW : EpStrongBundle Y BW) (EV : EpStrongBundle X BV)
    (F : EpFunctor Y X) (A : EpFunctor EW.toEpGroupoid EV.toEpGroupoid) : Prop where
  isStrongBundleFunctor : EW.IsStrongBundleFunctor EV F A
  surjective : Surjective A.obj
  isProperCovering : F.IsProperCovering
  isLocalStrongBundleIso : ∀ y : ObjY, ∃ (U : Set ObjY) (U' : Set ObjX), y ∈ U ∧
    BW.IsStrongBundleIsoOn BV isStrongBundleFunctor.isStrongBundleMap_obj U U'
  evenlyCovered : ∀ x : ObjX, ∃ (U : Set ObjX) (U' : ObjY → Set ObjY), IsOpen U ∧ x ∈ U ∧
    (F.obj ⁻¹' {x}).PairwiseDisjoint U' ∧
    (∀ y ∈ F.obj ⁻¹' {x}, y ∈ U' y ∧
      BW.IsStrongBundleIsoOn BV isStrongBundleFunctor.isStrongBundleMap_obj (U' y) U) ∧
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

/-! ### §8.5.2: the structure of strong bundle coverings -/

variable {EW : EpStrongBundle Y BW} {EV : EpStrongBundle X BV} {F : EpFunctor Y X}
  {A : EpFunctor EW.toEpGroupoid EV.toEpGroupoid}

/-- §8.5.2 (p. 288), "the functor `A` applied to morphisms has the form
`A(φ, w) = (F(φ), A_{s(φ)}(w))`". -/
theorem IsProperStrongBundleCovering.mor_val (h : EW.IsProperStrongBundleCovering EV F A)
    (q : pullbackSpace P Y.src) :
    (A.mor q : MorX × V) = (F.mor (q : MorY × W).1, A.obj (q : MorY × W).2) :=
  h.isStrongBundleFunctor.mor_val q

/-- **The fibre maps `A_y : P⁻¹(y) → Q⁻¹(F(y))` are topological linear isomorphisms**
(§8.5.2, p. 288: "the topological linear isomorphism induced by `A` between the fibers"), from
Definition 8.5.9 (2017: 8.10) (1). -/
def IsProperStrongBundleCovering.fiberEquiv (h : EW.IsProperStrongBundleCovering EV F A)
    (y : ObjY) : P ⁻¹' {y} ≃L[ℝ] Q ⁻¹' {F.obj y} :=
  (Classical.choose_spec (Classical.choose_spec (h.isLocalStrongBundleIso y))).2.fiberEquiv
    (Classical.choose_spec (Classical.choose_spec (h.isLocalStrongBundleIso y))).1

@[simp] lemma IsProperStrongBundleCovering.fiberEquiv_apply
    (h : EW.IsProperStrongBundleCovering EV F A) (y : ObjY) (v : P ⁻¹' {y}) :
    (h.fiberEquiv y v : V) = A.obj v := rfl

/-- The compatibility `τ(F(φ), A(w)) = A(μ(φ, w))` of a strong bundle functor `A` covering `F`
(the computation of §8.5.2: `τ(F(φ))(A_{s(φ)}(w)) = t(A(φ, w)) = A(t(φ, w)) = A(μ(φ)(w))`, using
only that `A` is a functor, `A(φ, w) = (F(φ), A_{s(φ)}(w))`). -/
theorem IsStrongBundleFunctor.μ_comm (h : EW.IsStrongBundleFunctor EV F A) (φ : MorY) (w : W)
    (hw : P w = Y.src φ) (hw' : Q (A.obj w) = X.src (F.mor φ)) :
    EV.μ ⟨(F.mor φ, A.obj w), hw'⟩ = A.obj (EW.μ ⟨(φ, w), hw⟩) :=
  (h.isMap.map_μ φ w hw).symm

/-- **§8.5.2** (pp. 288–289): for a proper strong bundle covering functor `A` covering `F`,
`μ_X(F(φ)) ∘ A_{s(φ)} = A_{t(φ)} ∘ μ_Y(φ)` on `P⁻¹(s(φ))` for every morphism `φ` of `Y`: the
family `y ↦ A_y` is a natural transformation `μ_Y → μ_X ∘ F` of the functors into `Ban` (Banach
spaces and topological linear isomorphisms), stated as this identity.  The fibre `Q⁻¹(F(s φ))`
is identified with `Q⁻¹(s(F φ))` (`F(s φ) = s(F φ)`).  Of the hypotheses only the strong bundle
functor part of Definition 8.5.9 (2017: 8.10) is used (`IsStrongBundleFunctor.μ_comm`); (1) makes the `A_y`
topological linear isomorphisms. -/
theorem section_8_5_2 (h : EW.IsProperStrongBundleCovering EV F A) (φ : MorY)
    (v : P ⁻¹' {Y.src φ}) :
    (EV.fiberMor (F.mor φ) ⟨h.fiberEquiv (Y.src φ) v,
        (h.fiberEquiv (Y.src φ) v).2.trans (F.src_mor φ).symm⟩ : V) =
      (h.fiberEquiv (Y.tgt φ) (EW.fiberMor φ v) : V) :=
  h.isStrongBundleFunctor.μ_comm φ v v.2 _

end EpStrongBundle

end ProperBundleCovering'

end Polyfold
