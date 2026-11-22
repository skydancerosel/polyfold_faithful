import Polyfold.Chapter18.MultisectionConstructions
import Polyfold.Chapter16.OrientationTransport
import Polyfold.Chapter12.OrientationFromSection
import Polyfold.Chapter12.OrientationEquivalenceComp
import Polyfold.Chapter12.OrientationMorphismContinuity
import Polyfold.Chapter17.BranchedOrientation


/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.5 "Orientations", pp. 856–859: **Definition 18.5.1** (the orientation category `O_f`),
the paragraphs on `φ_*` and on `Ψ̄_*`, `Ψ̄^*` (pp. 857–858), **Definition 18.5.2** (the
continuity property), **Remark 18.5.3**, **Definition 18.5.4** (orientations), **Remark 18.5.5**
and **Proposition 18.5.6** (left to the reader).  Numbers and pages are the 2021 text's.

# Orientations of sc-Fredholm section functors

The Part III orientations (Definitions 12.5.2 and 12.5.4, Theorems 12.5.3 and 12.5.7) are carried
to a strong polyfold bundle `P : E → C` through the models `W_Ψ̄ → X_Ψ` of covering families of
strong bundle uniformizers and the inclusions of covering families (`bundleIncl`,
`equivalences_bundleIncl`).

## Readings

* **`DET(f, α)` and its orientations** (p. 857).  We read the two-point set
  `{(DET(f, α), o), (DET(f, α), −o)}` as the orientations `Or_{q_α}` of the model section `f^R`
  at the point `q_α` of a chosen `Ψ̄_α ∈ F̄(α)` with `Ψ(q_α) = α`, in the reference model `R`
  (one `Ψ̄_α` for every object, `refCoveringFamily`); `Ψ̄_α` identifies it with the orientations of
  the determinant bundle over `Lin(f, α)` (the `Ψ̄_*` paragraph, p. 858).  `φ_*` is the action of
  the morphism `(q_α, φ, q_α')` of the reference model (`orPush`).
* **Definition 18.5.1.**  The category `O_f` is read as its objects `(α, (DET(f, α), o))`
  (`OrCatObj`), its morphisms `(φ, (DET(f, α), o))` (`OrCatMor`) with source and target, the
  projection `σ`, and the functor laws `(1_α)_* = Id`, `(ψ φ)_* = ψ_* φ_*` (`orPush_unit`,
  `orPush_comp`).
* **`Γ̄^* o`** (pp. 858–859).  For a section `o` of `σ` and a covering family `Ψ̄`, `Γ̄^* o` is the
  section `x ↦ (q_{Γ(x)} → x)_* o_{Γ(x)}` of the reference model (`toRef`) transported to `W_Ψ̄`
  (`pullCat`) along the cospan `W_R → W_{Ψ̄ ⊔ R} ← W_Ψ̄` (`modelTransport`), which represents the
  natural generalized strong bundle isomorphism of Theorem 17.1.18.
* **Definition 18.5.2.**  We read `Γ̄^* o` and `Ψ(ō) = α` as `Ψ̄^* o` and `α_z` (PLAN-18 §4).  The
  local representative `f_Ψ̄` with the orientations `Ψ̄^* o` is read as the piece `Ψ̄` of the model
  of `R ⊔ {Ψ̄}` with `Γ̄^* o`, and "related by continuation near `ō`" as Definition 6.6.12: a
  continuous orientation over an open neighbourhood of `ō` (`HasContinuityProperty`).
* **Orientations of the models** (`IsModelOrientation`) are the invariant sections which are
  continuous orientations over all of `X_Ψ`; by `isModelOrientation_iff` these are the
  orientations of Definition 12.5.4 for every topology on `O_{f^Ψ̄}` with the properties of
  Theorem 6.6.17.
* **Remark 18.5.5.**  `|σ| : |O_f| → |C_∞|` is read as the orbit map of `σ` in the reference
  model (`|X_R| ≅ |C|`, Theorem 17.1.18), and its topology as that of Theorem 6.6.17.
* **Proposition 18.5.6 (3).**  The pull-back of `o'` by `f̄ : W_Ψ̄ → W_Ψ̄'` is read as
  `modelTransport c' c o'`, and "they correspond to the same orientation for `f` provided …" as
  an equivalence (the converse holds as well).

## Hypotheses

The Part I hypotheses of Theorem 6.6.17 in the models are standing hypotheses: `S.IsTame`,
`S.AdmitsModelBumpFunctions` (Definition 18.4.1), the tame form of Definition 18.1.1, and
`F̄(α) ≠ ∅` for every `α`.  All four hold for the diagonal section of the reflection bundle
(`OrientationsExamples.lean`).

## What is formalized

* Transport between covering models: `inclPullOr`, `inclPushOr`, `modelTransport`, the cocycle
  identities `modelTransport_comp`, `modelTransport_modelTransport`, `modelTransport_self`,
  `modelTransport_eq_inclPullOr`, and continuity: `isModelContOrOn_inclPullOr`,
  `isModelContOrOn_inclPushOr`, `exists_isModelContOrOn_of_inclPullOr`,
  `isModelOrientation_modelTransport`.
* Definition 18.5.1: `OrCatObj`, `OrCatMor`, `definition_18_5_1_hyp`, `orPush`, `orPush_unit`,
  `orPush_comp`, `orPush_bijective_two` (two-point fibres, `φ_*` a bijection), and the obstruction
  `not_exists_isOrSectionFunctor` (`g_*(±o) = ∓o` for an isotropy `g` excludes section functors).
* Section functors (`IsOrSectionFunctor`) and invariant sections of the reference model are in
  bijection: `toRef`, `catOf`, `isModelInvariant_toRef`, `catOf_toRef`, `toRef_catOf`,
  `isOrSectionFunctor_catOf`.
* The `Ψ̄^*` paragraph: `inclPullOr_pullCat` and `pullCat_germ` (`Φ̄^* o_Ψ̄' = o_Ψ̄` near `q̄`).
* Definition 18.5.2 `HasContinuityProperty`, Definition 18.5.4 `IsOrientation`, `IsOrientable`.
* **`remark_18_5_3_hyp`**: the continuity property is equivalent to the continuity of `Γ̄^* o` in
  every covering model, and to its form with one `α_z` and one `Ψ̄_z` per class.
* **`remark_18_5_5_mp_hyp`**, **`remark_18_5_5_mpr_hyp`**.
* **`proposition_18_5_6_one_hyp`**, **`proposition_18_5_6_two_hyp`**,
  **`proposition_18_5_6_three_hyp`**.
* `exists_two_orientations`: an orientable `f` has the two orientations `o ≠ −o`.
-/

set_option maxSynthPendingDepth 3
open Set Function Topology
noncomputable section
namespace Polyfold

universe u

section Generic

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
  {Obj'' Mor'' : Type u} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor''] {X'' : EpGroupoid Obj'' Mor''}
  {W'' : Type u} [TopologicalSpace W''] [T2Space W''] [ParacompactSpace W''] {P'' : W'' → Obj''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]
  {B'' : StrongBundle X''.PObj P''} [ParacompactSpace (pullbackSpace P'' X''.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {E'' : EpStrongBundle X'' B''}

namespace EpStrongBundle.IsStrongBundleEquivalence

variable {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  {ψ : EpFunctor X' X''} {Ψ : EpFunctor E'.toEpGroupoid E''.toEpGroupoid}
  (h : E.IsStrongBundleEquivalence E' ϕ Φ) (h' : E'.IsStrongBundleEquivalence E'' ψ Ψ)
  {f : Obj → W} {f' : Obj' → W'} {f'' : Obj'' → W''}
  (hF : E.IsScFredholmSectionFunctor f) (hF' : E'.IsScFredholmSectionFunctor f')
  (hF'' : E''.IsScFredholmSectionFunctor f'') (hpb : f = h.pullback f')
  (hpb' : f' = h'.pullback f'') (hsec : B.HasScPlusSectionsThrough)
  (hsec' : B'.HasScPlusSectionsThrough) (hsec'' : B''.HasScPlusSectionsThrough)

/-- `pushOr` undoes `pullOr` on invariant sections. -/
theorem pushOr_pullOr_of_invariant {o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), Orx f' hF'.2 x hs}
    (ho' : E'.IsOrInvariant hF' hsec' o') :
    h.pushOr hF hF' hpb hsec hsec' (h.pullOr hF hF' hpb hsec hsec' o') = o' :=
  (h.pushOr_unique hF hF' hpb hsec hsec' (h.isOrInvariant_pullOr hF hF' hpb hsec hsec' ho') ho'
    fun _ _ => rfl).symm

/-- **The pull-back along a composite is the composite of the pull-backs.** -/
theorem pullOr_comp_of (hpb'' : f = (h'.comp h).pullback f'')
    (o'' : ∀ x (hs : x ∈ X''.PObj.smoothSet), Orx f'' hF''.2 x hs) :
    (h'.comp h).pullOr hF hF'' hpb'' hsec hsec'' o'' =
      h.pullOr hF hF' hpb hsec hsec' (h'.pullOr hF' hF'' hpb' hsec' hsec'' o'') := by
  funext a hs
  exact h.orEqv_comp h' hF hF' hF'' hpb hpb' hsec hsec' hsec'' a hs _

/-- **The push-forward along a composite is the composite of the push-forwards.** -/
theorem pushOr_comp_of (hpb'' : f = (h'.comp h).pullback f'')
    {o : ∀ x (hs : x ∈ X.PObj.smoothSet), Orx f hF.2 x hs} (ho : E.IsOrInvariant hF hsec o) :
    (h'.comp h).pushOr hF hF'' hpb'' hsec hsec'' o =
      h'.pushOr hF' hF'' hpb' hsec' hsec'' (h.pushOr hF hF' hpb hsec hsec' o) := by
  have ho' := h.isOrInvariant_pushOr hF hF' hpb hsec hsec' ho
  refine ((h'.comp h).pushOr_unique hF hF'' hpb'' hsec hsec'' ho
    (h'.isOrInvariant_pushOr hF' hF'' hpb' hsec' hsec'' ho') fun a ha => ?_).symm
  have e := congrFun (congrFun (h.pullOr_comp_of h' hF hF' hF'' hpb hpb' hsec hsec' hsec'' hpb''
    (h'.pushOr hF' hF'' hpb' hsec' hsec'' (h.pushOr hF hF' hpb hsec hsec' o))) a) ha
  refine e.trans ?_
  rw [h'.pullOr_pushOr hF' hF'' hpb' hsec' hsec'' ho', h.pullOr_pushOr hF hF' hpb hsec hsec' ho]

end EpStrongBundle.IsStrongBundleEquivalence


namespace EpStrongBundle

variable (E) {f : Obj → W} (hF : E.IsScFredholmSectionFunctor f) (hsec : B.HasScPlusSectionsThrough)

/-- Two factorizations of the same morphism act equally on orientations. -/
theorem orMor_orMor_eq {m₁ m₂ n₁ n₂ : Mor} {x y z w : Obj} (h₁x : X.src m₁ = x)
    (h₁y : X.tgt m₁ = y) (h₂y : X.src m₂ = y) (h₂z : X.tgt m₂ = z) (k₁x : X.src n₁ = x)
    (k₁w : X.tgt n₁ = w) (k₂w : X.src n₂ = w) (k₂z : X.tgt n₂ = z)
    (hs : x ∈ X.PObj.smoothSet) (hsy : y ∈ X.PObj.smoothSet) (hsw : w ∈ X.PObj.smoothSet)
    (hsz : z ∈ X.PObj.smoothSet) (h : X.comp m₂ m₁ = X.comp n₂ n₁) (ω : Orx f hF.2 x hs) :
    E.orMor hF hsec m₂ h₂y h₂z hsy hsz (E.orMor hF hsec m₁ h₁x h₁y hs hsy ω) =
      E.orMor hF hsec n₂ k₂w k₂z hsw hsz (E.orMor hF hsec n₁ k₁x k₁w hs hsw ω) := by
  rw [← Equiv.trans_apply, E.orMor_comp hF hsec h₁x h₁y h₂y h₂z hs hsy hsz, ← Equiv.trans_apply,
    E.orMor_comp hF hsec k₁x k₁w k₂w k₂z hs hsw hsz, E.orMor_congr hF hsec h]

end EpStrongBundle


section Other

variable {X' : Type u} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX : MPolyfold X'}
  {Y : Type u} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X'}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X' → Y} (hf : B.IsScFredholmSection f) (hsec : B.HasScPlusSectionsThrough)

include hsec

theorem exists_ne_orx (o : ∀ x (hs : x ∈ PX.smoothSet), Orx f hf x hs) {x : X'}
    (hs : x ∈ PX.smoothSet) : ∃ ω : Orx f hf x hs, ω ≠ o x hs := by
  obtain ⟨o₁, o₂, hne, -⟩ := ChartPoint.exists_two_or _ hf hs hsec
  by_cases h : o₁ = o x hs
  · exact ⟨o₂, fun h' => hne (h.trans h'.symm)⟩
  · exact ⟨o₁, h⟩

/-- **The other orientation `−o`**: at every smooth point, the orientation of `DET(f, x)`
different from `o_x` (p. 857: "the only other possible orientation is then `−o`"). -/
def otherOr (o : ∀ x (hs : x ∈ PX.smoothSet), Orx f hf x hs) :
    ∀ x (hs : x ∈ PX.smoothSet), Orx f hf x hs := fun _ hs =>
  (exists_ne_orx hf hsec o hs).choose

theorem otherOr_ne (o : ∀ x (hs : x ∈ PX.smoothSet), Orx f hf x hs) {x : X'}
    (hs : x ∈ PX.smoothSet) : otherOr hf hsec o x hs ≠ o x hs :=
  (exists_ne_orx hf hsec o hs).choose_spec

theorem eq_otherOr_of_ne (o : ∀ x (hs : x ∈ PX.smoothSet), Orx f hf x hs) {x : X'}
    (hs : x ∈ PX.smoothSet) {ω : Orx f hf x hs} (hω : ω ≠ o x hs) : ω = otherOr hf hsec o x hs := by
  obtain ⟨o₁, o₂, hne, hall⟩ := ChartPoint.exists_two_or _ hf hs hsec
  have hne' := otherOr_ne hf hsec o hs
  rcases hall ω with h1 | h1 <;> rcases hall (o x hs) with h2 | h2 <;>
    rcases hall (otherOr hf hsec o x hs) with h3 | h3 <;> simp_all

/-- A bijection carrying `o_x` to `o_y` carries `−o_x` to `−o_y`. -/
theorem equiv_otherOr (o : ∀ x (hs : x ∈ PX.smoothSet), Orx f hf x hs) {x y : X'}
    {hx : x ∈ PX.smoothSet} {hy : y ∈ PX.smoothSet} (e : Orx f hf x hx ≃ Orx f hf y hy)
    (he : e (o x hx) = o y hy) : e (otherOr hf hsec o x hx) = otherOr hf hsec o y hy :=
  eq_otherOr_of_ne hf hsec o hy fun h =>
    otherOr_ne hf hsec o hx (e.injective (h.trans he.symm))

theorem isContOrOn_otherOr {L : LocalTransport PX fun x hs => Orx f hf x hs} {U : Set X'}
    {o : ∀ x (hs : x ∈ PX.smoothSet), Orx f hf x hs} (h : IsContOrOn L U o) :
    IsContOrOn L U (otherOr hf hsec o) :=
  ⟨h.1, fun γ hγ hU _ _ h₀ h₁ hs₀ hs₁ => equiv_otherOr hf hsec o _ (h.2 γ hγ hU h₀ h₁ hs₀ hs₁)⟩

end Other

theorem EpStrongBundle.isOrInvariant_otherOr {f : Obj → W} (hF : E.IsScFredholmSectionFunctor f)
    (hsec : B.HasScPlusSectionsThrough) {o : ∀ x (hs : x ∈ X.PObj.smoothSet), Orx f hF.2 x hs}
    (ho : E.IsOrInvariant hF hsec o) : E.IsOrInvariant hF hsec (otherOr hF.2 hsec o) :=
  fun φ _ _ hx hx' hs hs' => equiv_otherOr hF.2 hsec o _ (ho φ hx hx' hs hs')

namespace SBLocalization

open CategoryTheory

variable {A A₁ K M : SEP.{u}}

/-- **The pull-back along `F ≫ G` is the composite of the pull-backs**, for strong bundle
equivalences of `SEP`. -/
theorem pullOr_sbe_of_comp_eq {F : A ⟶ K} {G : K ⟶ M} {H : A ⟶ M} (hFG : F ≫ G = H)
    (hFe : SEP.equivalences F) (hGe : SEP.equivalences G) (hHe : SEP.equivalences H)
    {f : A.Obj → A.W} {fK : K.Obj → K.W} {fM : M.Obj → M.W}
    (hF : A.E.IsScFredholmSectionFunctor f) (hFK : K.E.IsScFredholmSectionFunctor fK)
    (hFM : M.E.IsScFredholmSectionFunctor fM) (hpbF : f = (sbe hFe).pullback fK)
    (hpbG : fK = (sbe hGe).pullback fM) (hpbH : f = (sbe hHe).pullback fM)
    (hsec : A.B.HasScPlusSectionsThrough) (hsecK : K.B.HasScPlusSectionsThrough)
    (hsecM : M.B.HasScPlusSectionsThrough)
    (o : ∀ x (hs : x ∈ M.X.PObj.smoothSet), Orx fM hFM.2 x hs) :
    (sbe hHe).pullOr hF hFM hpbH hsec hsecM o =
      (sbe hFe).pullOr hF hFK hpbF hsec hsecK ((sbe hGe).pullOr hFK hFM hpbG hsecK hsecM o) := by
  subst hFG
  exact (sbe hFe).pullOr_comp_of (sbe hGe) hF hFK hFM hpbF hpbG hsec hsecK hsecM hpbH o

/-- **The push-forward along `F ≫ G` is the composite of the push-forwards** (invariant
sections). -/
theorem pushOr_sbe_of_comp_eq {F : A ⟶ K} {G : K ⟶ M} {H : A ⟶ M} (hFG : F ≫ G = H)
    (hFe : SEP.equivalences F) (hGe : SEP.equivalences G) (hHe : SEP.equivalences H)
    {f : A.Obj → A.W} {fK : K.Obj → K.W} {fM : M.Obj → M.W}
    (hF : A.E.IsScFredholmSectionFunctor f) (hFK : K.E.IsScFredholmSectionFunctor fK)
    (hFM : M.E.IsScFredholmSectionFunctor fM) (hpbF : f = (sbe hFe).pullback fK)
    (hpbG : fK = (sbe hGe).pullback fM) (hpbH : f = (sbe hHe).pullback fM)
    (hsec : A.B.HasScPlusSectionsThrough) (hsecK : K.B.HasScPlusSectionsThrough)
    (hsecM : M.B.HasScPlusSectionsThrough)
    {o : ∀ x (hs : x ∈ A.X.PObj.smoothSet), Orx f hF.2 x hs} (ho : A.E.IsOrInvariant hF hsec o) :
    (sbe hHe).pushOr hF hFM hpbH hsec hsecM o =
      (sbe hGe).pushOr hFK hFM hpbG hsecK hsecM ((sbe hFe).pushOr hF hFK hpbF hsec hsecK o) := by
  subst hFG
  exact (sbe hFe).pushOr_comp_of (sbe hGe) hF hFK hFM hpbF hpbG hsec hsecK hsecM hpbH ho

end SBLocalization

end Generic

section GenericCont

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
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'}

namespace EpStrongBundle.IsStrongBundleEquivalence

variable {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (h : E.IsStrongBundleEquivalence E' ϕ Φ)
  {f : Obj → W} {f' : Obj' → W'}
  (hF : E.IsScFredholmSectionFunctor f) (hF' : E'.IsScFredholmSectionFunctor f')
  (hpb : f = h.pullback f') (hsec : B.HasScPlusSectionsThrough)
  (hsec' : B'.HasScPlusSectionsThrough)
  (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions) (hfT : B.IsScFredholmSectionTame f)
  (hX' : X'.PObj.IsTame) (hbump' : X'.PObj.AdmitsBumpFunctions)
  (hfT' : B'.IsScFredholmSectionTame f')
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj')]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P' (Prod.snd : (Fin n → ℝ) × Obj' → Obj'))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj'))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P' (Prod.snd : (Fin n → ℝ) × Obj' → Obj'))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj') → (Fin n → ℝ) × Obj'))]

/-- **Continuity near a point passes from the pull-back to the section** (the local form of the
push-forward half of Theorem 12.5.7 (2)): if `pullOr o'` is a continuous orientation over an
open `U ∋ a`, then `o'` is a continuous orientation over an open neighbourhood of `ϕ(a)`. -/
theorem exists_isContOrOn_of_pullOr {U : Set Obj} {a : Obj} (ha : a ∈ U)
    {o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), Orx f' hF'.2 x hs}
    (hc : IsContOrOn (orLocalTransport hX hbump hfT hsec) U
      (h.pullOr hF hF' hpb hsec hsec' o')) :
    ∃ V', IsOpen V' ∧ ϕ.obj a ∈ V' ∧
      IsContOrOn (orLocalTransport hX' hbump' hfT' hsec') V' o' := by
  set L := h.locIso a
  have hV' : IsOpen (h.locSet' a ∩ L.g ⁻¹' U) :=
    L.base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage (h.isOpen_locSet' a) hc.1
  have hsub : h.locSet a ∩ L.ϕ ⁻¹' (h.locSet' a ∩ L.g ⁻¹' U) ⊆ U := fun y hy => by
    have := hy.2.2
    simp only [mem_preimage] at this
    rwa [L.base.left_inv y hy.1] at this
  have hopen : IsOpen (h.locSet a ∩ L.ϕ ⁻¹' (h.locSet' a ∩ L.g ⁻¹' U)) :=
    L.base.isScSmoothOn.continuousOn.isOpen_inter_preimage (h.isOpen_locSet a) hV'
  have hloc := (hc.mono_or hopen hsub).congr_or (o' := L.pullOrx hF.2 hF'.2
      (h.eqOn_loc hpb hF'.2.isScSmooth.1 a) hsec hsec' o') fun y hy hys =>
    (h.pullOr_eq_pullOrx hF hF' hpb hsec hsec' a o' hy.1 hys).symm
  refine ⟨_, (h.isOpen_locSet' a).inter hV', ⟨h.obj_mem_locSet' a, h.obj_mem_locSet' a, ?_⟩,
    L.isContOrOn_of_pullOrx hX hbump hfT hsec hX' hbump' hfT' hsec'
      (h.eqOn_loc hpb hF'.2.isScSmooth.1 a) hV' hloc⟩
  change L.g (L.ϕ a) ∈ U
  rw [L.base.left_inv a (h.mem_locSet a)]
  exact ha

end EpStrongBundle.IsStrongBundleEquivalence


namespace EpStrongBundle

variable (E) {f : Obj → W} (hF : E.IsScFredholmSectionFunctor f) (hsec : B.HasScPlusSectionsThrough)
  (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions) (hfT : B.IsScFredholmSectionTame f)
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]

/-- **Continuity near a point passes along a morphism** for invariant sections (Theorem 12.5.3,
last sentence): if `o` is invariant and a continuous orientation over an open `V ∋ x`, and
`σ : x → x'`, then `o` is a continuous orientation over an open neighbourhood of `x'`. -/
theorem exists_isContOrOn_of_mor {o : ∀ y (hy : y ∈ X.PObj.smoothSet), Orx f hF.2 y hy}
    (hinv : E.IsOrInvariant hF hsec o) (σ : Mor) {x x' : Obj} (hx : X.src σ = x)
    (hx' : X.tgt σ = x') (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet)
    {V : Set Obj} (hxV : x ∈ V) (ho : IsContOrOn (orLocalTransport hX hbump hfT hsec) V o) :
    ∃ V', x' ∈ V' ∧ IsContOrOn (orLocalTransport hX hbump hfT hsec) V' o := by
  obtain ⟨hC, hmem, -⟩ := E.theorem_12_5_3_push_hyp hF hsec hX hbump hfT σ hx hx' hs hs' ho
  refine ⟨_, hmem hxV, hC.congr_or fun y' hy' hys' => ?_⟩
  have hϕs : (E.morIso σ).ϕ y' ∈ X.PObj.smoothSet :=
    ((E.morIso σ).mem_smoothSet_iff hy'.1).1 hys'
  rw [E.pullOrx_morIso_eq_orMor hF hsec σ hy'.1 hϕs hys' o]
  exact hinv _ _ _ _ _

end EpStrongBundle

end GenericCont

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open PolyfoldConstruction SBLocalization EpStrongBundle

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  (Q : V.StrongPolyfoldBundleConstruction S) {f : V.SectionFunctor}

section ModelData

variable {ι : Type u} (Ψb : ι → Q.Unif)

/-- The section `f^Ψ̄_Ψ` of every model is an sc-Fredholm section functor (Remark 18.1.2 (a)). -/
theorem modelFred (hf : Q.IsScFredholmSectionFunctor f) :
    (Q.modelSEP Ψb).E.IsScFredholmSectionFunctor (Q.modelSection Ψb f) :=
  (Q.isScFredholmSectionFunctor_model_iff f Ψb).2 fun i =>
    (Q.isScFredholmSectionFunctor_iff_unif f).1 hf (Ψb i)

/-- The model section is tame sc-Fredholm when `f` is (Definition 18.1.1, tame form). -/
theorem modelFredTame (hfT : Q.IsScFredholmSectionFunctorTame f) :
    (Q.modelSEP Ψb).B.IsScFredholmSectionTame (Q.modelSection Ψb f) :=
  (Q.isScFredholmSectionTame_model_iff f Ψb).2 fun i =>
    (Q.isScFredholmSectionFunctorTame_iff_unif f).1 hfT (Ψb i)

/-- Every model of a tame polyfold structure is tame (Proposition 17.1.17 with
Definition 17.1.20). -/
theorem modelTame (hT : S.IsTame) : (Q.modelSEP Ψb).X.PObj.IsTame :=
  S.isTame_modelEpGroupoid (Q.modelBase Ψb) hT

end ModelData

/-- Bump functions on every covering model (Definition 18.4.1 and Remark 18.4.2, with
Theorem 12.3.2 (1)). -/
theorem modelBump (hbump : S.AdmitsModelBumpFunctions) (c : Q.BundleCoveringFamily) :
    (Q.modelSEP c.Ψ).X.PObj.AdmitsBumpFunctions := by
  obtain ⟨c₀, h⟩ := hbump
  exact EpGroupoid.theorem_12_3_2_1.1 ((S.admitsBumpFunctionsPointwise_model_iff c₀ c.base).1 h)

/-- sc⁺-sections through every point of a covering model (Part I's standing hypothesis). -/
theorem modelSec (hbump : S.AdmitsModelBumpFunctions) (c : Q.BundleCoveringFamily) :
    (Q.modelSEP c.Ψ).B.HasScPlusSectionsThrough :=
  (Q.modelBump hbump c).hasScPlusSectionsThrough

/-- **The covering family `Ψ̄ ⊔ Ψ̄'`.** -/
abbrev sumFamily (c d : Q.BundleCoveringFamily) : Q.BundleCoveringFamily where
  ι := c.ι ⊕ d.ι
  Ψ := Sum.elim c.Ψ d.Ψ
  cover := by
    refine eq_univ_of_forall fun z => ?_
    have hz : z ∈ ⋃ i, (Q.modelBase c.Ψ i).1.footprint := c.cover.symm ▸ mem_univ z
    obtain ⟨i, hi⟩ := mem_iUnion.1 hz
    exact mem_iUnion.2 ⟨Sum.inl i, hi⟩

variable (hf : Q.IsScFredholmSectionFunctor f) (hbump : S.AdmitsModelBumpFunctions)

/-- **Sections of `σ : O_{f^Ψ̄} → (X_Ψ)_∞`** in a covering model. -/
abbrev ModelOr (c : Q.BundleCoveringFamily) : Type u :=
  ∀ (x : (Q.modelSEP c.Ψ).Obj) (hs : x ∈ (Q.modelSEP c.Ψ).X.PObj.smoothSet),
    Orx (B := (Q.modelSEP c.Ψ).B) (Q.modelSection c.Ψ f) (Q.modelFred c.Ψ hf).2 x hs

/-- The invariance clause of Definition 12.5.4 in a covering model. -/
abbrev IsModelInvariant (c : Q.BundleCoveringFamily) (o : Q.ModelOr hf c) : Prop :=
  (Q.modelSEP c.Ψ).E.IsOrInvariant (Q.modelFred c.Ψ hf) (Q.modelSec hbump c) o

variable {c d : Q.BundleCoveringFamily}

/-- **The pull-back of a section along an inclusion `W_Ψ̄ → W_Φ̄` of covering families.** -/
def inclPullOr (σ : c.ι → d.ι) (h : d.Ψ ∘ σ = c.Ψ) (o : Q.ModelOr hf d) : Q.ModelOr hf c :=
  (sbe (Q.equivalences_bundleIncl h c.cover)).pullOr (Q.modelFred c.Ψ hf) (Q.modelFred d.Ψ hf)
    (Q.pullback_modelSection f d.Ψ h c.cover).symm (Q.modelSec hbump c) (Q.modelSec hbump d) o

/-- **The push-forward of a section along an inclusion `W_Ψ̄ → W_Φ̄` of covering families.** -/
def inclPushOr (σ : c.ι → d.ι) (h : d.Ψ ∘ σ = c.Ψ) (o : Q.ModelOr hf c) : Q.ModelOr hf d :=
  (sbe (Q.equivalences_bundleIncl h c.cover)).pushOr (Q.modelFred c.Ψ hf) (Q.modelFred d.Ψ hf)
    (Q.pullback_modelSection f d.Ψ h c.cover).symm (Q.modelSec hbump c) (Q.modelSec hbump d) o

theorem isModelInvariant_inclPullOr (σ : c.ι → d.ι) (h : d.Ψ ∘ σ = c.Ψ) {o : Q.ModelOr hf d}
    (ho : Q.IsModelInvariant hf hbump d o) :
    Q.IsModelInvariant hf hbump c (Q.inclPullOr hf hbump σ h o) :=
  (sbe (Q.equivalences_bundleIncl h c.cover)).isOrInvariant_pullOr _ _ _ _ _ ho

theorem isModelInvariant_inclPushOr (σ : c.ι → d.ι) (h : d.Ψ ∘ σ = c.Ψ) {o : Q.ModelOr hf c}
    (ho : Q.IsModelInvariant hf hbump c o) :
    Q.IsModelInvariant hf hbump d (Q.inclPushOr hf hbump σ h o) :=
  (sbe (Q.equivalences_bundleIncl h c.cover)).isOrInvariant_pushOr _ _ _ _ _ ho

theorem inclPullOr_inclPushOr (σ : c.ι → d.ι) (h : d.Ψ ∘ σ = c.Ψ) {o : Q.ModelOr hf c}
    (ho : Q.IsModelInvariant hf hbump c o) :
    Q.inclPullOr hf hbump σ h (Q.inclPushOr hf hbump σ h o) = o :=
  (sbe (Q.equivalences_bundleIncl h c.cover)).pullOr_pushOr _ _ _ _ _ ho

theorem inclPushOr_inclPullOr (σ : c.ι → d.ι) (h : d.Ψ ∘ σ = c.Ψ) {o : Q.ModelOr hf d}
    (ho : Q.IsModelInvariant hf hbump d o) :
    Q.inclPushOr hf hbump σ h (Q.inclPullOr hf hbump σ h o) = o :=
  (sbe (Q.equivalences_bundleIncl h c.cover)).pushOr_pullOr_of_invariant _ _ _ _ _ ho

theorem inclPullOr_comp {e : Q.BundleCoveringFamily} (σ : c.ι → d.ι) (τ : d.ι → e.ι)
    (h : d.Ψ ∘ σ = c.Ψ) (h' : e.Ψ ∘ τ = d.Ψ) (h'' : e.Ψ ∘ (τ ∘ σ) = c.Ψ) (o : Q.ModelOr hf e) :
    Q.inclPullOr hf hbump (τ ∘ σ) h'' o =
      Q.inclPullOr hf hbump σ h (Q.inclPullOr hf hbump τ h' o) :=
  pullOr_sbe_of_comp_eq (Q.bundleIncl_comp h h' h'' rfl) (Q.equivalences_bundleIncl h c.cover)
    (Q.equivalences_bundleIncl h' d.cover) (Q.equivalences_bundleIncl h'' c.cover) _ _ _ _ _ _ _ _
    _ o

theorem inclPushOr_comp {e : Q.BundleCoveringFamily} (σ : c.ι → d.ι) (τ : d.ι → e.ι)
    (h : d.Ψ ∘ σ = c.Ψ) (h' : e.Ψ ∘ τ = d.Ψ) (h'' : e.Ψ ∘ (τ ∘ σ) = c.Ψ) {o : Q.ModelOr hf c}
    (ho : Q.IsModelInvariant hf hbump c o) :
    Q.inclPushOr hf hbump (τ ∘ σ) h'' o =
      Q.inclPushOr hf hbump τ h' (Q.inclPushOr hf hbump σ h o) :=
  pushOr_sbe_of_comp_eq (Q.bundleIncl_comp h h' h'' rfl) (Q.equivalences_bundleIncl h c.cover)
    (Q.equivalences_bundleIncl h' d.cover) (Q.equivalences_bundleIncl h'' c.cover) _ _ _ _ _ _ _ _
    _ ho

/-! ### Transport between two covering models -/

/-- **Transport of a section from the model of `a` to the model of `b`**: the push-forward along
`W_a → W_{b ⊔ a}`, pulled back along `W_b → W_{b ⊔ a}`.  This cospan represents the natural
generalized strong bundle isomorphism `f̄_{b,a} : W_b → W_a` (`bundleComparison_comp_incl`), and
`modelTransport a b o` is the pull-back of `o` by `f̄_{b,a}`. -/
def modelTransport (a b : Q.BundleCoveringFamily) (o : Q.ModelOr hf a) : Q.ModelOr hf b :=
  Q.inclPullOr hf hbump (d := Q.sumFamily b a) Sum.inl rfl
    (Q.inclPushOr hf hbump (d := Q.sumFamily b a) Sum.inr rfl o)

theorem isModelInvariant_modelTransport (a b : Q.BundleCoveringFamily) {o : Q.ModelOr hf a}
    (ho : Q.IsModelInvariant hf hbump a o) :
    Q.IsModelInvariant hf hbump b (Q.modelTransport hf hbump a b o) :=
  Q.isModelInvariant_inclPullOr hf hbump _ _ (Q.isModelInvariant_inclPushOr hf hbump _ _ ho)

/-- **The transport through a larger family**: for `τ : b ⊔ a → M`, the transport is the
push-forward along `W_a → W_M`, pulled back along `W_b → W_M`. -/
theorem modelTransport_eq_via {a b M : Q.BundleCoveringFamily} (τ : (Q.sumFamily b a).ι → M.ι)
    (hτ : M.Ψ ∘ τ = (Q.sumFamily b a).Ψ) {σa : a.ι → M.ι} {σb : b.ι → M.ι}
    (ha : M.Ψ ∘ σa = a.Ψ) (hb : M.Ψ ∘ σb = b.Ψ) (hσa : τ ∘ Sum.inr = σa) (hσb : τ ∘ Sum.inl = σb)
    {o : Q.ModelOr hf a} (ho : Q.IsModelInvariant hf hbump a o) :
    Q.modelTransport hf hbump a b o =
      Q.inclPullOr hf hbump σb hb (Q.inclPushOr hf hbump σa ha o) := by
  subst hσa hσb
  have hl : (Q.sumFamily b a).Ψ ∘ Sum.inl = b.Ψ := rfl
  have hr : (Q.sumFamily b a).Ψ ∘ Sum.inr = a.Ψ := rfl
  have e1 := Q.inclPullOr_comp hf hbump (c := b) (d := Q.sumFamily b a) (e := M) Sum.inl τ hl hτ
    hb (Q.inclPushOr hf hbump (τ ∘ Sum.inr) ha o)
  have e2 := Q.inclPushOr_comp hf hbump (c := a) (d := Q.sumFamily b a) (e := M) Sum.inr τ hr hτ
    ha ho
  have e3 := Q.inclPullOr_inclPushOr hf hbump τ hτ
    (Q.isModelInvariant_inclPushOr hf hbump (d := Q.sumFamily b a) Sum.inr hr ho)
  rw [e1, e2, e3]
  rfl

/-- **The cocycle identity of the transports** (the orientation form of
`bundleComparison_comp`). -/
theorem modelTransport_comp (a b c : Q.BundleCoveringFamily) {o : Q.ModelOr hf a}
    (ho : Q.IsModelInvariant hf hbump a o) :
    Q.modelTransport hf hbump b c (Q.modelTransport hf hbump a b o) =
      Q.modelTransport hf hbump a c o := by
  set M := Q.sumFamily c (Q.sumFamily b a)
  have h₂ : M.Ψ ∘ Sum.map id Sum.inl = (Q.sumFamily c b).Ψ := by
    funext x; cases x <;> rfl
  have h₃ : M.Ψ ∘ Sum.map id Sum.inr = (Q.sumFamily c a).Ψ := by
    funext x; cases x <;> rfl
  have hA : M.Ψ ∘ (Sum.inr ∘ Sum.inr) = a.Ψ := rfl
  have hB : M.Ψ ∘ (Sum.inr ∘ Sum.inl) = b.Ψ := rfl
  have hC : M.Ψ ∘ Sum.inl = c.Ψ := rfl
  rw [Q.modelTransport_eq_via hf hbump (M := M) Sum.inr rfl hA hB rfl rfl ho,
    Q.modelTransport_eq_via hf hbump (M := M) (Sum.map id Sum.inl) h₂ hB hC rfl rfl
      (Q.isModelInvariant_inclPullOr hf hbump (d := M) _ hB
        (Q.isModelInvariant_inclPushOr hf hbump (d := M) _ hA ho)),
    Q.inclPushOr_inclPullOr hf hbump _ hB (Q.isModelInvariant_inclPushOr hf hbump (d := M) _ hA ho),
    Q.modelTransport_eq_via hf hbump (M := M) (Sum.map id Sum.inr) h₃ hA hC rfl rfl ho]

/-- **The transport back is the inverse** (`f̄_{a,b} ∘ f̄_{b,a} = 1`). -/
theorem modelTransport_modelTransport (a b : Q.BundleCoveringFamily) {o : Q.ModelOr hf a}
    (ho : Q.IsModelInvariant hf hbump a o) :
    Q.modelTransport hf hbump b a (Q.modelTransport hf hbump a b o) = o := by
  set M := Q.sumFamily a b
  have h₁ : M.Ψ ∘ Sum.swap = (Q.sumFamily b a).Ψ := by
    funext x; cases x <;> rfl
  have hA : M.Ψ ∘ Sum.inl = a.Ψ := rfl
  have hB : M.Ψ ∘ Sum.inr = b.Ψ := rfl
  rw [Q.modelTransport_eq_via hf hbump (M := M) Sum.swap h₁ hA hB rfl rfl ho,
    Q.modelTransport_eq_via hf hbump (M := M) id rfl hB hA rfl rfl
      (Q.isModelInvariant_inclPullOr hf hbump (d := M) _ hB
        (Q.isModelInvariant_inclPushOr hf hbump (d := M) _ hA ho)),
    Q.inclPushOr_inclPullOr hf hbump _ hB (Q.isModelInvariant_inclPushOr hf hbump (d := M) _ hA ho),
    Q.inclPullOr_inclPushOr hf hbump _ hA ho]


/-! ### Continuity in the covering models -/

section Continuity

variable (hT : S.IsTame) (hfT : Q.IsScFredholmSectionFunctorTame f)

/-- **A continuous orientation over `U` in a covering model**: Definition 6.6.12 (p. 263) for the
model section `f^Ψ̄` of `W_Ψ̄ → X_Ψ`, with the local transport of Theorem 6.6.13. -/
def IsModelContOrOn (c : Q.BundleCoveringFamily) (U : Set (Q.modelSEP c.Ψ).Obj)
    (o : Q.ModelOr hf c) : Prop :=
  haveI := paracompactSpace_rn_prod (Q.modelSEP c.Ψ).X.PObj
  haveI := paracompactSpace_rn_pullback (Q.modelSEP c.Ψ).B
  haveI := paracompactSpace_rn_rn_prod (Q.modelSEP c.Ψ).X.PObj
  haveI := paracompactSpace_rn_rn_pullback (Q.modelSEP c.Ψ).B
  IsContOrOn (orLocalTransport (Q.modelTame c.Ψ hT) (Q.modelBump hbump c)
    (Q.modelFredTame c.Ψ hfT) (Q.modelSec hbump c)) U o

/-- **An orientation of the model section `f^Ψ̄`** (Definition 12.5.4, p. 593, in the form of
`isModelOrientation_iff`): an invariant section of `σ : O_{f^Ψ̄} → (X_Ψ)_∞` which is a continuous
orientation over all of `X_Ψ`. -/
def IsModelOrientation (c : Q.BundleCoveringFamily) (o : Q.ModelOr hf c) : Prop :=
  Q.IsModelInvariant hf hbump c o ∧ Q.IsModelContOrOn hf hbump hT hfT c univ o

/-- **Pull-back of continuity along an inclusion** (Theorem 12.5.7 (2), pull-back half). -/
theorem isModelContOrOn_inclPullOr (σ : c.ι → d.ι) (h : d.Ψ ∘ σ = c.Ψ)
    {V : Set (Q.modelSEP d.Ψ).Obj}
    {o : Q.ModelOr hf d} (ho : Q.IsModelContOrOn hf hbump hT hfT d V o) :
    Q.IsModelContOrOn hf hbump hT hfT c
      ((SEP.Hom.ϕ (Q.bundleIncl c.Ψ d.Ψ σ h)).obj ⁻¹' V) (Q.inclPullOr hf hbump σ h o) := by
  have := paracompactSpace_rn_prod (Q.modelSEP c.Ψ).X.PObj
  have := paracompactSpace_rn_pullback (Q.modelSEP c.Ψ).B
  have := paracompactSpace_rn_rn_prod (Q.modelSEP c.Ψ).X.PObj
  have := paracompactSpace_rn_rn_pullback (Q.modelSEP c.Ψ).B
  have := paracompactSpace_rn_prod (Q.modelSEP d.Ψ).X.PObj
  have := paracompactSpace_rn_pullback (Q.modelSEP d.Ψ).B
  have := paracompactSpace_rn_rn_prod (Q.modelSEP d.Ψ).X.PObj
  have := paracompactSpace_rn_rn_pullback (Q.modelSEP d.Ψ).B
  exact (sbe (Q.equivalences_bundleIncl h c.cover)).isContOrOn_pullOr_hyp
    (hX := Q.modelTame c.Ψ hT) (hbump := Q.modelBump hbump c) (hfT := Q.modelFredTame c.Ψ hfT)
    (hX' := Q.modelTame d.Ψ hT) (hbump' := Q.modelBump hbump d)
    (hfT' := Q.modelFredTame d.Ψ hfT) _ _ _ _ _ ho

/-- **Push-forward of an orientation along an inclusion** (Theorem 12.5.7 (2), push-forward
half). -/
theorem isModelContOrOn_inclPushOr (σ : c.ι → d.ι) (h : d.Ψ ∘ σ = c.Ψ) {o : Q.ModelOr hf c}
    (hi : Q.IsModelInvariant hf hbump c o) (ho : Q.IsModelContOrOn hf hbump hT hfT c univ o) :
    Q.IsModelContOrOn hf hbump hT hfT d univ (Q.inclPushOr hf hbump σ h o) := by
  have := paracompactSpace_rn_prod (Q.modelSEP c.Ψ).X.PObj
  have := paracompactSpace_rn_pullback (Q.modelSEP c.Ψ).B
  have := paracompactSpace_rn_rn_prod (Q.modelSEP c.Ψ).X.PObj
  have := paracompactSpace_rn_rn_pullback (Q.modelSEP c.Ψ).B
  have := paracompactSpace_rn_prod (Q.modelSEP d.Ψ).X.PObj
  have := paracompactSpace_rn_pullback (Q.modelSEP d.Ψ).B
  have := paracompactSpace_rn_rn_prod (Q.modelSEP d.Ψ).X.PObj
  have := paracompactSpace_rn_rn_pullback (Q.modelSEP d.Ψ).B
  exact (sbe (Q.equivalences_bundleIncl h c.cover)).isContOrOn_pushOr_hyp
    (hX := Q.modelTame c.Ψ hT) (hbump := Q.modelBump hbump c) (hfT := Q.modelFredTame c.Ψ hfT)
    (hX' := Q.modelTame d.Ψ hT) (hbump' := Q.modelBump hbump d)
    (hfT' := Q.modelFredTame d.Ψ hfT) _ _ _ _ _ hi ho

/-- **Continuity near a point passes along an inclusion**: if the pull-back of `o` is a
continuous orientation over an open `U ∋ x`, then `o` is one over an open neighbourhood of the
image of `x`. -/
theorem exists_isModelContOrOn_of_inclPullOr (σ : c.ι → d.ι) (h : d.Ψ ∘ σ = c.Ψ)
    {U : Set (Q.modelSEP c.Ψ).Obj} {x : (Q.modelSEP c.Ψ).Obj} (hx : x ∈ U) {o : Q.ModelOr hf d}
    (hc : Q.IsModelContOrOn hf hbump hT hfT c U (Q.inclPullOr hf hbump σ h o)) :
    ∃ V, IsOpen V ∧ (SEP.Hom.ϕ (Q.bundleIncl c.Ψ d.Ψ σ h)).obj x ∈ V ∧
      Q.IsModelContOrOn hf hbump hT hfT d V o := by
  have := paracompactSpace_rn_prod (Q.modelSEP c.Ψ).X.PObj
  have := paracompactSpace_rn_pullback (Q.modelSEP c.Ψ).B
  have := paracompactSpace_rn_rn_prod (Q.modelSEP c.Ψ).X.PObj
  have := paracompactSpace_rn_rn_pullback (Q.modelSEP c.Ψ).B
  have := paracompactSpace_rn_prod (Q.modelSEP d.Ψ).X.PObj
  have := paracompactSpace_rn_pullback (Q.modelSEP d.Ψ).B
  have := paracompactSpace_rn_rn_prod (Q.modelSEP d.Ψ).X.PObj
  have := paracompactSpace_rn_rn_pullback (Q.modelSEP d.Ψ).B
  exact (sbe (Q.equivalences_bundleIncl h c.cover)).exists_isContOrOn_of_pullOr _ _ _ _ _
    (Q.modelTame c.Ψ hT) (Q.modelBump hbump c) (Q.modelFredTame c.Ψ hfT)
    (Q.modelTame d.Ψ hT) (Q.modelBump hbump d) (Q.modelFredTame d.Ψ hfT) hx hc

theorem isModelOrientation_inclPullOr (σ : c.ι → d.ι) (h : d.Ψ ∘ σ = c.Ψ) {o : Q.ModelOr hf d}
    (ho : Q.IsModelOrientation hf hbump hT hfT d o) :
    Q.IsModelOrientation hf hbump hT hfT c (Q.inclPullOr hf hbump σ h o) :=
  ⟨Q.isModelInvariant_inclPullOr hf hbump σ h ho.1,
    Q.isModelContOrOn_inclPullOr hf hbump hT hfT σ h ho.2⟩

theorem isModelOrientation_inclPushOr (σ : c.ι → d.ι) (h : d.Ψ ∘ σ = c.Ψ) {o : Q.ModelOr hf c}
    (ho : Q.IsModelOrientation hf hbump hT hfT c o) :
    Q.IsModelOrientation hf hbump hT hfT d (Q.inclPushOr hf hbump σ h o) :=
  ⟨Q.isModelInvariant_inclPushOr hf hbump σ h ho.1,
    Q.isModelContOrOn_inclPushOr hf hbump hT hfT σ h ho.1 ho.2⟩

/-- **The transport of an orientation is an orientation.** -/
theorem isModelOrientation_modelTransport (a b : Q.BundleCoveringFamily) {o : Q.ModelOr hf a}
    (ho : Q.IsModelOrientation hf hbump hT hfT a o) :
    Q.IsModelOrientation hf hbump hT hfT b (Q.modelTransport hf hbump a b o) :=
  Q.isModelOrientation_inclPullOr hf hbump hT hfT _ _
    (Q.isModelOrientation_inclPushOr hf hbump hT hfT _ _ ho)

end Continuity


/-! ### Identities of the transports -/

/-- The push-forward along the identity inclusion is the identity on invariant sections. -/
theorem inclPushOr_id {o : Q.ModelOr hf c} (ho : Q.IsModelInvariant hf hbump c o) :
    Q.inclPushOr hf hbump (c := c) (d := c) id rfl o = o := by
  have e : Q.inclPullOr hf hbump (c := c) (d := c) id rfl (Q.inclPushOr hf hbump id rfl o) =
      Q.inclPullOr hf hbump (c := c) (d := c) id rfl
        (Q.inclPushOr hf hbump id rfl (Q.inclPushOr hf hbump id rfl o)) :=
    congrArg (Q.inclPullOr hf hbump (c := c) (d := c) id rfl)
      (Q.inclPushOr_comp hf hbump (c := c) (d := c) (e := c) id id rfl rfl rfl ho)
  rw [Q.inclPullOr_inclPushOr hf hbump id rfl ho, Q.inclPullOr_inclPushOr hf hbump id rfl
    (Q.isModelInvariant_inclPushOr hf hbump id rfl ho)] at e
  exact e.symm

/-- **The transport to a subfamily is the pull-back along the inclusion.** -/
theorem modelTransport_eq_inclPullOr (σ : c.ι → d.ι) (h : d.Ψ ∘ σ = c.Ψ) {o : Q.ModelOr hf d}
    (ho : Q.IsModelInvariant hf hbump d o) :
    Q.modelTransport hf hbump d c o = Q.inclPullOr hf hbump σ h o := by
  have hτ : d.Ψ ∘ Sum.elim σ id = (Q.sumFamily c d).Ψ := by
    funext x; cases x with
    | inl i => exact congrFun h i
    | inr j => rfl
  rw [Q.modelTransport_eq_via hf hbump (M := d) (Sum.elim σ id) hτ rfl h rfl rfl ho]
  exact congrArg (Q.inclPullOr hf hbump σ h) (Q.inclPushOr_id hf hbump ho)

/-- **The transport from a model to itself is the identity.** -/
theorem modelTransport_self {o : Q.ModelOr hf c} (ho : Q.IsModelInvariant hf hbump c o) :
    Q.modelTransport hf hbump c c o = o := by
  rw [Q.modelTransport_eq_inclPullOr hf hbump id rfl ho]
  have := Q.inclPullOr_inclPushOr hf hbump (c := c) (d := c) id rfl ho
  rwa [Q.inclPushOr_id hf hbump ho] at this

/-- The transport is injective on invariant sections. -/
theorem modelTransport_injective (a b : Q.BundleCoveringFamily) {o o' : Q.ModelOr hf a}
    (ho : Q.IsModelInvariant hf hbump a o) (ho' : Q.IsModelInvariant hf hbump a o')
    (h : Q.modelTransport hf hbump a b o = Q.modelTransport hf hbump a b o') : o = o' := by
  rw [← Q.modelTransport_modelTransport hf hbump a b ho,
    ← Q.modelTransport_modelTransport hf hbump a b ho', h]

/-! ## The orientation category `O_f` (Definition 18.5.1) -/

section Category

variable (hF : Q.HasStrongBundleUniformizers)

/-- **The point `q_α` of `Ψ̄_α` over `α`** in the reference model `R` (one `Ψ̄_α ∈ F̄(α)` for
every object `α`, `refCoveringFamily`): `Ψ_α(q_α) = α`. -/
def refPt (α : C.Obj) : (Q.modelSEP (Q.refCoveringFamily hF).Ψ).Obj :=
  ⟨α, pointOf (Ψ := Q.baseUnif (Q.refBundleUnif (hF α)))
    (Q.base_mem α _ (Q.refBundleUnif_mem (hF α)))⟩

theorem obj_refPt (α : C.Obj) :
    (S.modelFunctor (Q.modelBase (Q.refCoveringFamily hF).Ψ)).obj (Q.refPt hF α) = α :=
  obj_pointOf (Ψ := Q.baseUnif (Q.refBundleUnif (hF α)))
    (Q.base_mem α _ (Q.refBundleUnif_mem (hF α)))

/-- An object of a covering model is smooth iff its image in `C` is (Definition 17.1.31). -/
theorem mem_smoothSet_model_iff' (c : Q.BundleCoveringFamily) (x : (Q.modelSEP c.Ψ).Obj) :
    x ∈ (Q.modelSEP c.Ψ).X.PObj.smoothSet ↔
      S.IsSmoothObj ((S.modelFunctor (Q.modelBase c.Ψ)).obj x) :=
  (S.isSmoothObj_model_iff x).symm

theorem refPt_mem {α : C.Obj} (hα : S.IsSmoothObj α) :
    Q.refPt hF α ∈ (Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.PObj.smoothSet := by
  rw [Q.mem_smoothSet_model_iff', Q.obj_refPt]
  exact hα

/-- **The two-point set `{(DET(f, α), o), (DET(f, α), −o)}`** over a smooth object `α`.  We read
`DET(f, α) → Lin(f, α)` and its orientations as those of the model section `f^R` at `q_α`
(Definition 6.6.1 and Theorem 6.6.4 in the chart of `Ψ̄_α`); `Ψ̄_α` identifies them with the
orientations of the determinant bundle over `Lin(f, α)` (the `Ψ̄_*` paragraph, p. 858). -/
abbrev DetOr (α : C.Obj) (hα : S.IsSmoothObj α) :=
  Orx (B := (Q.modelSEP (Q.refCoveringFamily hF).Ψ).B)
    (Q.modelSection (Q.refCoveringFamily hF).Ψ f) (Q.modelFred (Q.refCoveringFamily hF).Ψ hf).2
    (Q.refPt hF α) (Q.refPt_mem hF hα)

/-- **The morphism `(q_α, φ, q_α')` of the reference model** over a morphism `φ : α → α'`. -/
def refMor (φ : C.Mor) {α α' : C.Obj} (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') : (Q.modelSEP (Q.refCoveringFamily hF).Ψ).Mor :=
  ⟨(α, α'), S.morTr (Q.refPt hF α).2 φ (Q.refPt hF α').2 (Q.obj_refPt hF α) hs
    (Q.obj_refPt hF α') ht⟩

/-- **`φ_* : (DET(f, α), ±o) → (DET(f, α'), ±o')`** for a morphism `φ : α → α'` of smooth
objects (p. 856–857): the action of `(q_α, φ, q_α')` on orientations (Definition 12.5.2). -/
def orPush (φ : C.Mor) {α α' : C.Obj} (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (hα : S.IsSmoothObj α) (hα' : S.IsSmoothObj α') :
    Q.DetOr hf hF α hα ≃ Q.DetOr hf hF α' hα' :=
  (Q.modelSEP (Q.refCoveringFamily hF).Ψ).E.orMor (Q.modelFred _ hf) (Q.modelSec hbump _)
    (Q.refMor hF φ hs ht) rfl rfl _ _

theorem refMor_unit (α : C.Obj) :
    Q.refMor hF (C.toGroupoidStr.unit α) (C.toGroupoidStr.src_unit α)
        (C.toGroupoidStr.tgt_unit α) =
      (Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.unit (Q.refPt hF α) :=
  S.modelMor_ext rfl rfl (congrArg C.toGroupoidStr.unit (Q.obj_refPt hF α).symm)

theorem refMor_comp {φ ψ : C.Mor} {α α' α'' : C.Obj} (hφs : C.toGroupoidStr.src φ = α)
    (hφt : C.toGroupoidStr.tgt φ = α') (hψs : C.toGroupoidStr.src ψ = α')
    (hψt : C.toGroupoidStr.tgt ψ = α'') :
    (Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.comp (Q.refMor hF ψ hψs hψt)
        (Q.refMor hF φ hφs hφt) =
      Q.refMor hF (C.toGroupoidStr.comp ψ φ)
        ((C.toGroupoidStr.src_comp ψ φ (hψs.trans hφt.symm)).trans hφs)
        ((C.toGroupoidStr.tgt_comp ψ φ (hψs.trans hφt.symm)).trans hψt) :=
  S.modelGroupoid_comp_of _ _ (hψs.trans hφt.symm)

/-- **`(1_α)_* = Id`.** -/
theorem orPush_unit (α : C.Obj) (hα : S.IsSmoothObj α) :
    Q.orPush hf hbump hF (C.toGroupoidStr.unit α) (C.toGroupoidStr.src_unit α)
      (C.toGroupoidStr.tgt_unit α) hα hα = Equiv.refl _ :=
  EpStrongBundle.orMor_unit _ _ _ (Q.refMor_unit hF α) _ _ _

/-- **`(ψ ∘ φ)_* = ψ_* ∘ φ_*`**: `φ ↦ φ_*` is a functor, so that `O_f` is a category fibred
over `C_∞`. -/
theorem orPush_comp {φ ψ : C.Mor} {α α' α'' : C.Obj} (hφs : C.toGroupoidStr.src φ = α)
    (hφt : C.toGroupoidStr.tgt φ = α') (hψs : C.toGroupoidStr.src ψ = α')
    (hψt : C.toGroupoidStr.tgt ψ = α'') (hα : S.IsSmoothObj α) (hα' : S.IsSmoothObj α')
    (hα'' : S.IsSmoothObj α'') :
    (Q.orPush hf hbump hF φ hφs hφt hα hα').trans (Q.orPush hf hbump hF ψ hψs hψt hα' hα'') =
      Q.orPush hf hbump hF (C.toGroupoidStr.comp ψ φ)
        ((C.toGroupoidStr.src_comp ψ φ (hψs.trans hφt.symm)).trans hφs)
        ((C.toGroupoidStr.tgt_comp ψ φ (hψs.trans hφt.symm)).trans hψt) hα hα'' := by
  exact (EpStrongBundle.orMor_comp _ _ _ rfl rfl rfl rfl _ _ _).trans
    (EpStrongBundle.orMor_congr _ _ _ (Q.refMor_comp hF hφs hφt hψs hψt) _ _ _ _)


/-- Smooth objects are closed under morphisms. -/
theorem isSmoothObj_tgt {φ : C.Mor} (h : S.IsSmoothObj (C.toGroupoidStr.src φ)) :
    S.IsSmoothObj (C.toGroupoidStr.tgt φ) :=
  fun m => (h m).of_isomorphic ⟨φ, rfl, rfl⟩

/-- **An object `(α, (DET(f, α), o))` of the orientation category `O_f`** (Definition 18.5.1,
p. 857): a smooth object `α` with one of the two orientations of `DET(f, α)`. -/
structure OrCatObj where
  /-- The smooth object `α = σ(α, (DET(f, α), o))`. -/
  obj : C.Obj
  smooth : S.IsSmoothObj obj
  /-- The orientation `o`. -/
  or : Q.DetOr hf hF obj smooth

/-- **A morphism `(φ, (DET(f, α), o))` of `O_f`** (Definition 18.5.1, p. 857), `s(φ) = α`. -/
structure OrCatMor where
  /-- The smooth morphism `φ = σ(φ, (DET(f, α), o))`. -/
  mor : C.Mor
  smooth : S.IsSmoothObj (C.toGroupoidStr.src mor)
  /-- The orientation `o` at the source. -/
  or : Q.DetOr hf hF _ smooth

/-- The source `(α, (DET(f, α), o))` of `(φ, (DET(f, α), o))`. -/
def OrCatMor.src (m : Q.OrCatMor hf hF) : Q.OrCatObj hf hF := ⟨_, m.smooth, m.or⟩

/-- The target `(t(φ), (DET(f, t(φ)), φ_* o))` of `(φ, (DET(f, α), o))`. -/
def OrCatMor.tgt (m : Q.OrCatMor hf hF) : Q.OrCatObj hf hF :=
  ⟨_, isSmoothObj_tgt m.smooth, Q.orPush hf hbump hF m.mor rfl rfl _ _ m.or⟩

/-- **`σ : O_f → C_∞` is a functor** (Definition 18.5.1): it commutes with source and target.
The bump functions of Definition 18.4.1 (not in the text here) give the sc⁺-sections of
Definition 12.5.2; they exist for the reflection polyfold (`reflDiag_orientation_hyp`). -/
theorem definition_18_5_1_hyp (m : Q.OrCatMor hf hF) :
    (OrCatMor.src Q hf hF m).obj = C.toGroupoidStr.src m.mor ∧
      (OrCatMor.tgt Q hf hbump hF m).obj = C.toGroupoidStr.tgt m.mor :=
  ⟨rfl, rfl⟩

/-- **The fibres of `σ` are two-point sets, and `φ_*` is a bijection between them** (p. 857):
`{(DET(f, α), o), (DET(f, α), −o)} → {(DET(f, α'), o'), (DET(f, α'), −o')}`. -/
theorem orPush_bijective_two {φ : C.Mor} {α α' : C.Obj} (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (hα : S.IsSmoothObj α) (hα' : S.IsSmoothObj α') :
    (∃ o₁ o₂ : Q.DetOr hf hF α hα, o₁ ≠ o₂ ∧ ∀ o, o = o₁ ∨ o = o₂) ∧
      (∃ o₁ o₂ : Q.DetOr hf hF α' hα', o₁ ≠ o₂ ∧ ∀ o, o = o₁ ∨ o = o₂) ∧
      Bijective (Q.orPush hf hbump hF φ hs ht hα hα') :=
  ⟨exists_two_orx _ _ (Q.modelSec hbump _), exists_two_orx _ _ (Q.modelSec hbump _),
    (Q.orPush hf hbump hF φ hs ht hα hα').bijective⟩

/-- **A section functor `o : C_∞ → O_f` of `σ`** (p. 857–858): a choice `α ↦ o_α` of one of the
two orientations of `DET(f, α)` for every smooth `α`, with `o_{t(φ)} = φ_* o_{s(φ)}`. -/
abbrev OrSection := ∀ α (hα : S.IsSmoothObj α), Q.DetOr hf hF α hα

/-- The functor property `o_{t(φ)} = φ_* o_{s(φ)}` of a section `o` of `σ` (p. 858). -/
def IsOrSectionFunctor (o : Q.OrSection hf hF) : Prop :=
  ∀ (φ : C.Mor) {α α' : C.Obj} (hs : C.toGroupoidStr.src φ = α)
    (ht : C.toGroupoidStr.tgt φ = α') (hα : S.IsSmoothObj α) (hα' : S.IsSmoothObj α'),
    Q.orPush hf hbump hF φ hs ht hα hα' (o α hα) = o α' hα'

/-- **The obstruction to orientability** (p. 857): if an isotropy morphism `g ∈ G_α` reverses
an orientation of `DET(f, α)`, `g_*(DET(f, α), ±o) = (DET(f, α), ∓o)`, then `σ` has no section
functor. -/
theorem not_exists_isOrSectionFunctor {g : C.Mor} {α : C.Obj} (hs : C.toGroupoidStr.src g = α)
    (ht : C.toGroupoidStr.tgt g = α) (hα : S.IsSmoothObj α) (ω : Q.DetOr hf hF α hα)
    (hω : Q.orPush hf hbump hF g hs ht hα hα ω ≠ ω) :
    ¬ ∃ o : Q.OrSection hf hF, Q.IsOrSectionFunctor hf hbump hF o := by
  rintro ⟨o, ho⟩
  have hfix := ho g hs ht hα hα
  obtain ⟨o₁, o₂, hne, hall⟩ := (Q.orPush_bijective_two hf hbump hF hs ht hα hα).1
  have two : ∀ u v t : Q.DetOr hf hF α hα, u ≠ v → t = u ∨ t = v := by
    intro u v t huv
    rcases hall u with h1 | h1 <;> rcases hall v with h2 | h2 <;> rcases hall t with h3 | h3 <;>
      simp_all
  have key : ∀ w, Q.orPush hf hbump hF g hs ht hα hα w = w := by
    intro w
    by_cases hw : w = o α hα
    · rw [hw, hfix]
    · have h1 : Q.orPush hf hbump hF g hs ht hα hα w ≠ o α hα := fun h =>
        hw ((Q.orPush hf hbump hF g hs ht hα hα).injective (h.trans hfix.symm))
      exact (two (o α hα) w _ (Ne.symm hw)).resolve_left h1
  exact hω (key ω)

/-! ### Section functors and invariant sections of the reference model -/

/-- **The morphism `(q_{Γ(x)}, 1_{Γ(x)}, x) : q_{Γ(x)} → x`** of the reference model. -/
def refLift (x : (Q.modelSEP (Q.refCoveringFamily hF).Ψ).Obj) :
    (Q.modelSEP (Q.refCoveringFamily hF).Ψ).Mor :=
  ⟨((S.modelFunctor (Q.modelBase (Q.refCoveringFamily hF).Ψ)).obj x, x.1),
    S.morTr (Q.refPt hF _).2 (C.toGroupoidStr.unit _) x.2 (Q.obj_refPt hF _)
      (C.toGroupoidStr.src_unit _) rfl (C.toGroupoidStr.tgt_unit _)⟩

/-- **The section of the reference model given by a section of `σ`**:
`x ↦ (q_{Γ(x)} → x)_* o_{Γ(x)}`,
the orientation `Γ̄^* o` of `f^R` (the `Ψ̄^*` paragraph, p. 858). -/
def toRef (o : Q.OrSection hf hF) : Q.ModelOr hf (Q.refCoveringFamily hF) := fun x hs =>
  (Q.modelSEP (Q.refCoveringFamily hF).Ψ).E.orMor (Q.modelFred _ hf) (Q.modelSec hbump _)
    (Q.refLift hF x) rfl rfl (Q.refPt_mem hF ((Q.mem_smoothSet_model_iff' _ x).1 hs)) hs
    (o _ ((Q.mem_smoothSet_model_iff' _ x).1 hs))

/-- **The section of `σ` given by a section of the reference model**: `α ↦ o'_{q_α}`. -/
def catOf (o' : Q.ModelOr hf (Q.refCoveringFamily hF)) : Q.OrSection hf hF := fun α hα =>
  o' (Q.refPt hF α) (Q.refPt_mem hF hα)

theorem isOrSectionFunctor_catOf {o' : Q.ModelOr hf (Q.refCoveringFamily hF)}
    (ho' : Q.IsModelInvariant hf hbump _ o') :
    Q.IsOrSectionFunctor hf hbump hF (Q.catOf hf hF o') :=
  fun φ _ _ hs ht _ _ => ho' (Q.refMor hF φ hs ht) rfl rfl _ _

theorem toRef_catOf {o' : Q.ModelOr hf (Q.refCoveringFamily hF)}
    (ho' : Q.IsModelInvariant hf hbump _ o') :
    Q.toRef hf hbump hF (Q.catOf hf hF o') = o' :=
  funext fun x => funext fun _ => ho' (Q.refLift hF x) rfl rfl _ _

theorem refLift_refPt (α : C.Obj) :
    Q.refLift hF (Q.refPt hF α) = Q.refMor hF (C.toGroupoidStr.unit α)
      ((C.toGroupoidStr.src_unit α).trans (Q.obj_refPt hF α).symm)
      (C.toGroupoidStr.tgt_unit α) :=
  S.modelMor_ext rfl rfl (congrArg C.toGroupoidStr.unit (Q.obj_refPt hF α))

theorem catOf_toRef {o : Q.OrSection hf hF} (ho : Q.IsOrSectionFunctor hf hbump hF o) :
    Q.catOf hf hF (Q.toRef hf hbump hF o) = o := by
  funext α hα
  have hΓ := (Q.mem_smoothSet_model_iff' _ _).1 (Q.refPt_mem hF hα)
  have e1 : Q.catOf hf hF (Q.toRef hf hbump hF o) α hα =
      Q.orPush hf hbump hF (C.toGroupoidStr.unit α)
        ((C.toGroupoidStr.src_unit α).trans (Q.obj_refPt hF α).symm)
        (C.toGroupoidStr.tgt_unit α) hΓ hα (o _ hΓ) :=
    DFunLike.congr_fun (EpStrongBundle.orMor_congr _ _ _ (Q.refLift_refPt hF α) _ _ _ _) (o _ hΓ)
  exact e1.trans (ho _ _ _ _ hα)

/-- `m ∘ (q_{Γ(s m)} → s m) = (q_{Γ(t m)} → t m) ∘ (q_{Γ(s m)}, m, q_{Γ(t m)})`. -/
theorem comp_refLift (m : (Q.modelSEP (Q.refCoveringFamily hF).Ψ).Mor) :
    (Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.comp m
        (Q.refLift hF ((Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.src m)) =
      (Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.comp
        (Q.refLift hF ((Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.tgt m))
        (Q.refMor hF m.2.mor m.2.src_mor m.2.tgt_mor) := by
  have a : C.toGroupoidStr.comp m.2.mor (C.toGroupoidStr.unit (C.toGroupoidStr.src m.2.mor)) =
      m.2.mor := C.toGroupoidStr.comp_unit _
  have b : C.toGroupoidStr.comp (C.toGroupoidStr.unit (C.toGroupoidStr.tgt m.2.mor)) m.2.mor =
      m.2.mor := C.toGroupoidStr.unit_comp _
  rw [m.2.src_mor] at a
  rw [m.2.tgt_mor] at b
  refine S.modelMor_ext ?_ ?_ ?_
  · exact (S.modelGroupoid _).src_comp _ _ rfl |>.trans
      ((S.modelGroupoid _).src_comp (Q.refLift hF ((Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.tgt m))
        (Q.refMor hF m.2.mor m.2.src_mor m.2.tgt_mor) rfl).symm
  · exact (S.modelGroupoid _).tgt_comp _ _ rfl |>.trans
      ((S.modelGroupoid _).tgt_comp (Q.refLift hF ((Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.tgt m))
        (Q.refMor hF m.2.mor m.2.src_mor m.2.tgt_mor) rfl).symm
  · exact (S.modelGroupoid_comp_mor rfl).trans (a.trans (b.symm.trans
      (S.modelGroupoid_comp_mor
        (φ := Q.refLift hF ((Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.tgt m))
        (ψ := Q.refMor hF m.2.mor m.2.src_mor m.2.tgt_mor) rfl).symm))

/-- **Section functors are invariant sections of the reference model.** -/
theorem isModelInvariant_toRef {o : Q.OrSection hf hF} (ho : Q.IsOrSectionFunctor hf hbump hF o) :
    Q.IsModelInvariant hf hbump _ (Q.toRef hf hbump hF o) := by
  intro m x x' hx hx' hs hs'
  subst hx hx'
  have hΓs := (Q.mem_smoothSet_model_iff' _ _).1 hs
  have hΓt := (Q.mem_smoothSet_model_iff' _ _).1 hs'
  have e := ho m.2.mor m.2.src_mor m.2.tgt_mor hΓs hΓt
  have key := EpStrongBundle.orMor_orMor_eq (Q.modelSEP (Q.refCoveringFamily hF).Ψ).E
    (Q.modelFred _ hf) (Q.modelSec hbump _)
    (m₁ := Q.refLift hF ((Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.src m)) (m₂ := m)
    (n₁ := Q.refMor hF m.2.mor m.2.src_mor m.2.tgt_mor)
    (n₂ := Q.refLift hF ((Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.tgt m))
    rfl rfl rfl rfl rfl rfl rfl rfl (Q.refPt_mem hF hΓs) hs (Q.refPt_mem hF hΓt) hs'
    (Q.comp_refLift hF m) (o _ hΓs)
  exact key.trans (congrArg _ e)

end Category


/-! ## Orientations (Definitions 18.5.2 and 18.5.4, Remark 18.5.3, Proposition 18.5.6) -/

section Orientations

variable (hT : S.IsTame) (hfT : Q.IsScFredholmSectionFunctorTame f)
  (hF : Q.HasStrongBundleUniformizers)

/-- **The covering family `Ψ̄ ⊔ {Ψ̄'}`** (`adjoin`). -/
abbrev adjoinFamily (c : Q.BundleCoveringFamily) (Ψ : Q.Unif) : Q.BundleCoveringFamily where
  ι := c.ι ⊕ PUnit.{u + 1}
  Ψ := Q.adjoin c Ψ
  cover := by
    refine eq_univ_of_forall fun z => ?_
    have hz : z ∈ ⋃ i, (Q.modelBase c.Ψ i).1.footprint := c.cover.symm ▸ mem_univ z
    obtain ⟨i, hi⟩ := mem_iUnion.1 hz
    exact mem_iUnion.2 ⟨Sum.inl i, hi⟩

/-- **`Γ̄^* o` in a covering model** (p. 858): the section of `σ : O_{f^Ψ̄} → (X_Ψ)_∞` given by a
section `o` of `σ : O_f → C_∞`, transported from the reference model. -/
def pullCat (c : Q.BundleCoveringFamily) (o : Q.OrSection hf hF) : Q.ModelOr hf c :=
  Q.modelTransport hf hbump (Q.refCoveringFamily hF) c (Q.toRef hf hbump hF o)

theorem isModelInvariant_pullCat (c : Q.BundleCoveringFamily) {o : Q.OrSection hf hF}
    (ho : Q.IsOrSectionFunctor hf hbump hF o) :
    Q.IsModelInvariant hf hbump c (Q.pullCat hf hbump hF c o) :=
  Q.isModelInvariant_modelTransport hf hbump _ _ (Q.isModelInvariant_toRef hf hbump hF ho)

/-- **`Φ̄^* o_{Ψ̄'} = o_Ψ̄`** for an inclusion of covering families (the identity of germs on
p. 858, in the models). -/
theorem inclPullOr_pullCat {c d : Q.BundleCoveringFamily} (σ : c.ι → d.ι) (h : d.Ψ ∘ σ = c.Ψ)
    {o : Q.OrSection hf hF} (ho : Q.IsOrSectionFunctor hf hbump hF o) :
    Q.inclPullOr hf hbump σ h (Q.pullCat hf hbump hF d o) = Q.pullCat hf hbump hF c o := by
  rw [← Q.modelTransport_eq_inclPullOr hf hbump σ h (Q.isModelInvariant_pullCat hf hbump hF d ho),
    pullCat, Q.modelTransport_comp hf hbump _ _ _ (Q.isModelInvariant_toRef hf hbump hF ho)]
  rfl

/-- In the reference model, `Γ̄^* o` is `toRef o`. -/
theorem pullCat_ref {o : Q.OrSection hf hF} (ho : Q.IsOrSectionFunctor hf hbump hF o) :
    Q.pullCat hf hbump hF (Q.refCoveringFamily hF) o = Q.toRef hf hbump hF o :=
  Q.modelTransport_self hf hbump (Q.isModelInvariant_toRef hf hbump hF ho)

/-- `Γ̄^*` of the section defined by a section of a covering model is the transport. -/
theorem pullCat_catOf (c d : Q.BundleCoveringFamily) {o : Q.ModelOr hf c}
    (ho : Q.IsModelInvariant hf hbump c o) :
    Q.pullCat hf hbump hF d
        (Q.catOf hf hF (Q.modelTransport hf hbump c (Q.refCoveringFamily hF) o)) =
      Q.modelTransport hf hbump c d o := by
  rw [pullCat, Q.toRef_catOf hf hbump hF (Q.isModelInvariant_modelTransport hf hbump _ _ ho),
    Q.modelTransport_comp hf hbump _ _ _ ho]

/-- **The continuity property** (Definition 18.5.2, p. 858–859).  We read `Γ̄^* o` and
`Ψ(ō) = α` as `Ψ̄^* o` and `α_z`, and the local representative `f_Ψ̄` with the orientations
`Ψ̄^* o` as the piece `Ψ̄` of the model of `R ⊔ {Ψ̄}` with `Γ̄^* o` (`pullCat`); "related by
continuation near `ō`" is read as Definition 6.6.12: a continuous orientation over an open
neighbourhood of `ō`.  The condition is required for every class `z ∈ |C_∞|`, every
representative `α_z` of `z`, every `Ψ̄ ∈ F̄(α_z)` and every `ō` with `Ψ(ō) = α_z`. -/
def HasContinuityProperty (o : Q.OrSection hf hF) : Prop :=
  ∀ α : C.Obj, S.IsSmoothObj α → ∀ Ψ : Q.Unif, Ψ.1 ∈ Q.F α →
    ∀ q : (Q.baseUnif Ψ).1.O, (Q.baseUnif Ψ).1.obj q = α →
      ∃ U, (⟨Sum.inr PUnit.unit, q⟩ :
          (Q.modelSEP (Q.adjoinFamily (Q.refCoveringFamily hF) Ψ).Ψ).Obj) ∈ U ∧
        Q.IsModelContOrOn hf hbump hT hfT (Q.adjoinFamily (Q.refCoveringFamily hF) Ψ) U
          (Q.pullCat hf hbump hF (Q.adjoinFamily (Q.refCoveringFamily hF) Ψ) o)

/-- **An orientation for `f`** (Definition 18.5.4, p. 859): a section functor of
`σ : O_f → C_∞` with the continuity property. -/
def IsOrientation (o : Q.OrSection hf hF) : Prop :=
  Q.IsOrSectionFunctor hf hbump hF o ∧ Q.HasContinuityProperty hf hbump hT hfT hF o

/-- **`f` is orientable** (Definition 18.5.4): an orientation exists. -/
def IsOrientable : Prop := ∃ o, Q.IsOrientation hf hbump hT hfT hF o

/-! ### Local continuity in the models -/

/-- Continuity of an orientation is local (`isContOrOn_of_local_or`), in a covering model. -/
theorem isModelContOrOn_univ_of_local (c : Q.BundleCoveringFamily) {o : Q.ModelOr hf c}
    (h : ∀ x, x ∈ (Q.modelSEP c.Ψ).X.PObj.smoothSet →
      ∃ V, x ∈ V ∧ Q.IsModelContOrOn hf hbump hT hfT c V o) :
    Q.IsModelContOrOn hf hbump hT hfT c univ o := by
  have := paracompactSpace_rn_prod (Q.modelSEP c.Ψ).X.PObj
  have := paracompactSpace_rn_pullback (Q.modelSEP c.Ψ).B
  have := paracompactSpace_rn_rn_prod (Q.modelSEP c.Ψ).X.PObj
  have := paracompactSpace_rn_rn_pullback (Q.modelSEP c.Ψ).B
  exact isContOrOn_of_local_or isOpen_univ fun x _ hs => h x hs

/-- Continuity near a point passes along a morphism of a covering model (invariant sections). -/
theorem exists_isModelContOrOn_of_mor (c : Q.BundleCoveringFamily) {o : Q.ModelOr hf c}
    (hinv : Q.IsModelInvariant hf hbump c o) (m : (Q.modelSEP c.Ψ).Mor)
    {x x' : (Q.modelSEP c.Ψ).Obj} (hx : (Q.modelSEP c.Ψ).X.src m = x)
    (hx' : (Q.modelSEP c.Ψ).X.tgt m = x') (hs : x ∈ (Q.modelSEP c.Ψ).X.PObj.smoothSet)
    (hs' : x' ∈ (Q.modelSEP c.Ψ).X.PObj.smoothSet) {V : Set (Q.modelSEP c.Ψ).Obj} (hxV : x ∈ V)
    (ho : Q.IsModelContOrOn hf hbump hT hfT c V o) :
    ∃ V', x' ∈ V' ∧ Q.IsModelContOrOn hf hbump hT hfT c V' o := by
  have := paracompactSpace_rn_prod (Q.modelSEP c.Ψ).X.PObj
  have := paracompactSpace_rn_pullback (Q.modelSEP c.Ψ).B
  have := paracompactSpace_rn_rn_prod (Q.modelSEP c.Ψ).X.PObj
  have := paracompactSpace_rn_rn_pullback (Q.modelSEP c.Ψ).B
  exact (Q.modelSEP c.Ψ).E.exists_isContOrOn_of_mor _ _ (Q.modelTame c.Ψ hT) (Q.modelBump hbump c)
    (Q.modelFredTame c.Ψ hfT) hinv m hx hx' hs hs' hxV ho

/-- **The one-representative form of the continuity property** (Remark 18.5.3): in the class
of every smooth `α` there are an object `α'`, a `Ψ̄ ∈ F̄(α')` and an `ō` with `Ψ(ō) = α'` near
which `Γ̄^* o` is continuous. -/
def HasContinuityPropertyRep (o : Q.OrSection hf hF) : Prop :=
  ∀ α : C.Obj, S.IsSmoothObj α → ∃ (α' : C.Obj) (φ : C.Mor), C.toGroupoidStr.src φ = α' ∧
    C.toGroupoidStr.tgt φ = α ∧ ∃ Ψ : Q.Unif, Ψ.1 ∈ Q.F α' ∧
      ∃ q : (Q.baseUnif Ψ).1.O, (Q.baseUnif Ψ).1.obj q = α' ∧
        ∃ U, (⟨Sum.inr PUnit.unit, q⟩ :
            (Q.modelSEP (Q.adjoinFamily (Q.refCoveringFamily hF) Ψ).Ψ).Obj) ∈ U ∧
          Q.IsModelContOrOn hf hbump hT hfT (Q.adjoinFamily (Q.refCoveringFamily hF) Ψ) U
            (Q.pullCat hf hbump hF (Q.adjoinFamily (Q.refCoveringFamily hF) Ψ) o)

/-- **From one representative per class to every covering model.** -/
theorem isModelContOrOn_pullCat_of_rep {o : Q.OrSection hf hF}
    (ho : Q.IsOrSectionFunctor hf hbump hF o)
    (hrep : Q.HasContinuityPropertyRep hf hbump hT hfT hF o) (c : Q.BundleCoveringFamily) :
    Q.IsModelContOrOn hf hbump hT hfT c univ (Q.pullCat hf hbump hF c o) := by
  refine Q.isModelContOrOn_univ_of_local hf hbump hT hfT c fun x hx => ?_
  obtain ⟨α', φ, hφs, hφt, Ψ, -, q, hq, U, hqU, hU⟩ :=
    hrep _ ((Q.mem_smoothSet_model_iff' c x).1 hx)
  set J := Q.adjoinFamily (Q.refCoveringFamily hF) Ψ
  set M := Q.sumFamily c J
  rw [← Q.inclPullOr_pullCat hf hbump hF (d := M) Sum.inr rfl ho] at hU
  obtain ⟨V, -, hyV, hcV⟩ := Q.exists_isModelContOrOn_of_inclPullOr hf hbump hT hfT
    (d := M) Sum.inr rfl hqU hU
  have hα' : S.IsSmoothObj α' := fun k =>
    ((Q.mem_smoothSet_model_iff' c x).1 hx k).of_isomorphic
      ⟨C.toGroupoidStr.inv φ, (C.toGroupoidStr.src_inv φ).trans hφt,
        (C.toGroupoidStr.tgt_inv φ).trans hφs⟩
  let m : (Q.modelSEP M.Ψ).Mor := ⟨(Sum.inr (Sum.inr PUnit.unit), Sum.inl x.1),
    S.morTr q φ x.2 hq hφs rfl hφt⟩
  have hsy : (⟨Sum.inr (Sum.inr PUnit.unit), q⟩ : (Q.modelSEP M.Ψ).Obj) ∈
      (Q.modelSEP M.Ψ).X.PObj.smoothSet :=
    (Q.mem_smoothSet_model_iff' M ⟨Sum.inr (Sum.inr PUnit.unit), q⟩).2
      (show S.IsSmoothObj ((Q.baseUnif Ψ).1.obj q) by rw [hq]; exact hα')
  have hsx : (⟨Sum.inl x.1, x.2⟩ : (Q.modelSEP M.Ψ).Obj) ∈ (Q.modelSEP M.Ψ).X.PObj.smoothSet :=
    (Q.mem_smoothSet_model_iff' M _).2 ((Q.mem_smoothSet_model_iff' c x).1 hx)
  obtain ⟨V', hxV', hc'⟩ := Q.exists_isModelContOrOn_of_mor hf hbump hT hfT M
    (Q.isModelInvariant_pullCat hf hbump hF M ho) m rfl rfl hsy hsx hyV hcV
  have hpull := Q.isModelContOrOn_inclPullOr hf hbump hT hfT (c := c) (d := M) Sum.inl rfl hc'
  have e := Q.inclPullOr_pullCat hf hbump hF (c := c) (d := M) Sum.inl rfl ho
  rw [e] at hpull
  exact ⟨_, hxV', hpull⟩

/-- **Remark 18.5.3** (p. 859): for a section functor `o`, the continuity property
(Definition 18.5.2) is equivalent to the continuity of `Γ̄^* o` in every covering model, and to
its one-representative form: it suffices to check one object `α_z` and one `Ψ̄_z ∈ F̄(α_z)` in
every class `z`.
The hypotheses not in the text (`S.IsTame`, `S.AdmitsModelBumpFunctions`, the tame form of
Definition 18.1.1 and `F̄(α) ≠ ∅`, Part I's hypotheses of Theorem 6.6.17 in the models) hold for
the diagonal section of the reflection bundle, whose isotropy `−1` at `0` acts non-trivially on
the fibre (`reflDiag_orientation_hyp`). -/
theorem remark_18_5_3_hyp {o : Q.OrSection hf hF} (ho : Q.IsOrSectionFunctor hf hbump hF o) :
    (Q.HasContinuityProperty hf hbump hT hfT hF o ↔
      ∀ c, Q.IsModelContOrOn hf hbump hT hfT c univ (Q.pullCat hf hbump hF c o)) ∧
    (Q.HasContinuityProperty hf hbump hT hfT hF o ↔
      Q.HasContinuityPropertyRep hf hbump hT hfT hF o) := by
  have h1 : Q.HasContinuityProperty hf hbump hT hfT hF o →
      Q.HasContinuityPropertyRep hf hbump hT hfT hF o := by
    intro h α hα
    obtain ⟨U, hU, hc⟩ := h α hα (Q.refBundleUnif (hF α)) (Q.refBundleUnif_mem (hF α))
      (pointOf (Q.base_mem α _ (Q.refBundleUnif_mem (hF α)))) (obj_pointOf _)
    exact ⟨α, C.toGroupoidStr.unit α, C.toGroupoidStr.src_unit α, C.toGroupoidStr.tgt_unit α,
      _, Q.refBundleUnif_mem (hF α), _, obj_pointOf _, U, hU, hc⟩
  have h2 : (∀ c, Q.IsModelContOrOn hf hbump hT hfT c univ (Q.pullCat hf hbump hF c o)) →
      Q.HasContinuityProperty hf hbump hT hfT hF o :=
    fun h _ _ Ψ _ _ _ => ⟨univ, mem_univ _, h _⟩
  exact ⟨⟨fun h => Q.isModelContOrOn_pullCat_of_rep hf hbump hT hfT hF ho (h1 h), h2⟩,
    ⟨h1, fun h => h2 (Q.isModelContOrOn_pullCat_of_rep hf hbump hT hfT hF ho h)⟩⟩

/-- An orientation pulls back to an orientation of every covering model. -/
theorem isModelOrientation_pullCat {o : Q.OrSection hf hF}
    (ho : Q.IsOrientation hf hbump hT hfT hF o) (c : Q.BundleCoveringFamily) :
    Q.IsModelOrientation hf hbump hT hfT c (Q.pullCat hf hbump hF c o) :=
  ⟨Q.isModelInvariant_pullCat hf hbump hF c ho.1,
    ((Q.remark_18_5_3_hyp hf hbump hT hfT hF ho.1).1.1 ho.2) c⟩

/-- The section of `σ` defined by an orientation of a covering model is an orientation. -/
theorem isOrientation_catOf (c : Q.BundleCoveringFamily) {o : Q.ModelOr hf c}
    (ho : Q.IsModelOrientation hf hbump hT hfT c o) :
    Q.IsOrientation hf hbump hT hfT hF
      (Q.catOf hf hF (Q.modelTransport hf hbump c (Q.refCoveringFamily hF) o)) := by
  have hsf := Q.isOrSectionFunctor_catOf hf hbump hF
    (Q.isModelInvariant_modelTransport hf hbump c _ ho.1)
  refine ⟨hsf, (Q.remark_18_5_3_hyp hf hbump hT hfT hF hsf).1.2 fun d => ?_⟩
  rw [Q.pullCat_catOf hf hbump hF c d ho.1]
  exact (Q.isModelOrientation_modelTransport hf hbump hT hfT c d ho).2

/-- **Proposition 18.5.6 (1)** (p. 859, left to the reader): `f` is orientable iff `f^Ψ̄_Ψ` is,
for any covering family `Ψ̄`.
The hypotheses not in the text (`S.IsTame`, `S.AdmitsModelBumpFunctions`, the tame form of
Definition 18.1.1 and `F̄(α) ≠ ∅`, Part I's hypotheses of Theorem 6.6.17 in the models) hold for
the diagonal section of the reflection bundle, whose isotropy `−1` at `0` acts non-trivially on
the fibre (`reflDiag_orientation_hyp`). -/
theorem proposition_18_5_6_one_hyp (c : Q.BundleCoveringFamily) :
    Q.IsOrientable hf hbump hT hfT hF ↔ ∃ o, Q.IsModelOrientation hf hbump hT hfT c o :=
  ⟨fun ⟨_, ho⟩ => ⟨_, Q.isModelOrientation_pullCat hf hbump hT hfT hF ho c⟩,
    fun ⟨_, ho⟩ => ⟨_, Q.isOrientation_catOf hf hbump hT hfT hF c ho⟩⟩

/-- **Proposition 18.5.6 (2)** (p. 859, left to the reader): an orientation for `f` pulls back
to an orientation for `f^Ψ̄_Ψ` and to one for `f^Ψ̄'_Ψ'`.
The hypotheses not in the text (`S.IsTame`, `S.AdmitsModelBumpFunctions`, the tame form of
Definition 18.1.1 and `F̄(α) ≠ ∅`, Part I's hypotheses of Theorem 6.6.17 in the models) hold for
the diagonal section of the reflection bundle, whose isotropy `−1` at `0` acts non-trivially on
the fibre (`reflDiag_orientation_hyp`). -/
theorem proposition_18_5_6_two_hyp {o : Q.OrSection hf hF}
    (ho : Q.IsOrientation hf hbump hT hfT hF o)
    (c c' : Q.BundleCoveringFamily) :
    Q.IsModelOrientation hf hbump hT hfT c (Q.pullCat hf hbump hF c o) ∧
      Q.IsModelOrientation hf hbump hT hfT c' (Q.pullCat hf hbump hF c' o) :=
  ⟨Q.isModelOrientation_pullCat hf hbump hT hfT hF ho c,
    Q.isModelOrientation_pullCat hf hbump hT hfT hF ho c'⟩

/-- **Proposition 18.5.6 (3)** (p. 859, left to the reader): orientations `o` of `f^Ψ̄_Ψ` and
`o'` of `f^Ψ̄'_Ψ'` come from the same orientation of `f` iff `f̄ : W_Ψ̄ → W_Ψ̄'` pulls back `o'`
to `o`.  We read "they correspond to the same orientation for `f` provided …" as an
equivalence (the converse holds as well), and the pull-back by `f̄` as `modelTransport c' c`
(the cospan `W_Ψ̄ → W_{Ψ̄ ⊔ Ψ̄'} ← W_Ψ̄'` representing `f̄`, `bundleComparison_comp_incl`).
The hypotheses not in the text (`S.IsTame`, `S.AdmitsModelBumpFunctions`, the tame form of
Definition 18.1.1 and `F̄(α) ≠ ∅`, Part I's hypotheses of Theorem 6.6.17 in the models) hold for
the diagonal section of the reflection bundle, whose isotropy `−1` at `0` acts non-trivially on
the fibre (`reflDiag_orientation_hyp`). -/
theorem proposition_18_5_6_three_hyp (c c' : Q.BundleCoveringFamily) {o : Q.ModelOr hf c}
    {o' : Q.ModelOr hf c'} (ho : Q.IsModelOrientation hf hbump hT hfT c o)
    (ho' : Q.IsModelOrientation hf hbump hT hfT c' o') :
    (∃ O, Q.IsOrientation hf hbump hT hfT hF O ∧ Q.pullCat hf hbump hF c O = o ∧
        Q.pullCat hf hbump hF c' O = o') ↔
      Q.modelTransport hf hbump c' c o' = o := by
  constructor
  · rintro ⟨O, hO, rfl, rfl⟩
    rw [pullCat, pullCat, Q.modelTransport_comp hf hbump _ _ _
      (Q.isModelInvariant_toRef hf hbump hF hO.1)]
  · intro h
    refine ⟨_, Q.isOrientation_catOf hf hbump hT hfT hF c ho, ?_, ?_⟩
    · rw [Q.pullCat_catOf hf hbump hF c c ho.1, Q.modelTransport_self hf hbump ho.1]
    · rw [Q.pullCat_catOf hf hbump hF c c' ho.1, ← h,
        Q.modelTransport_modelTransport hf hbump c' c ho'.1]


/-! ### Definition 12.5.4 in the models, the second orientation, Remark 18.5.5 -/

/-- **The model orientations are the orientations of Definition 12.5.4** for every topology on
`O_{f^Ψ̄}` with the properties of Theorem 6.6.17. -/
theorem isModelOrientation_iff (c : Q.BundleCoveringFamily) (o : Q.ModelOr hf c) :
    Q.IsModelOrientation hf hbump hT hfT c o ↔
      ∀ t : TopologicalSpace (OrSpace (B := (Q.modelSEP c.Ψ).B) (Q.modelSection c.Ψ f)
          (Q.modelFred c.Ψ hf).2),
        (haveI := paracompactSpace_rn_prod (Q.modelSEP c.Ψ).X.PObj;
          haveI := paracompactSpace_rn_pullback (Q.modelSEP c.Ψ).B;
          IsOrientationTopology (B := (Q.modelSEP c.Ψ).B) (Q.modelSection c.Ψ f)
            (Q.modelFred c.Ψ hf).2 t) →
        (Q.modelSEP c.Ψ).E.definition_12_5_4 (Q.modelFred c.Ψ hf) (Q.modelSec hbump c) t o := by
  have := paracompactSpace_rn_prod (Q.modelSEP c.Ψ).X.PObj
  have := paracompactSpace_rn_pullback (Q.modelSEP c.Ψ).B
  have := paracompactSpace_rn_rn_prod (Q.modelSEP c.Ψ).X.PObj
  have := paracompactSpace_rn_rn_pullback (Q.modelSEP c.Ψ).B
  constructor
  · rintro ⟨hi, hc⟩ t ht
    exact ⟨(isContOrOn_univ_iff_continuous (Q.modelTame c.Ψ hT) (Q.modelBump hbump c)
      (Q.modelFredTame c.Ψ hfT) (Q.modelSec hbump c) ht).2 hc, hi⟩
  · intro H
    obtain ⟨t₀, ht₀⟩ := (theorem_6_6_17 (Q.modelTame c.Ψ hT) (Q.modelBump hbump c)
      (Q.modelFredTame c.Ψ hfT)).exists
    have h := H t₀ ht₀
    exact ⟨h.2, (isContOrOn_univ_iff_continuous (Q.modelTame c.Ψ hT) (Q.modelBump hbump c)
      (Q.modelFredTame c.Ψ hfT) (Q.modelSec hbump c) ht₀).1 h.1⟩

/-- `−o` is an orientation of a model with `o`. -/
theorem isModelOrientation_otherOr (c : Q.BundleCoveringFamily) {o : Q.ModelOr hf c}
    (ho : Q.IsModelOrientation hf hbump hT hfT c o) :
    Q.IsModelOrientation hf hbump hT hfT c (otherOr _ (Q.modelSec hbump c) o) := by
  refine ⟨(Q.modelSEP c.Ψ).E.isOrInvariant_otherOr _ _ ho.1, ?_⟩
  have := paracompactSpace_rn_prod (Q.modelSEP c.Ψ).X.PObj
  have := paracompactSpace_rn_pullback (Q.modelSEP c.Ψ).B
  have := paracompactSpace_rn_rn_prod (Q.modelSEP c.Ψ).X.PObj
  have := paracompactSpace_rn_rn_pullback (Q.modelSEP c.Ψ).B
  exact isContOrOn_otherOr _ _ ho.2

/-- **An orientable `f` has two different orientations `o` and `−o`** (p. 857), as soon as
`C` has a smooth object. -/
theorem exists_two_orientations (h : Q.IsOrientable hf hbump hT hfT hF) {α : C.Obj}
    (hα : S.IsSmoothObj α) :
    ∃ o₁ o₂ : Q.OrSection hf hF, Q.IsOrientation hf hbump hT hfT hF o₁ ∧
      Q.IsOrientation hf hbump hT hfT hF o₂ ∧ o₁ α hα ≠ o₂ α hα := by
  obtain ⟨o, ho⟩ := h
  have hR := Q.isModelOrientation_pullCat hf hbump hT hfT hF ho (Q.refCoveringFamily hF)
  have h₁ := Q.isOrientation_catOf hf hbump hT hfT hF _ hR
  have h₂ := Q.isOrientation_catOf hf hbump hT hfT hF _
    (Q.isModelOrientation_otherOr hf hbump hT hfT _ hR)
  rw [Q.modelTransport_self hf hbump hR.1] at h₁
  rw [Q.modelTransport_self hf hbump
    (Q.isModelOrientation_otherOr hf hbump hT hfT _ hR).1] at h₂
  exact ⟨_, _, h₁, h₂, (otherOr_ne _ _ _ _).symm⟩

/-- **Remark 18.5.5, first part** (p. 859, left to the reader): for an orientable `f`, `|σ|` is
`(2 : 1)` and an orientation defines a continuous section `|o|` of `|σ|`.  We read
`|σ| : |O_f| → |C_∞|` as the orbit map of `σ : O_{f^R} → (X_R)_∞` in the reference model
(`|X_R| ≅ |C|`, Theorem 17.1.18), for any topology on `O_{f^R}` with the properties of
Theorem 6.6.17 (Proposition 12.5.6).
The hypotheses not in the text (`S.IsTame`, `S.AdmitsModelBumpFunctions`, the tame form of
Definition 18.1.1 and `F̄(α) ≠ ∅`, Part I's hypotheses of Theorem 6.6.17 in the models) hold for
the diagonal section of the reflection bundle, whose isotropy `−1` at `0` acts non-trivially on
the fibre (`reflDiag_orientation_hyp`). -/
theorem remark_18_5_5_mp_hyp
    {t : TopologicalSpace (OrSpace (B := (Q.modelSEP (Q.refCoveringFamily hF).Ψ).B)
      (Q.modelSection (Q.refCoveringFamily hF).Ψ f) (Q.modelFred (Q.refCoveringFamily hF).Ψ hf).2)}
    (ht : haveI := paracompactSpace_rn_prod (Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.PObj
      haveI := paracompactSpace_rn_pullback (Q.modelSEP (Q.refCoveringFamily hF).Ψ).B
      IsOrientationTopology (B := (Q.modelSEP (Q.refCoveringFamily hF).Ψ).B) _ _ t)
    (h : Q.IsOrientable hf hbump hT hfT hF) :
    letI := t
    (Q.modelSEP (Q.refCoveringFamily hF).Ψ).E.IsTwoToOne (Q.modelFred _ hf) (Q.modelSec hbump _) ∧
      ∃ s : Quot (Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.SmoothRel →
          Quot ((Q.modelSEP (Q.refCoveringFamily hF).Ψ).E.OrRel (Q.modelFred _ hf)
            (Q.modelSec hbump _)),
        Continuous s ∧ ∀ z, (Q.modelSEP (Q.refCoveringFamily hF).Ψ).E.orbitProj
          (Q.modelFred _ hf) (Q.modelSec hbump _) (s z) = z := by
  obtain ⟨o, ho⟩ := (Q.proposition_18_5_6_one_hyp hf hbump hT hfT hF (Q.refCoveringFamily hF)).1 h
  exact EpStrongBundle.proposition_12_5_6_mp (t := t) _ _ _
    ((Q.isModelOrientation_iff hf hbump hT hfT _ o).1 ho t ht)

/-- **Remark 18.5.5, the converse** (p. 859, left to the reader): `f` is orientable if `|σ|` is
`(2 : 1)` and admits a continuous section (read as in `remark_18_5_5_mp_hyp`).
The hypotheses not in the text (`S.IsTame`, `S.AdmitsModelBumpFunctions`, the tame form of
Definition 18.1.1 and `F̄(α) ≠ ∅`, Part I's hypotheses of Theorem 6.6.17 in the models) hold for
the diagonal section of the reflection bundle, whose isotropy `−1` at `0` acts non-trivially on
the fibre (`reflDiag_orientation_hyp`). -/
theorem remark_18_5_5_mpr_hyp
    {t : TopologicalSpace (OrSpace (B := (Q.modelSEP (Q.refCoveringFamily hF).Ψ).B)
      (Q.modelSection (Q.refCoveringFamily hF).Ψ f) (Q.modelFred (Q.refCoveringFamily hF).Ψ hf).2)}
    (ht : haveI := paracompactSpace_rn_prod (Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.PObj
      haveI := paracompactSpace_rn_pullback (Q.modelSEP (Q.refCoveringFamily hF).Ψ).B
      IsOrientationTopology (B := (Q.modelSEP (Q.refCoveringFamily hF).Ψ).B) _ _ t)
    (h₁ : letI := t
      (Q.modelSEP (Q.refCoveringFamily hF).Ψ).E.IsTwoToOne (Q.modelFred _ hf)
      (Q.modelSec hbump _))
    {s : Quot (Q.modelSEP (Q.refCoveringFamily hF).Ψ).X.SmoothRel →
      Quot ((Q.modelSEP (Q.refCoveringFamily hF).Ψ).E.OrRel (Q.modelFred _ hf)
        (Q.modelSec hbump _))}
    (hs : ∀ z, (Q.modelSEP (Q.refCoveringFamily hF).Ψ).E.orbitProj (Q.modelFred _ hf)
      (Q.modelSec hbump _) (s z) = z)
    (hsc : @Continuous _ _ _ (@instTopologicalSpaceQuot _ _ t) s) :
    Q.IsOrientable hf hbump hT hfT hF := by
  set R := Q.refCoveringFamily hF
  have := paracompactSpace_rn_prod (Q.modelSEP R.Ψ).X.PObj
  have := paracompactSpace_rn_pullback (Q.modelSEP R.Ψ).B
  have := paracompactSpace_rn_rn_prod (Q.modelSEP R.Ψ).X.PObj
  have := paracompactSpace_rn_rn_pullback (Q.modelSEP R.Ψ).B
  obtain rfl := eq_orTopology_of (Q.modelTame R.Ψ hT) (Q.modelBump hbump R)
    (Q.modelFredTame R.Ψ hfT) (Q.modelSec hbump R) ht.isLocalHomeomorph ht.propagation
  obtain ⟨o, ho, -⟩ := (Q.modelSEP R.Ψ).E.proposition_12_5_6_mpr_hyp (Q.modelTame R.Ψ hT)
    (Q.modelBump hbump R) (Q.modelFredTame R.Ψ hfT) (Q.modelFred R.Ψ hf) h₁ hs hsc
  refine (Q.proposition_18_5_6_one_hyp hf hbump hT hfT hF R).2 ⟨o, ho.2, ?_⟩
  exact (isContOrOn_univ_iff_continuous (Q.modelTame R.Ψ hT) (Q.modelBump hbump R)
    (Q.modelFredTame R.Ψ hfT) (Q.modelSec hbump R) ht).1 ho.1

/-- **The identity of germs `Φ̄^* o_Ψ̄' = o_Ψ̄` near `q̄`** (p. 858): for a morphism
`Φ = (q̄, φ, q̄')` of a covering model, the section carried by the local strong bundle
isomorphism of `Φ⁻¹` (`Φ̂ : U(q̄) → U(q̄')` with its lift) is `Γ̄^* o` on the target set of the
sheet of `Φ⁻¹`, an open neighbourhood of `q̄`. -/
theorem pullCat_germ (c : Q.BundleCoveringFamily) {o : Q.OrSection hf hF}
    (ho : Q.IsOrSectionFunctor hf hbump hF o) (Φ : (Q.modelSEP c.Ψ).Mor)
    {y : (Q.modelSEP c.Ψ).Obj}
    (hy : y ∈ ((Q.modelSEP c.Ψ).X.sheetAt ((Q.modelSEP c.Ψ).X.inv Φ)).tgtSet)
    (hys : y ∈ (Q.modelSEP c.Ψ).X.PObj.smoothSet) :
    ((Q.modelSEP c.Ψ).E.morIso ((Q.modelSEP c.Ψ).X.inv Φ)).pullOrx (Q.modelFred c.Ψ hf).2
        (Q.modelFred c.Ψ hf).2 ((Q.modelSEP c.Ψ).E.eqOn_morIso_of_functor (Q.modelFred c.Ψ hf) _)
        (Q.modelSec hbump c) (Q.modelSec hbump c) (Q.pullCat hf hbump hF c o) y hys =
      Q.pullCat hf hbump hF c o y hys := by
  have hϕs : ((Q.modelSEP c.Ψ).E.morIso ((Q.modelSEP c.Ψ).X.inv Φ)).ϕ y ∈
      (Q.modelSEP c.Ψ).X.PObj.smoothSet :=
    (((Q.modelSEP c.Ψ).E.morIso _).mem_smoothSet_iff hy).1 hys
  exact ((Q.modelSEP c.Ψ).E.pullOrx_morIso_eq_orMor (Q.modelFred c.Ψ hf) (Q.modelSec hbump c) _
    hy hϕs hys _).trans (Q.isModelInvariant_pullCat hf hbump hF c ho _ _ _ _ _)

end Orientations

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

end Polyfold
