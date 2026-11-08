import Polyfold.Chapter10.StrongBundleLocalization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.5 "Localization in the Strong Bundle Case" (pp. 504–508; 2017:
pp. 364–368): the tools for the weak fibred product of strong bundles over ep-groupoids, which
the text uses without spelling out (2021 p. 505: the composition of generalized strong bundle
maps is defined "following our earlier construction", i.e. that of Theorems 10.2.2 and 10.3.8).
The weak fibred product itself and the strong bundle version of Theorem 10.2.2 are in
`StrongBundleWeakFibredProduct.lean`; the category `SEP(F⁻¹)` of Definition 10.5.1 is in
`StrongBundleLocalizationCategory.lean`.

# Pull-backs, transports and inverse lifts of strong bundles over ep-groupoids

## What is formalized

For a strong bundle `(P : W → X, μ)` over an ep-groupoid `X` (Definition 8.3.1) and an
sc-smooth functor `π : A → X`:

* `EpStrongBundle.pullbackAlong`: the pull-back `(π*W, μ_π)` over `A`, with
  `μ_π(γ, (a, w)) = (t(γ), μ(π(γ), w))` (the analogue of `pullbackμ` in `Book2021.lean` for a
  functor in place of a groupoid map);
  `pullbackProjFunctor`, the projection `π*W → W`, a strong bundle functor covering `π`;
  `pullbackLiftFunctor`, the lift `W_C → π*W` of a strong bundle functor covering `π ∘ κ`.
* `isStrongBundleEquivalence_pullbackProjFunctor`: **if `π` is an equivalence, the projection
  `π*W → W` is a strong bundle equivalence** (Definition 10.4.1): it covers `π`, is an
  equivalence of the ep-groupoids `(π*W, 𝐀 ×_A π*W) → (W, 𝐗 ×_X W)`, induces a homeomorphism of
  the orbit spaces at level `[1]`, and restricts to strong bundle isomorphisms near every object
  and morphism.
* `IsStrongBundleEquivalence.of_comp_left`: two out of three for strong bundle equivalences
  (`Ψ`, `Ψ ∘ Φ` equivalences and `Φ` a strong bundle functor give `Φ` an equivalence), with the
  cancellation lemmas `IsScDiffeoOn.of_comp`, `IsStrongBundleIsoOn.of_comp`.
* `transportFunctor`: for a strong bundle functor `Ψ` covering `ψ` and a natural transformation
  `τ : ψ → ϕ`, the strong bundle functor `w ↦ μ'(τ(P w), Ψ(w))` covering `ϕ`, with the natural
  transformation of strong bundle functors `transportNatTrans : Ψ → Θ` (Definition 10.4.8).
* `invLiftFunctor`: for a strong bundle equivalence `Φ` covering `ϕ` and a strong bundle functor
  `Θ` covering `ϕ ∘ κ`, the unique strong bundle functor `Λ` covering `κ` with `Φ ∘ Λ = Θ`
  (`comp_invLiftFunctor`, `invLiftMap_eq`), fibrewise `Λ(c) = Φ_{κ(P c)}⁻¹(Θ(c))`; sc-smooth
  since it is locally `Φ⁻¹ ∘ Θ` for the local strong bundle isomorphisms of `Φ`.

## Our reading

The text's strong bundle equivalences are fibrewise linear isomorphisms (Proposition 10.4.4),
which is what makes `Λ` well defined; we use `IsStrongBundleEquivalence.fiberEquiv` and
`eq_of_obj_eq`.  Everything here is a tool; no statement of the text is stated in this file.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Lifts into a pull-back as strong bundle maps -/

section Lift

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {f : Z → X} [ParacompactSpace (pullbackSpace P f)]
  {V : Type*} [TopologicalSpace V] [T2Space V] [ParacompactSpace V] {PV : MPolyfold V}
  {R : Type*} [TopologicalSpace R] [T2Space R] [ParacompactSpace R] {Q : R → V}
  [∀ v, AddCommGroup (Q ⁻¹' {v})] [∀ v, Module ℝ (Q ⁻¹' {v})]

namespace StrongBundle

/-- A strong bundle map covering `g` covers any `g'` equal to `g`. -/
theorem IsStrongBundleMap.congr_base {BR : StrongBundle PV Q} {B : StrongBundle PX P}
    {g g' : V → X} {Θ : R → Y} (h : BR.IsStrongBundleMap B g Θ) (hg : g = g') :
    BR.IsStrongBundleMap B g' Θ := hg ▸ h

/-- **The universal property of the pull-back for strong bundle maps**: a strong bundle map
`Θ : R → Y` covering `f ∘ l` lifts to the strong bundle map `r ↦ (l(Q r), Θ(r))` into `f*Y`,
covering `l`. -/
theorem isStrongBundleMap_pullbackPair (B : StrongBundle PX P) (hf : PZ.IsScSmoothMap PX f)
    {BR : StrongBundle PV Q} {l : V → Z} (hl : PV.IsScSmoothMap PZ l) {Θ : R → Y}
    (hΘ : BR.IsStrongBundleMap B (f ∘ l) Θ) :
    BR.IsStrongBundleMap (B.pullback hf) l (pullbackPair P f (l ∘ Q) Θ hΘ.covers) where
  covers _ := rfl
  fiber_linear x := by
    let L : Q ⁻¹' {x} →ₗ[ℝ] pullbackProj P f ⁻¹' {l x} :=
      ((pullbackFiberLinearEquiv P f (l x)).symm.toLinearMap).comp (hΘ.fiber_linear x).mk'
    have hL : fiberRestrict Q (pullbackProj P f) l (pullbackPair P f (l ∘ Q) Θ hΘ.covers)
        (fun _ => rfl) x = L := by
      funext v
      apply Subtype.ext; apply Subtype.ext
      have hv : Q (v : R) = x := v.2
      change (l (Q v), Θ v) = (l x, Θ v)
      rw [hv]
    rw [hL]; exact L.isLinear
  isScSmoothMap := B.isScSmoothMap_pullbackPair hf (hl.comp BR.isScSmoothMap_proj)
    hΘ.isScSmoothMap hΘ.covers
  mapsTo_oneSet r hr := (B.mem_oneSet_pullback_iff hf _).2 (hΘ.mapsTo_oneSet hr)
  isScSmoothMap_one := by
    refine B.isScSmoothMap_to_pullback_one hf ?_ ?_
    · exact hl.comp BR.isScSmoothMap_proj1
    · exact MPolyfold.IsScSmoothOn.congr hΘ.isScSmoothMap_one fun a _ => B.oneVal_injective rfl

end StrongBundle

end Lift

/-! ### Cancelling sc-diffeomorphisms and local strong bundle isomorphisms -/

section Cancel

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  {X'' : Type*} [TopologicalSpace X''] [T2Space X''] [ParacompactSpace X''] {PX'' : MPolyfold X''}
  {Y'' : Type*} [TopologicalSpace Y''] [T2Space Y''] [ParacompactSpace Y''] {P'' : Y'' → X''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]

namespace MPolyfold

/-- **Left cancellation of sc-diffeomorphisms**: if `g ∘ f : U → U''` (inverse `G`) and
`g : V' → V''` (inverse `g'`) are sc-diffeomorphisms, and `f` is sc-smooth on `U` with
`f(U) ⊆ V'`, then `f : U → V' ∩ g⁻¹(U'')` is one, with inverse `G ∘ g`. -/
theorem IsScDiffeoOn.of_comp {f : X → X'} {g : X' → X''} {G : X'' → X} {g' : X'' → X'}
    {U : Set X} {U'' : Set X''} {V' : Set X'} {V'' : Set X''}
    (hgf : PX.IsScDiffeoOn PX'' (g ∘ f) G U U'') (hg : PX'.IsScDiffeoOn PX'' g g' V' V'')
    (hf : PX.IsScSmoothOn PX' f U) (hfU : MapsTo f U V') :
    PX.IsScDiffeoOn PX' f (G ∘ g) U (V' ∩ g ⁻¹' U'') where
  isScSmoothOn := hf
  isScSmoothOn_inv := IsScSmoothOn.comp hgf.isScSmoothOn_inv
    (hg.isScSmoothOn.mono (hg.isScSmoothOn.continuousOn.isOpen_inter_preimage hg.isOpen_source
      hgf.isOpen_target) inter_subset_left) fun _ hy => hy.2
  mapsTo _ hx := ⟨hfU hx, hgf.mapsTo hx⟩
  mapsTo_inv _ hy := hgf.mapsTo_inv hy.2
  left_inv x hx := hgf.left_inv x hx
  right_inv y hy :=
    (hg.left_inv _ (hfU (hgf.mapsTo_inv hy.2))).symm.trans
      ((congrArg g' (hgf.right_inv (g y) hy.2)).trans (hg.left_inv _ hy.1))

end MPolyfold

namespace StrongBundle

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {B'' : StrongBundle PX'' P''}

/-- A local strong bundle isomorphism over `U, U'` for `f` is one for any `f' = f`. -/
theorem IsStrongBundleIsoOn.of_eq {f f' : X → X'} {Φ : Y → Y'} {h : B.IsStrongBundleMap B' f Φ}
    {U : Set X} {U' : Set X'} (hi : B.IsStrongBundleIsoOn B' h U U') (hf : f = f') :
    B.IsStrongBundleIsoOn B' (h.congr_base hf) U U' := by
  subst hf; exact hi

/-- **Left cancellation of local strong bundle isomorphisms**: if `Ψ ∘ Φ : Y|U → Y''|U''` and
`Ψ : Y'|V' → Y''|V''` are strong bundle isomorphisms and `f(U) ⊆ V'`, then `Φ` is a strong bundle
isomorphism `Y|U → Y'|(V' ∩ f'⁻¹(U''))`. -/
theorem IsStrongBundleIsoOn.of_comp {f : X → X'} {Φ : Y → Y'} {h : B.IsStrongBundleMap B' f Φ}
    {f' : X' → X''} {Ψ : Y' → Y''} {h' : B'.IsStrongBundleMap B'' f' Ψ} {U : Set X}
    {U'' : Set X''} {V' : Set X'} {V'' : Set X''}
    (hc : B.IsStrongBundleIsoOn B'' (h'.comp h) U U'') (hi' : B'.IsStrongBundleIsoOn B'' h' V' V'')
    (hU : MapsTo f U V') : B.IsStrongBundleIsoOn B' h U (V' ∩ f' ⁻¹' U'') := by
  obtain ⟨G, hG⟩ := hc.isScDiffeoOn_base
  obtain ⟨g', hg'⟩ := hi'.isScDiffeoOn_base
  obtain ⟨Gi, hGi⟩ := hc.isScDiffeoOn_zero
  obtain ⟨Ψi, hΨi⟩ := hi'.isScDiffeoOn_zero
  obtain ⟨G₁, hG₁⟩ := hc.isScDiffeoOn_one
  obtain ⟨Ψ₁, hΨ₁⟩ := hi'.isScDiffeoOn_one
  have hUo : IsOpen U := hG.isOpen_source
  refine ⟨⟨_, hG.of_comp hg' (h.isScSmoothMap_base.mono hUo (subset_univ _)) hU⟩, ⟨Gi ∘ Ψ, ?_⟩,
    ⟨G₁ ∘ oneRestrict B' B'' Ψ h'.mapsTo_oneSet, ?_⟩⟩
  · have e := hGi.of_comp hΨi (h.isScSmoothMap.mono (hUo.preimage B.continuous) (subset_univ _))
      fun y hy => by
        change P' (Φ y) ∈ V'
        rw [h.covers]; exact hU hy
    have hset : P' ⁻¹' V' ∩ Ψ ⁻¹' (P'' ⁻¹' U'') = P' ⁻¹' (V' ∩ f' ⁻¹' U'') := by
      ext y
      simp only [mem_inter_iff, mem_preimage, h'.covers]
    rwa [hset] at e
  · have hc1 : Continuous (P ∘ B.oneVal) := B.continuous.comp B.continuous_oneVal
    have e := MPolyfold.IsScDiffeoOn.of_comp (f := oneRestrict B B' Φ h.mapsTo_oneSet)
      (g := oneRestrict B' B'' Ψ h'.mapsTo_oneSet) hG₁ hΨ₁
      (h.isScSmoothMap_one.mono (hUo.preimage hc1) (subset_univ _)) fun y hy => by
        change P' (Φ (B.oneVal y)) ∈ V'
        rw [h.covers]; exact hU hy
    have hset : (P' ∘ B'.oneVal) ⁻¹' V' ∩
        oneRestrict B' B'' Ψ h'.mapsTo_oneSet ⁻¹' ((P'' ∘ B''.oneVal) ⁻¹' U'') =
        (P' ∘ B'.oneVal) ⁻¹' (V' ∩ f' ⁻¹' U'') := by
      ext y
      simp only [mem_inter_iff, mem_preimage, Function.comp_apply, oneVal_oneRestrict, h'.covers]
    rwa [hset] at e

/-- A point of `Y_{0,1}` over every `x` (the zero of the fibre). -/
theorem exists_one_over (B : StrongBundle PX P) (x : X) : ∃ y : B.One, P (B.oneVal y) = x := by
  obtain ⟨g, hg, -⟩ :=
    ((B.isScPlusSection_iff (fiberZero P)).1 StrongBundle.isScPlusSection_fiberZero).2
  exact ⟨g x, by rw [show B.oneVal (g x) = fiberZero P x from congrFun hg x]; exact
    proj_fiberZero P x⟩

end StrongBundle

end Cancel

section PullbackIso

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {f : Z → X} [ParacompactSpace (pullbackSpace P f)]

namespace StrongBundle

open scoped Classical in
/-- The level-`[1]` inverse `y ↦ (σ(P y), y)` of `P' : f*Y[1] → Y[1]` over a sheet `σ` of `f` on
`V` (junk value `q₁` off `V`). -/
def pullbackSheetInvOne (B : StrongBundle PX P) (hf : PZ.IsScSmoothMap PX f) (σ : X → Z)
    (V : Set X) (hσ : ∀ x ∈ V, f (σ x) = x) (q₁ : (B.pullback hf).One) (y : B.One) :
    (B.pullback hf).One :=
  if h : P (B.oneVal y) ∈ V then
    (B.pullback hf).oneMk ⟨(σ (P (B.oneVal y)), B.oneVal y), (hσ _ h).symm⟩
      ((B.mem_oneSet_pullback_iff hf _).2 (B.oneVal_mem y))
  else q₁

theorem pullbackSheetInvOne_val (B : StrongBundle PX P) (hf : PZ.IsScSmoothMap PX f) {σ : X → Z}
    {V : Set X} (hσ : ∀ x ∈ V, f (σ x) = x) (q₁ : (B.pullback hf).One) {y : B.One}
    (hy : P (B.oneVal y) ∈ V) :
    ((B.pullback hf).oneVal (B.pullbackSheetInvOne hf σ V hσ q₁ y) : Z × Y) =
      (σ (P (B.oneVal y)), B.oneVal y) := by
  unfold pullbackSheetInvOne; rw [dif_pos hy]; rfl

/-- **The pull-back along a sheet of `f` is a local strong bundle isomorphism**: over an
sc-diffeomorphism `f : U → V`, `P' : f*Y → Y` is a strong bundle isomorphism
`f*Y|U → Y|V` covering `f`, at the levels `[0]` and `[1]` (inverses `y ↦ (σ(P y), y)`). -/
theorem isStrongBundleIsoOn_pullbackProj' (B : StrongBundle PX P) (hf : PZ.IsScSmoothMap PX f)
    {σ : X → Z} {U : Set Z} {V : Set X} (hd : PZ.IsScDiffeoOn PX f σ U V) (z₀ : Z) :
    (B.pullback hf).IsStrongBundleIsoOn B (B.isStrongBundleMap_pullbackProj' hf) U V := by
  obtain ⟨y₀, hy₀⟩ := B.exists_one_over (f z₀)
  let q₁ : (B.pullback hf).One := (B.pullback hf).oneMk ⟨(z₀, B.oneVal y₀), hy₀⟩
    ((B.mem_oneSet_pullback_iff hf _).2 (B.oneVal_mem y₀))
  refine ⟨⟨σ, hd⟩, ⟨_, B.isScDiffeoOn_pullbackProj' hf hd ((B.pullback hf).oneVal q₁)⟩,
    ⟨B.pullbackSheetInvOne hf σ V hd.right_inv q₁, ?_⟩⟩
  have hc1 : Continuous (P ∘ B.oneVal) := B.continuous.comp B.continuous_oneVal
  have hc1' : Continuous (pullbackProj P f ∘ (B.pullback hf).oneVal) :=
    (continuous_pullbackProj P f).comp (B.pullback hf).continuous_oneVal
  have hVo : IsOpen ((P ∘ B.oneVal) ⁻¹' V) := hd.isOpen_target.preimage hc1
  refine ⟨(B.isScSmoothMap_one_pullbackProj' hf).mono (hd.isOpen_source.preimage hc1')
    (subset_univ _), ?_, ?_, ?_, ?_, ?_⟩
  · refine B.isScSmoothOn_to_pullback_one hf ?_ ?_
    · refine (MPolyfold.IsScSmoothOn.comp hd.isScSmoothOn_inv
        (B.isScSmoothMap_proj1.mono hVo (subset_univ _)) fun _ hy => hy).congr fun y hy => ?_
      change σ (P (B.oneVal y)) = ((B.pullback hf).oneVal _ : Z × Y).1
      rw [B.pullbackSheetInvOne_val hf hd.right_inv q₁ hy]
    · refine (MPolyfold.isScSmoothMap_id.mono hVo (subset_univ _)).congr fun y hy => ?_
      apply B.oneVal_injective
      change B.oneVal y = ((B.pullback hf).oneVal _ : Z × Y).2
      rw [B.pullbackSheetInvOne_val hf hd.right_inv q₁ hy]
  · intro q hq
    change P ((B.pullback hf).oneVal q : Z × Y).2 ∈ V
    rw [show P ((B.pullback hf).oneVal q : Z × Y).2 = f ((B.pullback hf).oneVal q : Z × Y).1
      from ((B.pullback hf).oneVal q).2]
    exact hd.mapsTo hq
  · intro y hy
    change (((B.pullback hf).oneVal _ : Z × Y)).1 ∈ U
    rw [B.pullbackSheetInvOne_val hf hd.right_inv q₁ hy]
    exact hd.mapsTo_inv hy
  · intro q hq
    have hPq : P (B.oneVal (oneRestrict (B.pullback hf) B (pullbackProj' P f)
        (B.isStrongBundleMap_pullbackProj' hf).mapsTo_oneSet q)) ∈ V := by
      change P ((B.pullback hf).oneVal q : Z × Y).2 ∈ V
      rw [show P ((B.pullback hf).oneVal q : Z × Y).2 = f ((B.pullback hf).oneVal q : Z × Y).1
        from ((B.pullback hf).oneVal q).2]
      exact hd.mapsTo hq
    apply (B.pullback hf).oneVal_injective
    apply Subtype.ext
    rw [B.pullbackSheetInvOne_val hf hd.right_inv q₁ hPq]
    refine Prod.ext ?_ rfl
    change σ (P ((B.pullback hf).oneVal q : Z × Y).2) = _
    rw [show P ((B.pullback hf).oneVal q : Z × Y).2 = f ((B.pullback hf).oneVal q : Z × Y).1
      from ((B.pullback hf).oneVal q).2]
    exact hd.left_inv _ hq
  · intro y hy
    apply B.oneVal_injective
    change (((B.pullback hf).oneVal _ : Z × Y)).2 = _
    rw [B.pullbackSheetInvOne_val hf hd.right_inv q₁ hy]

end StrongBundle

end PullbackIso

/-! ### The pull-back of a strong bundle over an ep-groupoid along a functor -/

section PullbackAlong

variable {ObjA MorA : Type u} [TopologicalSpace ObjA] [T2Space ObjA] [ParacompactSpace ObjA]
  [TopologicalSpace MorA] [T2Space MorA] [ParacompactSpace MorA] {A : EpGroupoid ObjA MorA}
  {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  (E : EpStrongBundle X B) (π : EpFunctor A X)
  [ParacompactSpace (pullbackSpace P π.obj)]
  [ParacompactSpace (pullbackSpace (pullbackProj P π.obj) A.src)]

namespace EpStrongBundle

omit [TopologicalSpace W] [T2Space W] [ParacompactSpace W] [∀ x, AddCommGroup (P ⁻¹' {x})]
  [∀ x, Module ℝ (P ⁻¹' {x})] [ParacompactSpace (pullbackSpace P X.src)]
  [ParacompactSpace (pullbackSpace P π.obj)]
  [ParacompactSpace (pullbackSpace (pullbackProj P π.obj) A.src)] in
theorem pbMorPair_mem (q : pullbackSpace (pullbackProj P π.obj) A.src) :
    P ((q : MorA × pullbackSpace P π.obj).2 : ObjA × W).2 =
      X.src (π.mor (q : MorA × pullbackSpace P π.obj).1) :=
  ((q : MorA × pullbackSpace P π.obj).2.2 :).trans ((congrArg π.obj q.2).trans (π.src_mor _).symm)

/-- `(m, (a, w)) ↦ (π(m), w) ∈ 𝐗 ₛ×_P W`. -/
def pbMorPair : pullbackSpace (pullbackProj P π.obj) A.src → pullbackSpace P X.src :=
  pullbackPair P X.src (π.mor ∘ pullbackProj (pullbackProj P π.obj) A.src)
    (pullbackProj' P π.obj ∘ pullbackProj' (pullbackProj P π.obj) A.src) (pbMorPair_mem π)

/-- **The structure map of the pull-back `π*W`**: `μ_π(m, (a, w)) = (t(m), μ(π(m), w))`. -/
def pbμ : pullbackSpace (pullbackProj P π.obj) A.src → pullbackSpace P π.obj :=
  pullbackPair P π.obj (A.tgt ∘ pullbackProj (pullbackProj P π.obj) A.src) (E.μ ∘ pbMorPair π)
    (fun _ => (E.P_μ _).trans (π.tgt_mor _))

@[simp] theorem pbμ_val (q : pullbackSpace (pullbackProj P π.obj) A.src) :
    (E.pbμ π q : ObjA × W) = (A.tgt (q : MorA × pullbackSpace P π.obj).1,
      E.μ ⟨(π.mor (q : MorA × pullbackSpace P π.obj).1,
        ((q : MorA × pullbackSpace P π.obj).2 : ObjA × W).2), pbMorPair_mem π q⟩) := rfl

theorem isStrongBundleMap_pbMorPair :
    ((B.pullback π.isScSmoothMap_obj).pullback A.isScSmoothMap_src).IsStrongBundleMap
      (B.pullback X.isScSmoothMap_src) π.mor (pbMorPair π) :=
  B.isStrongBundleMap_pullbackPair X.isScSmoothMap_src π.isScSmoothMap_mor
    (((B.isStrongBundleMap_pullbackProj' π.isScSmoothMap_obj).comp
      ((B.pullback π.isScSmoothMap_obj).isStrongBundleMap_pullbackProj'
        A.isScSmoothMap_src)).congr_base (funext fun m => (π.src_mor m).symm))

theorem isStrongBundleMap_pbμ :
    ((B.pullback π.isScSmoothMap_obj).pullback A.isScSmoothMap_src).IsStrongBundleMap
      (B.pullback π.isScSmoothMap_obj) A.tgt (E.pbμ π) :=
  B.isStrongBundleMap_pullbackPair π.isScSmoothMap_obj A.isScSmoothMap_tgt
    ((E.isStrongBundleMap.comp (isStrongBundleMap_pbMorPair π)).congr_base
      (funext fun m => π.tgt_mor m))

theorem pbμ_unit (w : pullbackSpace P π.obj) : E.pbμ π (A.unitPair w) = w := by
  apply Subtype.ext
  rw [pbμ_val]
  refine Prod.ext (A.tgt_unit _) ((E.μ_congr ?_).trans (E.μ_unit _))
  change (π.mor (A.unit (w : ObjA × W).1), (w : ObjA × W).2) =
    (X.unit (P (w : ObjA × W).2), (w : ObjA × W).2)
  rw [π.mor_unit, (w.2 : P (w : ObjA × W).2 = π.obj (w : ObjA × W).1)]

theorem pbμ_comp (ψ γ : MorA) (w : pullbackSpace P π.obj)
    (h₁ : pullbackProj P π.obj w = A.src γ) (h₂ : A.src ψ = A.tgt γ) :
    E.pbμ π ⟨(A.comp ψ γ, w), h₁.trans (A.src_comp ψ γ h₂).symm⟩ =
      E.pbμ π ⟨(ψ, E.pbμ π ⟨(γ, w), h₁⟩), h₂.symm⟩ := by
  apply Subtype.ext
  rw [pbμ_val, pbμ_val]
  refine Prod.ext (A.tgt_comp ψ γ h₂) ?_
  have hw : P (w : ObjA × W).2 = X.src (π.mor γ) := pbMorPair_mem π ⟨(γ, w), h₁⟩
  have h₂' : X.src (π.mor ψ) = X.tgt (π.mor γ) := by rw [π.src_mor, π.tgt_mor, h₂]
  refine (E.μ_congr ?_).trans ((E.μ_comp (π.mor ψ) (π.mor γ) _ hw h₂').trans ?_)
  · change (π.mor (A.comp ψ γ), (w : ObjA × W).2) = (X.comp (π.mor ψ) (π.mor γ), _)
    rw [π.mor_comp _ _ h₂]
  · rfl

open scoped Classical in
/-- `(a', w') ↦ (π(σ a')⁻¹, w') ∈ 𝐗 ₛ×_P W` for a map `σ : A → 𝐀` (junk `(1, w')` when the pair is
not composable). -/
def pbInvAux (σ : ObjA → MorA) (q' : pullbackSpace P π.obj) : pullbackSpace P X.src :=
  if h : P (q' : ObjA × W).2 = X.src (X.inv (π.mor (σ (q' : ObjA × W).1))) then
    ⟨(X.inv (π.mor (σ (q' : ObjA × W).1)), (q' : ObjA × W).2), h⟩
  else X.unitPair (q' : ObjA × W).2

omit [ParacompactSpace (pullbackSpace P X.src)] [ParacompactSpace (pullbackSpace P π.obj)]
  [ParacompactSpace (pullbackSpace (pullbackProj P π.obj) A.src)] in
theorem pbInvAux_val {σ : ObjA → MorA} {q' : pullbackSpace P π.obj}
    (h : A.tgt (σ (q' : ObjA × W).1) = (q' : ObjA × W).1) :
    (pbInvAux π σ q' : Mor × W) = (X.inv (π.mor (σ (q' : ObjA × W).1)), (q' : ObjA × W).2) := by
  have hc : P (q' : ObjA × W).2 = X.src (X.inv (π.mor (σ (q' : ObjA × W).1))) := by
    rw [X.src_inv, π.tgt_mor, h]; exact q'.2
  unfold pbInvAux; rw [dif_pos hc]

omit [ParacompactSpace (pullbackSpace P π.obj)]
  [ParacompactSpace (pullbackSpace (pullbackProj P π.obj) A.src)] in
theorem P_μ_pbInvAux {σ : ObjA → MorA} {q' : pullbackSpace P π.obj}
    (h : A.tgt (σ (q' : ObjA × W).1) = (q' : ObjA × W).1) :
    P (E.μ (pbInvAux π σ q')) = π.obj (A.src (σ (q' : ObjA × W).1)) := by
  rw [E.P_μ, pbInvAux_val π h, X.tgt_inv, π.src_mor]

open scoped Classical in
/-- **The local inverse of `μ_π`** over a sheet `σ` of `t` on `V`:
`(a', w') ↦ (σ(a'), (s(σ a'), μ(π(σ a')⁻¹, w')))`; junk value `q₀` off `V`. -/
def pbμInv (σ : ObjA → MorA) (V : Set ObjA) (hσ : ∀ a ∈ V, A.tgt (σ a) = a)
    (q₀ : pullbackSpace (pullbackProj P π.obj) A.src) (q' : pullbackSpace P π.obj) :
    pullbackSpace (pullbackProj P π.obj) A.src :=
  if h : (q' : ObjA × W).1 ∈ V then
    ⟨(σ (q' : ObjA × W).1, ⟨(A.src (σ (q' : ObjA × W).1), E.μ (pbInvAux π σ q')),
      E.P_μ_pbInvAux π (hσ _ h)⟩), rfl⟩
  else q₀

omit [ParacompactSpace (pullbackSpace P π.obj)]
  [ParacompactSpace (pullbackSpace (pullbackProj P π.obj) A.src)] in
theorem pbμInv_val {σ : ObjA → MorA} {V : Set ObjA} (hσ : ∀ a ∈ V, A.tgt (σ a) = a)
    (q₀ : pullbackSpace (pullbackProj P π.obj) A.src) {q' : pullbackSpace P π.obj}
    (h : (q' : ObjA × W).1 ∈ V) :
    (E.pbμInv π σ V hσ q₀ q' : MorA × pullbackSpace P π.obj) = (σ (q' : ObjA × W).1,
      ⟨(A.src (σ (q' : ObjA × W).1), E.μ (pbInvAux π σ q')),
        E.P_μ_pbInvAux π (hσ _ h)⟩) := by
  unfold pbμInv; rw [dif_pos h]

/-- **`μ_π` is a local sc-diffeomorphism** (Definition 8.3.1 (1) for `π*W`): near `(m, (a, w))`,
with a sheet `σ` of `t` at `m`, the inverse is `(a', w') ↦ (σ(a'), (s(σ a'), μ(π(σ a')⁻¹, w')))`. -/
theorem isLocalScDiffeo_pbμ :
    ((B.pullback π.isScSmoothMap_obj).pullback A.isScSmoothMap_src).toMPolyfold0.IsLocalScDiffeo
      (B.pullback π.isScSmoothMap_obj).toMPolyfold0 (E.pbμ π) := by
  intro q₀
  obtain ⟨U, V, σ, hm, hd⟩ := A.isLocalScDiffeo_tgt (q₀ : MorA × pullbackSpace P π.obj).1
  set Bπ := B.pullback π.isScSmoothMap_obj
  set Bπ' := Bπ.pullback A.isScSmoothMap_src
  have hV' : IsOpen (pullbackProj P π.obj ⁻¹' V) :=
    hd.isOpen_target.preimage (continuous_pullbackProj P π.obj)
  have hU' : IsOpen (pullbackProj (pullbackProj P π.obj) A.src ⁻¹' U) :=
    hd.isOpen_source.preimage (continuous_pullbackProj _ _)
  have hσV : ∀ a ∈ V, A.tgt (σ a) = a := hd.right_inv
  -- smoothness of the pieces of the inverse on `V'`
  have hσs : Bπ.toMPolyfold0.IsScSmoothOn A.PMor (σ ∘ pullbackProj P π.obj)
      (pullbackProj P π.obj ⁻¹' V) :=
    MPolyfold.IsScSmoothOn.comp hd.isScSmoothOn_inv (Bπ.isScSmoothMap_proj.mono hV' (subset_univ _))
      fun _ h => h
  have hinvs : Bπ.toMPolyfold0.IsScSmoothOn X.PMor
      (X.inv ∘ π.mor ∘ σ ∘ pullbackProj P π.obj) (pullbackProj P π.obj ⁻¹' V) :=
    MPolyfold.IsScSmoothOn.comp (g := X.inv ∘ π.mor)
      (X.isScSmoothMap_inv.comp π.isScSmoothMap_mor) hσs (mapsTo_univ _ _)
  have hauxs : Bπ.toMPolyfold0.IsScSmoothOn (B.pullback X.isScSmoothMap_src).toMPolyfold0
      (pbInvAux π σ) (pullbackProj P π.obj ⁻¹' V) :=
    B.isScSmoothOn_to_pullback_of_eqOn X.isScSmoothMap_src hinvs
      ((B.isScSmoothMap_pullbackProj' π.isScSmoothMap_obj).mono hV' (subset_univ _))
      fun q' hq' => pbInvAux_val π (hσV _ hq')
  have hμs : Bπ.toMPolyfold0.IsScSmoothOn B.toMPolyfold0 (E.μ ∘ pbInvAux π σ)
      (pullbackProj P π.obj ⁻¹' V) :=
    MPolyfold.IsScSmoothOn.comp E.isStrongBundleMap.isScSmoothMap hauxs (mapsTo_univ _ _)
  have hsrcs : Bπ.toMPolyfold0.IsScSmoothOn A.PObj (A.src ∘ σ ∘ pullbackProj P π.obj)
      (pullbackProj P π.obj ⁻¹' V) :=
    MPolyfold.IsScSmoothOn.comp (g := A.src) A.isScSmoothMap_src hσs (mapsTo_univ _ _)
  have hmid : Bπ.toMPolyfold0.IsScSmoothOn Bπ.toMPolyfold0
      (fun q' => ((E.pbμInv π σ V hσV q₀ q' : MorA × pullbackSpace P π.obj).2))
      (pullbackProj P π.obj ⁻¹' V) :=
    B.isScSmoothOn_to_pullback_of_eqOn π.isScSmoothMap_obj hsrcs hμs fun q' hq' => by
      rw [E.pbμInv_val π hσV q₀ hq']; rfl
  have hinv : Bπ.toMPolyfold0.IsScSmoothOn Bπ'.toMPolyfold0 (E.pbμInv π σ V hσV q₀)
      (pullbackProj P π.obj ⁻¹' V) :=
    Bπ.isScSmoothOn_to_pullback_of_eqOn A.isScSmoothMap_src hσs hmid fun q' hq' => by
      rw [E.pbμInv_val π hσV q₀ hq']; rfl
  refine ⟨pullbackProj (pullbackProj P π.obj) A.src ⁻¹' U, pullbackProj P π.obj ⁻¹' V,
    E.pbμInv π σ V hσV q₀, hm, ?_⟩
  refine ⟨(E.isStrongBundleMap_pbμ π).isScSmoothMap.mono hU' (subset_univ _), hinv, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact hd.mapsTo hq
  · intro q' hq'
    change (E.pbμInv π σ V hσV q₀ q' : MorA × pullbackSpace P π.obj).1 ∈ U
    rw [E.pbμInv_val π hσV q₀ hq']
    exact hd.mapsTo_inv hq'
  · intro q hq
    have hq1 : (q : MorA × pullbackSpace P π.obj).1 ∈ U := hq
    have hV : (E.pbμ π q : ObjA × W).1 ∈ V := hd.mapsTo hq1
    have hσt : σ (E.pbμ π q : ObjA × W).1 = (q : MorA × pullbackSpace P π.obj).1 :=
      hd.left_inv _ hq1
    apply Subtype.ext
    rw [E.pbμInv_val π hσV q₀ hV]
    refine Prod.ext hσt (Subtype.ext ?_)
    change (A.src (σ (E.pbμ π q : ObjA × W).1), E.μ (pbInvAux π σ (E.pbμ π q))) =
      ((q : MorA × pullbackSpace P π.obj).2 : ObjA × W)
    refine Prod.ext ?_ ?_
    · rw [hσt]; exact q.2.symm
    · have h1 := pbInvAux_val π (σ := σ) (q' := E.pbμ π q) (hσV _ hV)
      rw [hσt] at h1
      have h5 : E.μ (pbInvAux π σ (E.pbμ π q)) = E.μ ⟨(X.inv (pbMorPair π q : Mor × W).1,
          E.μ (pbMorPair π q)), by
            change P (E.μ _) = X.src (X.inv _); rw [E.P_μ, X.src_inv]⟩ := E.μ_congr h1
      rw [h5]
      exact E.μ_inv_μ (pbMorPair π q) _
  · intro q' hq'
    have hq1 : (q' : ObjA × W).1 ∈ V := hq'
    apply Subtype.ext
    rw [pbμ_val]
    have hv := E.pbμInv_val π hσV q₀ hq1
    refine Prod.ext ?_ ?_
    · change A.tgt (E.pbμInv π σ V hσV q₀ q' : MorA × pullbackSpace P π.obj).1 = _
      rw [hv]; exact hσV _ hq1
    · have h2 : E.μ ⟨(π.mor (E.pbμInv π σ V hσV q₀ q' : MorA × pullbackSpace P π.obj).1,
          ((E.pbμInv π σ V hσV q₀ q' : MorA × pullbackSpace P π.obj).2 : ObjA × W).2),
          pbMorPair_mem π _⟩ =
          E.μ ⟨(π.mor (σ (q' : ObjA × W).1), E.μ (pbInvAux π σ q')),
            (E.P_μ_pbInvAux π (hσV _ hq1)).trans (π.src_mor _).symm⟩ :=
          E.μ_congr (Prod.ext (congrArg π.mor (congrArg Prod.fst hv))
            (congrArg (fun p : MorA × pullbackSpace P π.obj => (p.2 : ObjA × W).2) hv))
      rw [h2]
      have h3 := pbInvAux_val π (σ := σ) (q' := q') (hσV _ hq1)
      have h4 : E.μ (pbInvAux π σ q') = E.μ ⟨(X.inv (π.mor (σ (q' : ObjA × W).1)),
          (q' : ObjA × W).2), by rw [← h3]; exact (pbInvAux π σ q').2⟩ := E.μ_congr h3
      simp only [h4]
      exact E.μ_μ_inv _ _ _ _

/-- **The pull-back `π*W → A` of a strong bundle `(P : W → X, μ)` over an ep-groupoid along an
sc-smooth functor `π : A → X`**: the pull-back strong bundle `A ×_X W → A` of Part I with the
structure map `μ_π(m, (a, w)) = (t(m), μ(π(m), w))`. -/
def pullbackAlong : EpStrongBundle A (B.pullback π.isScSmoothMap_obj) where
  μ := E.pbμ π
  isStrongBundleMap := E.isStrongBundleMap_pbμ π
  surjective w := ⟨A.unitPair w, E.pbμ_unit π w⟩
  isLocalScDiffeo := E.isLocalScDiffeo_pbμ π
  μ_unit := E.pbμ_unit π
  μ_comp := E.pbμ_comp π

@[simp] theorem pullbackAlong_μ : (E.pullbackAlong π).μ = E.pbμ π := rfl

/-- **The projection `Π : π*W → W`, `(a, w) ↦ w`, covers `π`** (Definition 8.5). -/
theorem isMap_pullbackProj' :
    (E.pullbackAlong π).IsMap E π (pullbackProj' P π.obj) where
  isStrongBundleMap := B.isStrongBundleMap_pullbackProj' π.isScSmoothMap_obj
  map_μ _ _ _ := rfl

/-- **The projection functor `Π : π*W → W`** (a strong bundle functor covering `π`). -/
def pullbackProjFunctor : EpFunctor (E.pullbackAlong π).toEpGroupoid E.toEpGroupoid :=
  (E.isMap_pullbackProj' π).liftFunctor

theorem isStrongBundleFunctor_pullbackProjFunctor :
    (E.pullbackAlong π).IsStrongBundleFunctor E π (E.pullbackProjFunctor π) :=
  (E.isMap_pullbackProj' π).isStrongBundleFunctor_liftFunctor

@[simp] theorem pullbackProjFunctor_obj :
    (E.pullbackProjFunctor π).obj = pullbackProj' P π.obj := rfl

variable {ObjC MorC : Type u} [TopologicalSpace ObjC] [T2Space ObjC] [ParacompactSpace ObjC]
  [TopologicalSpace MorC] [T2Space MorC] [ParacompactSpace MorC] {Y : EpGroupoid ObjC MorC}
  {WC : Type u} [TopologicalSpace WC] [T2Space WC] [ParacompactSpace WC] {PC : WC → ObjC}
  [∀ x, AddCommGroup (PC ⁻¹' {x})] [∀ x, Module ℝ (PC ⁻¹' {x})] {BC : StrongBundle Y.PObj PC}
  [ParacompactSpace (pullbackSpace PC Y.src)] {C : EpStrongBundle Y BC}

/-- **The lift into the pull-back**: for a strong bundle map `Θ : W_C → W` covering `π ∘ κ`, the
map `c ↦ (κ(P_C c), Θ(c)) ∈ π*W`. -/
def pullbackLift {κ : EpFunctor Y A} {Θ : WC → W} (hΘ : C.IsMap E (π.comp κ) Θ) :
    WC → pullbackSpace P π.obj :=
  pullbackPair P π.obj (κ.obj ∘ PC) Θ hΘ.isStrongBundleMap.covers

/-- **The universal property of `π*W`**: the lift covers `κ` (Definition 8.5). -/
theorem isMap_pullbackLift {κ : EpFunctor Y A} {Θ : WC → W} (hΘ : C.IsMap E (π.comp κ) Θ) :
    C.IsMap (E.pullbackAlong π) κ (E.pullbackLift π hΘ) where
  isStrongBundleMap := B.isStrongBundleMap_pullbackPair π.isScSmoothMap_obj κ.isScSmoothMap_obj
    hΘ.isStrongBundleMap
  map_μ γ c h := Subtype.ext (Prod.ext (by
    change κ.obj (PC (C.μ _)) = A.tgt (κ.mor γ)
    rw [C.P_μ, κ.tgt_mor]) (hΘ.map_μ γ c h))

/-- The lift as a strong bundle functor `W_C → π*W` covering `κ`. -/
def pullbackLiftFunctor {κ : EpFunctor Y A} {Θ : WC → W} (hΘ : C.IsMap E (π.comp κ) Θ) :
    EpFunctor C.toEpGroupoid (E.pullbackAlong π).toEpGroupoid :=
  (E.isMap_pullbackLift π hΘ).liftFunctor

theorem isStrongBundleFunctor_pullbackLiftFunctor {κ : EpFunctor Y A} {Θ : WC → W}
    (hΘ : C.IsMap E (π.comp κ) Θ) :
    C.IsStrongBundleFunctor (E.pullbackAlong π) κ (E.pullbackLiftFunctor π hΘ) :=
  (E.isMap_pullbackLift π hΘ).isStrongBundleFunctor_liftFunctor

/-- `Π ∘ ℓ = Θ` (as functors). -/
theorem pullbackProjFunctor_comp_pullbackLiftFunctor {κ : EpFunctor Y A} {Θ : WC → W}
    (hΘ : C.IsMap E (π.comp κ) Θ) :
    (E.pullbackProjFunctor π).comp (E.pullbackLiftFunctor π hΘ) = hΘ.liftFunctor :=
  EpFunctor.ext rfl rfl

end EpStrongBundle

end PullbackAlong

/-! ### Two out of three for strong bundle equivalences -/

theorem isHomeomorph_of_comp_left {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [TopologicalSpace γ] {f : α → β} {g : β → γ} (hg : IsHomeomorph g)
    (hgf : IsHomeomorph (g ∘ f)) : IsHomeomorph f := by
  have hpre : ∀ S : Set β, f ⁻¹' S = (g ∘ f) ⁻¹' (g '' S) := fun S => by
    ext a; simp only [mem_preimage, Function.comp_apply, hg.injective.mem_set_image]
  have himg : ∀ O : Set α, f '' O = g ⁻¹' ((g ∘ f) '' O) := fun O => by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, rfl⟩
    · rintro ⟨a, ha, hab⟩; exact ⟨a, ha, hg.injective hab⟩
  refine ⟨continuous_def.2 fun S hS => ?_, fun O hO => ?_, ⟨hgf.injective.of_comp, fun b => ?_⟩⟩
  · rw [hpre]; exact hgf.continuous.isOpen_preimage _ (hg.isOpenMap _ hS)
  · rw [himg]; exact (hgf.isOpenMap _ hO).preimage hg.continuous
  · obtain ⟨a, ha⟩ := hgf.surjective (g b)
    exact ⟨a, hg.injective ha⟩

section TwoOutOfThree

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

namespace EpStrongBundle

/-- **Two out of three for strong bundle equivalences**: if `Ψ` and `Ψ ∘ Φ` are strong bundle
equivalences and `Φ` is a strong bundle functor, then `Φ` is a strong bundle equivalence. -/
theorem IsStrongBundleEquivalence.of_comp_left {ϕ : EpFunctor X X'} {ψ : EpFunctor X' X''}
    {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} {Ψ : EpFunctor E'.toEpGroupoid E''.toEpGroupoid}
    (hΨ : E'.IsStrongBundleEquivalence E'' ψ Ψ) (hΦ : E.IsStrongBundleFunctor E' ϕ Φ)
    (hΨΦ : E.IsStrongBundleEquivalence E'' (ψ.comp ϕ) (Ψ.comp Φ)) :
    E.IsStrongBundleEquivalence E' ϕ Φ where
  isStrongBundleFunctor := hΦ
  isEquivalence_base :=
    EpFunctor.IsEquivalence.of_comp_left hΨ.isEquivalence_base hΨΦ.isEquivalence_base
  isEquivalence := EpFunctor.IsEquivalence.of_comp_left hΨ.isEquivalence hΨΦ.isEquivalence
  isHomeomorph_oneOrbitMap := by
    have hgf := hΨΦ.isHomeomorph_oneOrbitMap
    rw [oneOrbitMap_comp hΦ.isStrongBundleMap_obj.mapsTo_oneSet
      hΨ.isStrongBundleFunctor.isStrongBundleMap_obj.mapsTo_oneSet] at hgf
    exact isHomeomorph_of_comp_left hΨ.isHomeomorph_oneOrbitMap hgf
  isLocalStrongBundleIso_obj x := by
    obtain ⟨U, U'', hx, hc⟩ := hΨΦ.isLocalStrongBundleIso_obj x
    obtain ⟨V', V'', hx', hi'⟩ := hΨ.isLocalStrongBundleIso_obj (ϕ.obj x)
    obtain ⟨G, hG⟩ := hc.isScDiffeoOn_base
    obtain ⟨g', hg'⟩ := hi'.isScDiffeoOn_base
    have hU₀ : IsOpen (U ∩ ϕ.obj ⁻¹' V') :=
      hG.isOpen_source.inter (hg'.isOpen_source.preimage ϕ.continuous_obj')
    have hc₀ := hc.restrict hG hU₀ inter_subset_left
    exact ⟨U ∩ ϕ.obj ⁻¹' V', _, ⟨hx, hx'⟩, StrongBundle.IsStrongBundleIsoOn.of_comp
      (h := hΦ.isStrongBundleMap_obj) (h' := hΨ.isStrongBundleFunctor.isStrongBundleMap_obj) hc₀
      hi' fun y hy => hy.2⟩
  isLocalStrongBundleIso_mor φ := by
    obtain ⟨U, U'', hx, hc⟩ := hΨΦ.isLocalStrongBundleIso_mor φ
    obtain ⟨V', V'', hx', hi'⟩ := hΨ.isLocalStrongBundleIso_mor (ϕ.mor φ)
    obtain ⟨G, hG⟩ := hc.isScDiffeoOn_base
    obtain ⟨g', hg'⟩ := hi'.isScDiffeoOn_base
    have hU₀ : IsOpen (U ∩ ϕ.mor ⁻¹' V') :=
      hG.isOpen_source.inter (hg'.isOpen_source.preimage ϕ.continuous_mor)
    have hc₀ := hc.restrict hG hU₀ inter_subset_left
    exact ⟨U ∩ ϕ.mor ⁻¹' V', _, ⟨hx, hx'⟩, StrongBundle.IsStrongBundleIsoOn.of_comp
      (h := hΦ.isStrongBundleMap_mor) (h' := hΨ.isStrongBundleFunctor.isStrongBundleMap_mor) hc₀
      hi' fun y hy => hy.2⟩

end EpStrongBundle

end TwoOutOfThree

/-! ### The pull-back along an equivalence -/

section PullbackEquivalence

variable {ObjA MorA : Type u} [TopologicalSpace ObjA] [T2Space ObjA] [ParacompactSpace ObjA]
  [TopologicalSpace MorA] [T2Space MorA] [ParacompactSpace MorA] {A : EpGroupoid ObjA MorA}
  {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

namespace EpStrongBundle

variable (B) in
open scoped Classical in
/-- `w ↦ (τ(P w)⁻¹, w) ∈ 𝐗 ₛ×_P W` at level `[1]`, for a local section `τ` of `t` on `V` (junk
value `(1_{P w}, w)` off `V`). -/
def invPairOne (τ : Obj → Mor) (V : Set Obj) (hτ : ∀ x ∈ V, X.tgt (τ x) = x) (w : B.One) :
    (B.pullback X.isScSmoothMap_src).One :=
  if h : P (B.oneVal w) ∈ V then
    (B.pullback X.isScSmoothMap_src).oneMk ⟨(X.inv (τ (P (B.oneVal w))), B.oneVal w),
      show P (B.oneVal w) = X.src (X.inv (τ (P (B.oneVal w)))) by rw [X.src_inv, hτ _ h]⟩
      ((B.mem_oneSet_pullback_iff _ _).2 (B.oneVal_mem w))
  else (B.pullback X.isScSmoothMap_src).oneMk (X.unitPair (B.oneVal w))
    ((B.mem_oneSet_pullback_iff _ _).2 (B.oneVal_mem w))

theorem invPairOne_val {τ : Obj → Mor} {V : Set Obj} (hτ : ∀ x ∈ V, X.tgt (τ x) = x)
    {w : B.One} (hw : P (B.oneVal w) ∈ V) :
    ((B.pullback X.isScSmoothMap_src).oneVal (invPairOne B τ V hτ w) : Mor × W) =
      (X.inv (τ (P (B.oneVal w))), B.oneVal w) := by
  unfold invPairOne; rw [dif_pos hw]; rfl

theorem isScSmoothOn_invPairOne {τ : Obj → Mor} {V : Set Obj} (hτ : ∀ x ∈ V, X.tgt (τ x) = x)
    (hτs : X.PObj.IsScSmoothOn X.PMor τ V) :
    B.toMPolyfold1.IsScSmoothOn (B.pullback X.isScSmoothMap_src).toMPolyfold1
      (invPairOne B τ V hτ) ((P ∘ B.oneVal) ⁻¹' V) := by
  have hVo : IsOpen ((P ∘ B.oneVal) ⁻¹' V) :=
    hτs.isOpen.preimage (B.continuous.comp B.continuous_oneVal)
  refine B.isScSmoothOn_to_pullback_one X.isScSmoothMap_src ?_ ?_
  · refine (MPolyfold.IsScSmoothOn.comp (g := X.inv) X.isScSmoothMap_inv
      (MPolyfold.IsScSmoothOn.comp hτs (B.isScSmoothMap_proj1.mono hVo (subset_univ _))
        fun _ h => h) (mapsTo_univ _ _)).congr fun w hw => ?_
    change X.inv (τ (P (B.oneVal w))) =
      (((B.pullback X.isScSmoothMap_src).oneVal (invPairOne B τ V hτ w) : Mor × W)).1
    rw [invPairOne_val hτ hw]
  · refine (MPolyfold.isScSmoothMap_id.mono hVo (subset_univ _)).congr fun w hw =>
      B.oneVal_injective ?_
    change B.oneVal w =
      (((B.pullback X.isScSmoothMap_src).oneVal (invPairOne B τ V hτ w) : Mor × W)).2
    rw [invPairOne_val hτ hw]

variable (E : EpStrongBundle X B) (π : EpFunctor A X)
  [ParacompactSpace (pullbackSpace P π.obj)]
  [ParacompactSpace (pullbackSpace (pullbackProj P π.obj) A.src)]

/-- The source of a morphism with target in `W_{0,1}` lies in `W_{0,1}`. -/
theorem mem_oneSet_of_mor (ψ : pullbackSpace P X.src) (h : E.μ ψ ∈ B.oneSet) :
    (ψ : Mor × W).2 ∈ B.oneSet := by
  rw [← E.μ_morInv ψ]
  exact E.isStrongBundleMap.mapsTo_oneSet ((B.mem_oneSet_pullback_iff X.isScSmoothMap_src _).2 h)

open scoped Classical in
/-- The local lift `w ↦ (g(s(τ(P w))), μ(τ(P w)⁻¹, w)) ∈ π*W[1]` used for the openness of
`|Π[1]|` (junk value `q₀`). -/
def pbOneLift (τ : Obj → Mor) (V : Set Obj) (hτ : ∀ x ∈ V, X.tgt (τ x) = x) (g : Obj → ObjA)
    (Va : Set Obj) (hg : ∀ x ∈ Va, π.obj (g x) = x) (q₀ : (B.pullback π.isScSmoothMap_obj).One)
    (w : B.One) : (B.pullback π.isScSmoothMap_obj).One :=
  if h : P (B.oneVal w) ∈ V ∩ (X.src ∘ τ) ⁻¹' Va then
    (B.pullback π.isScSmoothMap_obj).oneMk
      ⟨(g (X.src (τ (P (B.oneVal w)))),
        E.μ ((B.pullback X.isScSmoothMap_src).oneVal (invPairOne B τ V hτ w))), by
        change P (E.μ _) = π.obj (g (X.src (τ (P (B.oneVal w)))))
        rw [E.P_μ, invPairOne_val hτ h.1, X.tgt_inv]; exact (hg _ h.2).symm⟩
      ((B.mem_oneSet_pullback_iff π.isScSmoothMap_obj _).2
        (E.isStrongBundleMap.mapsTo_oneSet ((B.pullback X.isScSmoothMap_src).oneVal_mem _)))
  else q₀

omit [ParacompactSpace (pullbackSpace (pullbackProj P π.obj) A.src)] in
theorem pbOneLift_val {τ : Obj → Mor} {V : Set Obj} (hτ : ∀ x ∈ V, X.tgt (τ x) = x)
    {g : Obj → ObjA} {Va : Set Obj} (hg : ∀ x ∈ Va, π.obj (g x) = x)
    (q₀ : (B.pullback π.isScSmoothMap_obj).One) {w : B.One}
    (hw : P (B.oneVal w) ∈ V ∩ (X.src ∘ τ) ⁻¹' Va) :
    ((B.pullback π.isScSmoothMap_obj).oneVal (E.pbOneLift π τ V hτ g Va hg q₀ w) : ObjA × W) =
      (g (X.src (τ (P (B.oneVal w)))),
        E.μ ((B.pullback X.isScSmoothMap_src).oneVal (invPairOne B τ V hτ w))) := by
  unfold pbOneLift; rw [dif_pos hw]; rfl

omit [ParacompactSpace (pullbackSpace (pullbackProj P π.obj) A.src)] in
theorem isScSmoothOn_pbOneLift {τ : Obj → Mor} {V : Set Obj} (hτ : ∀ x ∈ V, X.tgt (τ x) = x)
    (hτs : X.PObj.IsScSmoothOn X.PMor τ V) {g : Obj → ObjA} {Va : Set Obj}
    (hg : ∀ x ∈ Va, π.obj (g x) = x) (hgs : X.PObj.IsScSmoothOn A.PObj g Va)
    (q₀ : (B.pullback π.isScSmoothMap_obj).One) :
    B.toMPolyfold1.IsScSmoothOn (B.pullback π.isScSmoothMap_obj).toMPolyfold1
      (E.pbOneLift π τ V hτ g Va hg q₀) ((P ∘ B.oneVal) ⁻¹' (V ∩ (X.src ∘ τ) ⁻¹' Va)) := by
  have hsτ : X.PObj.IsScSmoothOn X.PObj (X.src ∘ τ) V :=
    MPolyfold.IsScSmoothOn.comp (g := X.src) X.isScSmoothMap_src hτs (mapsTo_univ _ _)
  have hN₀ : IsOpen (V ∩ (X.src ∘ τ) ⁻¹' Va) :=
    hsτ.continuousOn.isOpen_inter_preimage hτs.isOpen hgs.isOpen
  have hc1 : Continuous (P ∘ B.oneVal) := B.continuous.comp B.continuous_oneVal
  have hN : IsOpen ((P ∘ B.oneVal) ⁻¹' (V ∩ (X.src ∘ τ) ⁻¹' Va)) := hN₀.preimage hc1
  refine B.isScSmoothOn_to_pullback_one π.isScSmoothMap_obj ?_ ?_
  · have h1 : X.PObj.IsScSmoothOn X.PObj (X.src ∘ τ) (V ∩ (X.src ∘ τ) ⁻¹' Va) :=
      hsτ.mono hN₀ inter_subset_left
    have h2 : X.PObj.IsScSmoothOn A.PObj (g ∘ (X.src ∘ τ)) (V ∩ (X.src ∘ τ) ⁻¹' Va) :=
      MPolyfold.IsScSmoothOn.comp hgs h1 fun _ h => h.2
    refine (MPolyfold.IsScSmoothOn.comp h2 (B.isScSmoothMap_proj1.mono hN (subset_univ _))
      fun _ h => h).congr fun w hw => ?_
    change g (X.src (τ (P (B.oneVal w)))) =
      (((B.pullback π.isScSmoothMap_obj).oneVal (E.pbOneLift π τ V hτ g Va hg q₀ w) :
        ObjA × W)).1
    rw [E.pbOneLift_val π hτ hg q₀ hw]
  · have h3 := (isScSmoothOn_invPairOne (B := B) hτ hτs).mono hN
      (preimage_mono inter_subset_left)
    refine (MPolyfold.IsScSmoothOn.comp E.isStrongBundleMap.isScSmoothMap_one h3
      (mapsTo_univ _ _)).congr fun w hw => B.oneVal_injective ?_
    change E.μ ((B.pullback X.isScSmoothMap_src).oneVal (invPairOne B τ V hτ w)) =
      (((B.pullback π.isScSmoothMap_obj).oneVal (E.pbOneLift π τ V hτ g Va hg q₀ w) :
        ObjA × W)).2
    rw [E.pbOneLift_val π hτ hg q₀ hw]

variable {π}

/-- `Π : (π*W, π*𝐖) → (W, 𝐖)` is full if `π` is. -/
theorem full_pullbackProjFunctor (hπ : π.IsEquivalence) :
    (E.pullbackProjFunctor π).toFunctor.Full := by
  refine (GroupoidFunctor.full_iff _).2 fun q q' ψ hs ht => ?_
  have hs' : (ψ : Mor × W).2 = (q : ObjA × W).2 := hs
  have ht' : E.μ ψ = (q' : ObjA × W).2 := ht
  have h1 : X.src (ψ : Mor × W).1 = π.obj (q : ObjA × W).1 := by
    rw [← (ψ.2 : P (ψ : Mor × W).2 = X.src (ψ : Mor × W).1), hs']; exact q.2
  have h2 : X.tgt (ψ : Mor × W).1 = π.obj (q' : ObjA × W).1 := by
    rw [← E.P_μ, ht']; exact q'.2
  obtain ⟨a, ha, ha', hπa⟩ := hπ.exists_mor_eq h1 h2
  refine ⟨⟨(a, q), ha.symm⟩, rfl, ?_, ?_⟩
  · apply Subtype.ext
    exact Prod.ext ha' ((E.μ_congr (Prod.ext hπa hs'.symm)).trans ht')
  · exact Subtype.ext (Prod.ext hπa hs'.symm)

/-- `Π` is faithful if `π` is. -/
theorem faithful_pullbackProjFunctor (hπ : π.IsEquivalence) :
    (E.pullbackProjFunctor π).toFunctor.Faithful := by
  refine (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs ht he => ?_
  have hs' : (φ : MorA × pullbackSpace P π.obj).2 = (φ' : MorA × pullbackSpace P π.obj).2 := hs
  have h1 : A.src (φ : MorA × pullbackSpace P π.obj).1 =
      A.src (φ' : MorA × pullbackSpace P π.obj).1 := by
    rw [← (φ.2 : pullbackProj P π.obj (φ : MorA × pullbackSpace P π.obj).2 =
      A.src (φ : MorA × pullbackSpace P π.obj).1), ← (φ'.2 : pullbackProj P π.obj
      (φ' : MorA × pullbackSpace P π.obj).2 = A.src (φ' : MorA × pullbackSpace P π.obj).1), hs']
  have h2 : A.tgt (φ : MorA × pullbackSpace P π.obj).1 =
      A.tgt (φ' : MorA × pullbackSpace P π.obj).1 :=
    congrArg (fun q : pullbackSpace P π.obj => (q : ObjA × W).1) ht
  have h3 : π.mor (φ : MorA × pullbackSpace P π.obj).1 =
      π.mor (φ' : MorA × pullbackSpace P π.obj).1 :=
    congrArg (fun q : pullbackSpace P X.src => (q : Mor × W).1) he
  exact Subtype.ext (Prod.ext (hπ.mor_injective h1 h2 h3) hs')

/-- `Π` is essentially surjective if `π` is: `w ≅ (a, μ(σ⁻¹, w))` for `σ : π(a) → P(w)`. -/
theorem essSurj_pullbackProjFunctor (hπ : π.IsEquivalence) :
    (E.pullbackProjFunctor π).toFunctor.EssSurj := by
  refine (GroupoidFunctor.essSurj_iff _).2 fun w => ?_
  obtain ⟨a, σ, hs, ht⟩ := hπ.exists_iso (P w)
  have h1 : P w = X.src (X.inv σ) := by rw [X.src_inv, ht]
  have h2 : P (E.μ ⟨(X.inv σ, w), h1⟩) = π.obj a := by rw [E.P_μ, X.tgt_inv, hs]
  refine ⟨⟨(a, E.μ ⟨(X.inv σ, w), h1⟩), h2⟩, ⟨(σ, E.μ ⟨(X.inv σ, w), h1⟩), h2.trans hs.symm⟩,
    rfl, ?_⟩
  exact E.μ_μ_inv σ w h1 _

/-- **`Π : (π*W, π*𝐖) → (W, 𝐖)` is an equivalence of ep-groupoids** if `π` is (Lemma 10.1.2). -/
theorem isEquivalence_pullbackProjFunctor (hπ : π.IsEquivalence) :
    (E.pullbackProjFunctor π).IsEquivalence :=
  (E.pullbackProjFunctor π).lemma_10_1_2
    { faithful := E.faithful_pullbackProjFunctor hπ
      full := E.full_pullbackProjFunctor hπ
      essSurj := E.essSurj_pullbackProjFunctor hπ }
    (B.isLocalScDiffeo_pullbackProj' π.isScSmoothMap_obj hπ.isLocalScDiffeo_obj)

/-- `|Π[1]|` is injective. -/
theorem injective_oneOrbitMap_pullbackProjFunctor (hπ : π.IsEquivalence) :
    Injective ((E.pullbackAlong π).oneOrbitMap E (E.pullbackProjFunctor π)
      (E.isStrongBundleFunctor_pullbackProjFunctor π).isStrongBundleMap_obj.mapsTo_oneSet) := by
  intro c c' h
  induction c using Quotient.inductionOn with | h q => ?_
  induction c' using Quotient.inductionOn with | h q' => ?_
  rw [oneOrbitMap_mk, oneOrbitMap_mk] at h
  obtain ⟨ψ, hs, ht⟩ := Quotient.exact h
  obtain ⟨φ, hφs, hφt, -⟩ :=
    (GroupoidFunctor.full_iff _).1 (E.full_pullbackProjFunctor hπ) _ _ ψ hs ht
  exact Quotient.sound ⟨φ, hφs, hφt⟩

/-- `|Π[1]|` is surjective. -/
theorem surjective_oneOrbitMap_pullbackProjFunctor (hπ : π.IsEquivalence) :
    Surjective ((E.pullbackAlong π).oneOrbitMap E (E.pullbackProjFunctor π)
      (E.isStrongBundleFunctor_pullbackProjFunctor π).isStrongBundleMap_obj.mapsTo_oneSet) := by
  intro c
  induction c using Quotient.inductionOn with | h w => ?_
  obtain ⟨q, ψ, hs, ht⟩ :=
    (GroupoidFunctor.essSurj_iff _).1 (E.essSurj_pullbackProjFunctor hπ) (B.oneVal w)
  have hs' : (ψ : Mor × W).2 = (q : ObjA × W).2 := hs
  have ht' : E.μ ψ = B.oneVal w := ht
  have hq : q ∈ (B.pullback π.isScSmoothMap_obj).oneSet :=
    (B.mem_oneSet_pullback_iff _ q).2 (hs' ▸ E.mem_oneSet_of_mor ψ (ht' ▸ B.oneVal_mem w))
  refine ⟨Quotient.mk _ ((B.pullback π.isScSmoothMap_obj).oneMk q hq), ?_⟩
  rw [oneOrbitMap_mk]
  exact Quotient.sound ⟨ψ, hs, ht⟩

/-- **`|Π[1]|` is open**: near `w ≅ Π(q)` (by `ψ`), with a local section `τ` of `t` at `ψ` and a
local inverse `g` of `π` at `q`, `w₁ ↦ (g(s(τ(P w₁))), μ(τ(P w₁)⁻¹, w₁))` is a continuous local
lift through `q` of the orbit map. -/
theorem isOpenMap_oneOrbitMap_pullbackProjFunctor (hπ : π.IsEquivalence) :
    IsOpenMap ((E.pullbackAlong π).oneOrbitMap E (E.pullbackProjFunctor π)
      (E.isStrongBundleFunctor_pullbackProjFunctor π).isStrongBundleMap_obj.mapsTo_oneSet) := by
  intro O hO
  have hÕ : IsOpen ((Quotient.mk _ : (B.pullback π.isScSmoothMap_obj).One →
      (E.pullbackAlong π).OneOrbitSpace) ⁻¹' O) := hO.preimage continuous_quot_mk
  refine isQuotientMap_quotient_mk'.isOpen_preimage.1 ?_
  rw [isOpen_iff_forall_mem_open]
  rintro w ⟨c, hcO, hc⟩
  induction c using Quotient.inductionOn with | h q => ?_
  rw [oneOrbitMap_mk] at hc
  obtain ⟨ψ, hψs, hψt⟩ := Quotient.exact hc
  have hψs' : (ψ : Mor × W).2 = ((B.pullback π.isScSmoothMap_obj).oneVal q : ObjA × W).2 := hψs
  have hψt' : E.μ ψ = B.oneVal w := hψt
  obtain ⟨Ut, Vt, τ, hψU, hτ⟩ := X.isLocalScDiffeo_tgt (ψ : Mor × W).1
  obtain ⟨Ua, Va, g, haU, hg⟩ :=
    hπ.isLocalScDiffeo_obj ((B.pullback π.isScSmoothMap_obj).oneVal q : ObjA × W).1
  have hsτ : X.PObj.IsScSmoothOn X.PObj (X.src ∘ τ) Vt :=
    MPolyfold.IsScSmoothOn.comp (g := X.src) X.isScSmoothMap_src hτ.isScSmoothOn_inv
      (mapsTo_univ _ _)
  have hN₀ : IsOpen (Vt ∩ (X.src ∘ τ) ⁻¹' Va) :=
    hsτ.continuousOn.isOpen_inter_preimage hτ.isOpen_target hg.isOpen_target
  have hc1 : Continuous (P ∘ B.oneVal) := B.continuous.comp B.continuous_oneVal
  have hN : IsOpen ((P ∘ B.oneVal) ⁻¹' (Vt ∩ (X.src ∘ τ) ⁻¹' Va)) := hN₀.preimage hc1
  have hFs := E.isScSmoothOn_pbOneLift π hτ.right_inv hτ.isScSmoothOn_inv hg.right_inv
    hg.isScSmoothOn_inv q
  have hPw : P (B.oneVal w) = X.tgt (ψ : Mor × W).1 := by rw [← hψt', E.P_μ]
  have hτw : τ (P (B.oneVal w)) = (ψ : Mor × W).1 := by rw [hPw]; exact hτ.left_inv _ hψU
  have hsψ : X.src (ψ : Mor × W).1 =
      π.obj ((B.pullback π.isScSmoothMap_obj).oneVal q : ObjA × W).1 := by
    rw [← (ψ.2 : P (ψ : Mor × W).2 = X.src (ψ : Mor × W).1), hψs']
    exact ((B.pullback π.isScSmoothMap_obj).oneVal q).2
  have hwN : P (B.oneVal w) ∈ Vt ∩ (X.src ∘ τ) ⁻¹' Va := by
    refine ⟨hPw ▸ hτ.mapsTo hψU, ?_⟩
    change X.src (τ (P (B.oneVal w))) ∈ Va
    rw [hτw, hsψ]; exact hg.mapsTo haU
  have hFw : E.pbOneLift π τ Vt hτ.right_inv g Va hg.right_inv q w = q := by
    apply (B.pullback π.isScSmoothMap_obj).oneVal_injective
    apply Subtype.ext
    rw [E.pbOneLift_val π hτ.right_inv hg.right_inv q hwN]
    refine Prod.ext ?_ ?_
    · change g (X.src (τ (P (B.oneVal w)))) = _
      rw [hτw, hsψ]; exact hg.left_inv _ haU
    · change E.μ _ = _
      have e1 := invPairOne_val (B := B) hτ.right_inv hwN.1
      rw [hτw, ← hψt'] at e1
      exact (E.μ_congr (q' := E.morInv ψ) e1).trans ((E.μ_morInv ψ).trans hψs')
  refine ⟨(P ∘ B.oneVal) ⁻¹' (Vt ∩ (X.src ∘ τ) ⁻¹' Va) ∩
      E.pbOneLift π τ Vt hτ.right_inv g Va hg.right_inv q ⁻¹'
        ((Quotient.mk _ : (B.pullback π.isScSmoothMap_obj).One →
          (E.pullbackAlong π).OneOrbitSpace) ⁻¹' O), ?_,
    hFs.continuousOn.isOpen_inter_preimage hN hÕ, hwN, ?_⟩
  · rintro w₁ ⟨hw₁N, hw₁O⟩
    refine ⟨Quotient.mk _ (E.pbOneLift π τ Vt hτ.right_inv g Va hg.right_inv q w₁), hw₁O, ?_⟩
    rw [oneOrbitMap_mk]
    have e1 := invPairOne_val (B := B) hτ.right_inv hw₁N.1
    have hm : P (E.μ ((B.pullback X.isScSmoothMap_src).oneVal (invPairOne B τ Vt hτ.right_inv
        w₁))) = X.src (τ (P (B.oneVal w₁))) := by
      rw [E.P_μ, e1, X.tgt_inv]
    refine Quotient.sound ⟨⟨(τ (P (B.oneVal w₁)), E.μ ((B.pullback X.isScSmoothMap_src).oneVal
      (invPairOne B τ Vt hτ.right_inv w₁))), hm⟩, ?_, ?_⟩
    · change E.μ _ = (((B.pullback π.isScSmoothMap_obj).oneVal _ : ObjA × W)).2
      rw [E.pbOneLift_val π hτ.right_inv hg.right_inv q hw₁N]
    · change E.μ _ = B.oneVal w₁
      have hm' : P (B.oneVal w₁) = X.src (X.inv (τ (P (B.oneVal w₁)))) := by
        rw [X.src_inv]; exact (hτ.right_inv _ hw₁N.1).symm
      have e2 : E.μ ((B.pullback X.isScSmoothMap_src).oneVal (invPairOne B τ Vt hτ.right_inv w₁))
          = E.μ ⟨(X.inv (τ (P (B.oneVal w₁))), B.oneVal w₁), hm'⟩ := E.μ_congr e1
      have e3 : E.μ ⟨(τ (P (B.oneVal w₁)), E.μ ((B.pullback X.isScSmoothMap_src).oneVal
          (invPairOne B τ Vt hτ.right_inv w₁))), hm⟩ = E.μ ⟨(τ (P (B.oneVal w₁)),
          E.μ ⟨(X.inv (τ (P (B.oneVal w₁))), B.oneVal w₁), hm'⟩), by rw [← e2]; exact hm⟩ :=
        E.μ_congr (Prod.ext rfl e2)
      exact e3.trans (E.μ_μ_inv _ _ _ _)
  · rw [mem_preimage, hFw]; exact hcO

/-- **The pull-back along an equivalence: `Π : π*W → W` is a strong bundle equivalence**
(Definition 10.4.1) covering `π`, if `π` is an equivalence. -/
theorem isStrongBundleEquivalence_pullbackProjFunctor (hπ : π.IsEquivalence) :
    (E.pullbackAlong π).IsStrongBundleEquivalence E π (E.pullbackProjFunctor π) where
  isStrongBundleFunctor := E.isStrongBundleFunctor_pullbackProjFunctor π
  isEquivalence_base := hπ
  isEquivalence := E.isEquivalence_pullbackProjFunctor hπ
  isHomeomorph_oneOrbitMap :=
    ⟨continuous_oneOrbitMap (continuousOn_univ.1
      (E.isStrongBundleFunctor_pullbackProjFunctor
          π).isStrongBundleMap_obj.isScSmoothMap_one.continuousOn),
      E.isOpenMap_oneOrbitMap_pullbackProjFunctor hπ,
      E.injective_oneOrbitMap_pullbackProjFunctor hπ,
      E.surjective_oneOrbitMap_pullbackProjFunctor hπ⟩
  isLocalStrongBundleIso_obj a := by
    obtain ⟨U, V, σ, ha, hd⟩ := hπ.isLocalScDiffeo_obj a
    exact ⟨U, V, ha, B.isStrongBundleIsoOn_pullbackProj' π.isScSmoothMap_obj hd a⟩
  isLocalStrongBundleIso_mor m := by
    obtain ⟨U₃, V₃, σ₃, hm₃, hd₃⟩ := A.isLocalScDiffeo_src m
    obtain ⟨U₂, V₂, σ₂, hm₂, hd₂⟩ := hπ.isLocalScDiffeo_obj (A.src m)
    obtain ⟨U₁, V₁, σ₁, hm₁, hd₁⟩ := X.isLocalScDiffeo_src (π.mor m)
    have i₃ := (B.pullback π.isScSmoothMap_obj).isStrongBundleIsoOn_pullbackProj'
      A.isScSmoothMap_src hd₃ m
    have i₂ := B.isStrongBundleIsoOn_pullbackProj' π.isScSmoothMap_obj hd₂ (A.src m)
    have i₁ := B.isStrongBundleIsoOn_pullbackProj' X.isScSmoothMap_src hd₁ (π.mor m)
    obtain ⟨U₀, U₀'', hm₀, i₀⟩ := i₂.exists_comp i₃ hm₃ hm₂
    have i₀' := i₀.of_eq (show π.obj ∘ A.src = X.src ∘ π.mor from
      funext fun m => (π.src_mor m).symm)
    obtain ⟨G, hG⟩ := i₀'.isScDiffeoOn_base
    have hU₄ : IsOpen (U₀ ∩ π.mor ⁻¹' U₁) :=
      hG.isOpen_source.inter (hd₁.isOpen_source.preimage π.continuous_mor)
    have i₄ := i₀'.restrict hG hU₄ inter_subset_left
    exact ⟨U₀ ∩ π.mor ⁻¹' U₁, _, ⟨hm₀, hm₁⟩, StrongBundle.IsStrongBundleIsoOn.of_comp
      (h := (E.isStrongBundleFunctor_pullbackProjFunctor π).isStrongBundleMap_mor)
      (h' := B.isStrongBundleMap_pullbackProj' X.isScSmoothMap_src) i₄ i₁ fun _ hy => hy.2⟩

end EpStrongBundle

end PullbackEquivalence

/-! ### Transport along a natural transformation; the fibrewise inverse of an equivalence -/

section TransportInverse

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
  {ObjC MorC : Type u} [TopologicalSpace ObjC] [T2Space ObjC] [ParacompactSpace ObjC]
  [TopologicalSpace MorC] [T2Space MorC] [ParacompactSpace MorC] {Y : EpGroupoid ObjC MorC}
  {WC : Type u} [TopologicalSpace WC] [T2Space WC] [ParacompactSpace WC] {PC : WC → ObjC}
  [∀ x, AddCommGroup (PC ⁻¹' {x})] [∀ x, Module ℝ (PC ⁻¹' {x})] {BC : StrongBundle Y.PObj PC}
  [ParacompactSpace (pullbackSpace PC Y.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {C : EpStrongBundle Y BC}

namespace EpStrongBundle

section Transport

variable {ψ ϕ : EpFunctor X X'} {Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}

theorem transportPair_mem (hΨ : E.IsStrongBundleFunctor E' ψ Ψ) (τ : EpNatTrans ψ ϕ) (w : W) : P'
    (Ψ.obj w) = X'.src (τ.app (P w)) := by
  rw [hΨ.isStrongBundleMap_obj.covers, τ.src_app]

/-- `w ↦ (τ(P w), Ψ(w)) ∈ 𝐗' ₛ×_{P'} W'`. -/
def transportPair (hΨ : E.IsStrongBundleFunctor E' ψ Ψ) (τ : EpNatTrans ψ ϕ) :
    W → pullbackSpace P' X'.src :=
  pullbackPair P' X'.src (τ.app ∘ P) Ψ.obj (transportPair_mem hΨ τ)

/-- **Transport of a strong bundle functor `Ψ` covering `ψ` along `τ : ψ → ϕ`**:
`Θ(w) = μ'(τ(P w), Ψ(w))`. -/
def transportMap (hΨ : E.IsStrongBundleFunctor E' ψ Ψ) (τ : EpNatTrans ψ ϕ) : W → W' :=
  E'.μ ∘ transportPair hΨ τ

theorem isStrongBundleMap_transportPair (hΨ : E.IsStrongBundleFunctor E' ψ Ψ)
    (τ : EpNatTrans ψ ϕ) :
    B.IsStrongBundleMap (B'.pullback X'.isScSmoothMap_src) τ.app (transportPair hΨ τ) :=
  B'.isStrongBundleMap_pullbackPair X'.isScSmoothMap_src τ.isScSmoothMap_app
    (hΨ.isStrongBundleMap_obj.congr_base (funext fun x => (τ.src_app x).symm))

/-- **The transported map covers `ϕ`** (Definition 8.5): `Θ(μ(γ, w)) = μ'(ϕ(γ), Θ(w))`, by the
naturality `τ(t γ) ∘ ψ(γ) = ϕ(γ) ∘ τ(s γ)` and Definition 8.3.1 (3). -/
theorem isMap_transportMap (hΨ : E.IsStrongBundleFunctor E' ψ Ψ) (τ : EpNatTrans ψ ϕ) :
    E.IsMap E' ϕ (transportMap hΨ τ) where
  isStrongBundleMap := (E'.isStrongBundleMap.comp (isStrongBundleMap_transportPair hΨ τ)).congr_base
    (funext τ.tgt_app)
  map_μ γ w hw := by
    have hP : P w = X.src γ := hw
    have e1 := hΨ.isMap.map_μ γ w hw
    have h1 : P' (Ψ.obj w) = X'.src (ψ.mor γ) := by
      rw [hΨ.isStrongBundleMap_obj.covers, hP, ψ.src_mor]
    have h2 : X'.src (τ.app (X.tgt γ)) = X'.tgt (ψ.mor γ) := by rw [τ.src_app, ψ.tgt_mor]
    have h3 : P' (Ψ.obj w) = X'.src (τ.app (X.src γ)) := by
      rw [hΨ.isStrongBundleMap_obj.covers, hP, τ.src_app]
    have h4 : X'.src (ϕ.mor γ) = X'.tgt (τ.app (X.src γ)) := by rw [ϕ.src_mor, τ.tgt_app]
    have s1 : transportMap hΨ τ (E.μ ⟨(γ, w), hw⟩) = E'.μ ⟨(τ.app (X.tgt γ),
        E'.μ ⟨(ψ.mor γ, Ψ.obj w), h1⟩), by
        change P' (E'.μ _) = _; rw [E'.P_μ]; exact h2.symm⟩ :=
      E'.μ_congr (Prod.ext (by change τ.app (P (E.μ _)) = _; rw [E.P_μ]) e1)
    have s2 := E'.μ_comp (τ.app (X.tgt γ)) (ψ.mor γ) (Ψ.obj w) h1 h2
    have s3 : E'.μ ⟨(X'.comp (τ.app (X.tgt γ)) (ψ.mor γ), Ψ.obj w),
        h1.trans (X'.src_comp _ _ h2).symm⟩ = E'.μ ⟨(X'.comp (ϕ.mor γ) (τ.app (X.src γ)),
        Ψ.obj w), h3.trans (X'.src_comp _ _ h4).symm⟩ :=
      E'.μ_congr (Prod.ext (τ.naturality γ) rfl)
    have s4 := E'.μ_comp (ϕ.mor γ) (τ.app (X.src γ)) (Ψ.obj w) h3 h4
    refine s1.trans (s2.symm.trans (s3.trans (s4.trans (E'.μ_congr (Prod.ext rfl ?_)))))
    exact E'.μ_congr (Prod.ext (show τ.app (X.src γ) = τ.app (P w) by rw [hP]) rfl)

/-- The transported strong bundle functor `Θ` covering `ϕ`. -/
def transportFunctor (hΨ : E.IsStrongBundleFunctor E' ψ Ψ) (τ : EpNatTrans ψ ϕ) :
    EpFunctor E.toEpGroupoid E'.toEpGroupoid :=
  (isMap_transportMap hΨ τ).liftFunctor

theorem isStrongBundleFunctor_transportFunctor (hΨ : E.IsStrongBundleFunctor E' ψ Ψ)
    (τ : EpNatTrans ψ ϕ) :
    E.IsStrongBundleFunctor E' ϕ (transportFunctor hΨ τ) :=
  (isMap_transportMap hΨ τ).isStrongBundleFunctor_liftFunctor

@[simp] theorem transportFunctor_obj (hΨ : E.IsStrongBundleFunctor E' ψ Ψ)
    (τ : EpNatTrans ψ ϕ) (w : W) :
    (transportFunctor hΨ τ).obj w = E'.μ (transportPair hΨ τ w) := rfl

/-- **`Ψ ≃ Θ`**: `w ↦ (τ(P w), Ψ(w))` is a natural transformation of strong bundle functors
(Definitions 10.4.8 and 10.4.10) covering `τ`. -/
def transportNatTrans (hΨ : E.IsStrongBundleFunctor E' ψ Ψ) (τ : EpNatTrans ψ ϕ) :
    E.StrongBundleNatTrans E' ψ ϕ Ψ (transportFunctor hΨ τ) :=
  IsStrongBundleNatTransMap.toNatTrans
    ⟨fun _ => rfl, isStrongBundleMap_transportPair hΨ τ, fun _ => rfl⟩ hΨ
    (isStrongBundleFunctor_transportFunctor hΨ τ)

end Transport

section InvLift

variable {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (hΦ : E.IsStrongBundleEquivalence E' ϕ Φ) {κ : EpFunctor Y X} {Θ : WC → W'}
  (hΘ : C.IsMap E' (ϕ.comp κ) Θ)

/-- **The fibrewise inverse lift through a strong bundle equivalence**:
`Λ(c) = Φ_{κ(P c)}⁻¹(Θ(c))` for a strong bundle map `Θ` covering `ϕ ∘ κ`. -/
def invLiftMap (c : WC) : W :=
  ((hΦ.fiberEquiv (κ.obj (PC c))).symm ⟨Θ c, hΘ.isStrongBundleMap.covers c⟩ : W)

omit [ParacompactSpace (pullbackSpace PC Y.src)] in
theorem P_invLiftMap (c : WC) : P (invLiftMap hΦ hΘ c) = κ.obj (PC c) :=
  ((hΦ.fiberEquiv (κ.obj (PC c))).symm ⟨Θ c, hΘ.isStrongBundleMap.covers c⟩).2

omit [ParacompactSpace (pullbackSpace PC Y.src)] in
theorem obj_invLiftMap (c : WC) : Φ.obj (invLiftMap hΦ hΘ c) = Θ c :=
  congrArg Subtype.val ((hΦ.fiberEquiv (κ.obj (PC c))).apply_symm_apply
    ⟨Θ c, hΘ.isStrongBundleMap.covers c⟩)

omit [ParacompactSpace (pullbackSpace PC Y.src)] in
/-- `Λ(c)` is the unique `w` over `κ(P c)` with `Φ(w) = Θ(c)`. -/
theorem invLiftMap_eq {c : WC} {w : W} (hw : P w = κ.obj (PC c)) (he : Φ.obj w = Θ c) :
    invLiftMap hΦ hΘ c = w :=
  hΦ.eq_of_obj_eq ((P_invLiftMap hΦ hΘ c).trans hw.symm) ((obj_invLiftMap hΦ hΘ c).trans he.symm)

omit [ParacompactSpace (pullbackSpace PC Y.src)] in
/-- Near `c`, `Λ = Ψ ∘ Θ` for the inverse `Ψ` of a local strong bundle isomorphism of `Φ`. -/
theorem invLiftMap_eq_of_isoOn {U : Set Obj} {U' : Set Obj'}
    (hi : B.IsStrongBundleIsoOn B' hΦ.isStrongBundleFunctor.isStrongBundleMap_obj U U')
    {Ψi : W' → W}
    (hΨi : B.toMPolyfold0.IsScDiffeoOn B'.toMPolyfold0 Φ.obj Ψi (P ⁻¹' U) (P' ⁻¹' U'))
    {c : WC} (hc : κ.obj (PC c) ∈ U) : invLiftMap hΦ hΘ c = Ψi (Θ c) := by
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  have hΘc : Θ c ∈ P' ⁻¹' U' := by
    change P' (Θ c) ∈ U'; rw [hΘ.isStrongBundleMap.covers]; exact hg.mapsTo hc
  refine (invLiftMap_eq hΦ hΘ ?_ (hΨi.right_inv _ hΘc)).symm ▸ rfl
  refine hg.injOn (hΨi.mapsTo_inv hΘc) hc ?_
  rw [← hΦ.covers, hΨi.right_inv _ hΘc]
  exact hΘ.isStrongBundleMap.covers c

omit [ParacompactSpace (pullbackSpace PC Y.src)] in
theorem mapsTo_oneSet_invLiftMap : MapsTo (invLiftMap hΦ hΘ) BC.oneSet B.oneSet := by
  intro c hc
  obtain ⟨U, U', hx, hi⟩ := hΦ.isLocalStrongBundleIso_obj (κ.obj (PC c))
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
  have h1 := hΘ.isStrongBundleMap.mapsTo_oneSet hc
  have hv1 : B'.oneMk _ h1 ∈ (P' ∘ B'.oneVal) ⁻¹' U' := by
    change P' (Θ c) ∈ U'; rw [hΘ.isStrongBundleMap.covers]; exact hg.mapsTo hx
  have hw1 := hΨ₁.mapsTo_inv hv1
  have hA1 := congrArg B'.oneVal (hΨ₁.right_inv _ hv1)
  rw [StrongBundle.oneVal_oneRestrict] at hA1
  have hP : P (B.oneVal (Ψ₁ (B'.oneMk _ h1))) = κ.obj (PC c) := by
    refine hg.injOn hw1 hx ?_
    rw [Function.comp_apply, ← hΦ.covers, hA1]
    exact hΘ.isStrongBundleMap.covers c
  rw [invLiftMap_eq hΦ hΘ hP hA1]
  exact B.oneVal_mem _

omit [ParacompactSpace (pullbackSpace PC Y.src)] in
/-- **`Λ` is a strong bundle map covering `κ`**: linear on the fibres, sc-smooth at the levels
`[0]` and `[1]` (locally `Ψ ∘ Θ`, resp. `Ψ₁ ∘ Θ[1]`). -/
theorem isStrongBundleMap_invLiftMap : BC.IsStrongBundleMap B κ.obj (invLiftMap hΦ hΘ) where
  covers := P_invLiftMap hΦ hΘ
  fiber_linear y := by
    let L : PC ⁻¹' {y} →ₗ[ℝ] P ⁻¹' {κ.obj y} :=
      ((hΦ.fiberEquiv (κ.obj y)).symm.toLinearMap).comp (hΘ.isStrongBundleMap.fiber_linear y).mk'
    have hL : fiberRestrict PC P κ.obj (invLiftMap hΦ hΘ) (P_invLiftMap hΦ hΘ) y = L := by
      funext v
      apply Subtype.ext
      have hv : PC (v : WC) = y := v.2
      refine invLiftMap_eq hΦ hΘ ?_ ?_
      · rw [hv]; exact ((hΦ.fiberEquiv (κ.obj y)).symm _).2
      · exact congrArg Subtype.val ((hΦ.fiberEquiv (κ.obj y)).apply_symm_apply _)
    rw [hL]; exact L.isLinear
  isScSmoothMap := by
    refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun c _ => ?_
    obtain ⟨U, U', hx, hi⟩ := hΦ.isLocalStrongBundleIso_obj (κ.obj (PC c))
    obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
    obtain ⟨Ψi, hΨi⟩ := hi.isScDiffeoOn_zero
    have hO : IsOpen ((κ.obj ∘ PC) ⁻¹' U) :=
      hg.isOpen_source.preimage (κ.continuous_obj'.comp BC.continuous)
    have hmaps : MapsTo Θ ((κ.obj ∘ PC) ⁻¹' U) (P' ⁻¹' U') := fun c' hc' => by
      change P' (Θ c') ∈ U'; rw [hΘ.isStrongBundleMap.covers]; exact hg.mapsTo hc'
    refine ⟨_, hO, hx, subset_univ _, ?_⟩
    refine (MPolyfold.IsScSmoothOn.comp hΨi.isScSmoothOn_inv
      (hΘ.isStrongBundleMap.isScSmoothMap.mono hO (subset_univ _)) hmaps).congr fun c' hc' => ?_
    exact (invLiftMap_eq_of_isoOn hΦ hΘ hi hΨi hc').symm
  mapsTo_oneSet := mapsTo_oneSet_invLiftMap hΦ hΘ
  isScSmoothMap_one := by
    refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun c1 _ => ?_
    obtain ⟨U, U', hx, hi⟩ := hΦ.isLocalStrongBundleIso_obj (κ.obj (PC (BC.oneVal c1)))
    obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
    obtain ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
    have hO : IsOpen ((κ.obj ∘ PC ∘ BC.oneVal) ⁻¹' U) :=
      hg.isOpen_source.preimage (κ.continuous_obj'.comp (BC.continuous.comp BC.continuous_oneVal))
    have hmaps : MapsTo (StrongBundle.oneRestrict BC B' Θ hΘ.isStrongBundleMap.mapsTo_oneSet)
        ((κ.obj ∘ PC ∘ BC.oneVal) ⁻¹' U) ((P' ∘ B'.oneVal) ⁻¹' U') := fun c' hc' => by
      change P' (Θ (BC.oneVal c')) ∈ U'; rw [hΘ.isStrongBundleMap.covers]; exact hg.mapsTo hc'
    refine ⟨_, hO, hx, subset_univ _, ?_⟩
    refine (MPolyfold.IsScSmoothOn.comp hΨ₁.isScSmoothOn_inv
      (hΘ.isStrongBundleMap.isScSmoothMap_one.mono hO (subset_univ _)) hmaps).congr
      fun c' hc' => ?_
    apply B.oneVal_injective
    have hA1 := congrArg B'.oneVal (hΨ₁.right_inv _ (hmaps hc'))
    rw [StrongBundle.oneVal_oneRestrict, StrongBundle.oneVal_oneRestrict] at hA1
    have hw1 := hΨ₁.mapsTo_inv (hmaps hc')
    have hP : P (B.oneVal (Ψ₁ (StrongBundle.oneRestrict BC B' Θ
        hΘ.isStrongBundleMap.mapsTo_oneSet c'))) = κ.obj (PC (BC.oneVal c')) := by
      refine hg.injOn hw1 hc' ?_
      rw [Function.comp_apply, ← hΦ.covers, hA1]
      exact hΘ.isStrongBundleMap.covers _
    rw [StrongBundle.oneVal_oneRestrict]
    exact (invLiftMap_eq hΦ hΘ hP hA1).symm

/-- **`Λ` covers `κ`** (Definition 8.5): `Φ(Λ(μ_C(γ, c))) = Θ(μ_C(γ, c)) = μ'(ϕ(κ(γ)), Θ(c)) =
Φ(μ(κ(γ), Λ(c)))`, and `Φ` is injective on the fibres. -/
theorem isMap_invLiftMap : C.IsMap E κ (invLiftMap hΦ hΘ) where
  isStrongBundleMap := isStrongBundleMap_invLiftMap hΦ hΘ
  map_μ γ c h := by
    refine invLiftMap_eq hΦ hΘ ?_ ?_
    · rw [E.P_μ, C.P_μ, κ.tgt_mor]
    · have hc : P (invLiftMap hΦ hΘ c) = X.src (κ.mor γ) := by
        rw [P_invLiftMap hΦ hΘ c, h, κ.src_mor]
      refine (hΦ.isStrongBundleFunctor.isMap.map_μ (κ.mor γ) (invLiftMap hΦ hΘ c) hc).trans ?_
      rw [hΘ.map_μ γ c h]
      exact E'.μ_congr (Prod.ext rfl (obj_invLiftMap hΦ hΘ c))

/-- The fibrewise inverse lift as a strong bundle functor `W_C → W` covering `κ`. -/
def invLiftFunctor : EpFunctor C.toEpGroupoid E.toEpGroupoid :=
  (isMap_invLiftMap hΦ hΘ).liftFunctor

theorem isStrongBundleFunctor_invLiftFunctor :
    C.IsStrongBundleFunctor E κ (invLiftFunctor hΦ hΘ) :=
  (isMap_invLiftMap hΦ hΘ).isStrongBundleFunctor_liftFunctor

/-- `Φ ∘ Λ = Θ` as functors. -/
theorem comp_invLiftFunctor : Φ.comp (invLiftFunctor hΦ hΘ) = hΘ.liftFunctor := by
  refine EpFunctor.ext (funext (obj_invLiftMap hΦ hΘ)) (funext fun q => Subtype.ext ?_)
  change (Φ.mor (liftMor κ (isMap_invLiftMap hΦ hΘ).isStrongBundleMap.covers q) : Mor' × W') = _
  rw [hΦ.isStrongBundleFunctor.mor_val]
  exact Prod.ext rfl (obj_invLiftMap hΦ hΘ _)

end InvLift

end EpStrongBundle

end TransportInverse

end Polyfold
