import Polyfold.Chapter18.LinearizationSet
import Polyfold.Chapter12.RestrictionLocalIso
import Polyfold.Chapter5.IndexAlongPathsLocal
import Polyfold.Chapter5.RestrictOpenGermData

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 18,
§18.1, **Definition 18.1.4**, p. 845: `Lin(f, α)` built from **local sc⁺-sections**, as the text
says ("a local sc⁺-section `s` defined near `q₀`"), and its further claims with no hypothesis
beyond Definition 18.1.1.  Part I: the linearization of a section sc-smooth on an open set
(§3.1 on `P|V`), and the transport of local sc⁺-sections (Definition 2.6.6 on an open set).

# `Lin(f, α)` with local sc⁺-sections

## The text, paraphrased

(Definition 18.1.4) For `α` with `f(α) = 0`, `Ψ̄ ∈ F̄(α)` and `q₀` over `α`, take a local
sc⁺-section `s` defined near `q₀` with `(f_Ψ̄ + s)(q₀) = 0` and put
`f'_s(α) e = Ψ̄(q₀)((f_Ψ̄ + s)'(q₀)(S_Ψ e))`.  `Lin(f, α)` is the set of these operators; it does
not depend on `Ψ̄`, its elements are sc-Fredholm of one index, and `φ_*` maps `Lin(f, α)` into
`Lin(f, α')` for `φ : α → α'`.

## What is formalized

Part I (`StrongBundle`):
* `MPolyfold.IsScDiffeoOn.tangentFiberCLE`: `Tϕ : T_xX ≃L T_{x'}X'` for an sc-diffeomorphism.
* `IsScPlusSectionOn B s V` (Definition 2.6.6 on the open set `V`; the form of
  `SBLocalization.IsScPlusSectionOn` for one strong bundle), `IsScPlusSectionOn.restrictOpen`
  (it is an sc⁺-section of `P|V`), `IsScSmoothSection.isScSmoothOn_sectionAdd'` (`f + s` is
  sc-smooth on `V`, Theorem 3.1.18 on `P|V`).
* `linZeroAtOn`, `linZeroLoc`: `g'(x)` for `g` sc-smooth on an open `V ∋ x`, as `(g|V)'(x)` read
  through `T_xV ≅ T_xX` and `(Y|V)_x = Y_x`; `linZeroLoc_eq_linZeroAt` (for an sc-smooth `g` it is
  Part I's `g'(x)`), `linZeroLoc_sectionAdd_index` (its index is the local index
  `IsIndexAtLocal`, Definition 6.2.1 with local sections), `LocalIso.linZeroLoc_transport`.
* `LocalIso.isScPlusSectionOn_transport`: `Φ ∘ s ∘ g` is a local sc⁺-section;
  `extendByZero`, `IsScPlusSectionOn.extendByZero`: a local section extended by `0`.

Chapter 18 (`StrongPolyfoldBundleConstruction`):
* `linOpLoc`, `linSetLocAt`, **`linSetLoc`**: `f'_s(α)` and `Lin(f, α)` with local
  sc⁺-sections, alongside `linOp`, `linSetAt`, `linSet` (global sc⁺-sections).
* `linOp_eq_linOpLoc`, `linSetAt_subset_linSetLocAt`, **`linSet_subset_linSetLoc`**: a global
  sc⁺-section is a local one on `O`, so `linSet ⊆ linSetLoc`.
* `linZeroLoc_transAct_of_eqOn`, **`exists_linZeroLoc_transAct`**: a local sc⁺-section near
  `s(a)` is carried along `a ∈ M(Ψ, Ψ')` to the local sc⁺-section `t̄ ∘ s̄⁻¹ ∘ s ∘ s ∘ t⁻¹` near
  `t(a)` (extended by `0`), with the transition law of the linearizations; no cut-off and no
  hypothesis are needed.
* `linSetLocAt_subset`, `linSetLoc_eq_linSetLocAt`, `linSetLocAt_index`,
  `exists_index_linSetLoc`, `linPush_mem_linSetLocAt`, `linPush_mem_linSetLoc`, and
  **`definition_18_1_4_local`**: the claims of Definition 18.1.4 for `linSetLoc`, with no
  hypothesis (compare `definition_18_1_4_hyp`, which assumes `HasTransportedScPlusSections`
  for `linSet`).

## Reading

We read "a local sc⁺-section `s` defined near `q₀`" as a section `s` of `K → O` that is an
sc⁺-section on an open `W ∋ q₀` (`IsScPlusSectionOn`); `f'_s(α)` uses `s` only on `W`
(`linZeroAtOn` is the linearization of `(f_Ψ̄ + s)|W`).  With local sections the transport along
a transition needs no extension of `s` from a neighbourhood to all of `O'`, which is what
`HasTransportedScPlusSections` provides for `linSet`.
-/

set_option maxSynthPendingDepth 3

open Set Function Module

noncomputable section

namespace Polyfold

universe u v

section PartI

open StrongRetr MPolyfold

namespace MPolyfold.IsScDiffeoOn

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {ϕ : X → X'} {g : X' → X} {U : Set X} {U' : Set X'}

/-- **`Tϕ : T_xX ≃L T_{x'}X'` for an sc-diffeomorphism `ϕ : U → U'`**, with inverse `Tg`. -/
def tangentFiberCLE (h : PX.IsScDiffeoOn PX' ϕ g U U') {x : PX.Level 1} {x' : PX'.Level 1}
    (hxU : PX.levelVal 1 x ∈ U) (hxx' : ϕ (PX.levelVal 1 x) = PX'.levelVal 1 x') :
    PX.tangentFiber x ≃L[ℝ] PX'.tangentFiber x' :=
  ContinuousLinearEquiv.equivOfInverse (tangentMapOnCLM h.isScSmoothOn hxU hxx')
    (tangentMapOnCLM h.isScSmoothOn_inv (hxx' ▸ h.mapsTo hxU)
      ((congrArg g hxx'.symm).trans (h.left_inv _ hxU)))
    (fun a => Subtype.ext (by
      rw [tangentMapOnCLM_apply, tangentMapOnCLM_apply]
      have ha : a.1 ∈ PX.tangentPreimage U := by
        rw [MPolyfold.mem_tangentPreimage,
          GCT.PolyfoldConstruction.levelVal_tangentProj_of_mem a.2]
        exact hxU
      have hgf : PX.IsScSmoothOn PX (g ∘ ϕ) U := h.isScSmoothOn_inv.comp h.isScSmoothOn h.mapsTo
      rw [← Function.comp_apply (f := tangentMapOn h.isScSmoothOn_inv),
        ← tangentMapOn_comp h.isScSmoothOn_inv h.isScSmoothOn h.mapsTo ha]
      exact tangentMapOn_eqOn_id hgf (fun y hy => h.left_inv y hy) ha))
    (fun b => Subtype.ext (by
      rw [tangentMapOnCLM_apply, tangentMapOnCLM_apply]
      have hb : b.1 ∈ PX'.tangentPreimage U' := by
        rw [MPolyfold.mem_tangentPreimage,
          GCT.PolyfoldConstruction.levelVal_tangentProj_of_mem b.2, ← hxx']
        exact h.mapsTo hxU
      have hfg : PX'.IsScSmoothOn PX' (ϕ ∘ g) U' :=
        h.isScSmoothOn.comp h.isScSmoothOn_inv h.mapsTo_inv
      rw [← Function.comp_apply (f := tangentMapOn h.isScSmoothOn),
        ← tangentMapOn_comp h.isScSmoothOn h.isScSmoothOn_inv h.mapsTo_inv hb]
      exact tangentMapOn_eqOn_id hfg (fun y hy => h.right_inv y hy) hb))

/-- `Tϕ` applied is the tangent map of `ϕ`. -/
theorem tangentFiberCLE_apply (h : PX.IsScDiffeoOn PX' ϕ g U U') {x : PX.Level 1}
    {x' : PX'.Level 1} (hxU : PX.levelVal 1 x ∈ U)
    (hxx' : ϕ (PX.levelVal 1 x) = PX'.levelVal 1 x') (a : PX.tangentFiber x) :
    h.tangentFiberCLE hxU hxx' a = tangentMapOnCLM h.isScSmoothOn hxU hxx' a := rfl

end MPolyfold.IsScDiffeoOn

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}

namespace StrongBundle

variable (B) in
/-- **A local sc⁺-section on the open set `V`** (2021 p. 845, "a local sc⁺-section `s` defined
near `q₀`"; Part I's sc⁺-section, Definition 2.6.6, on `V`): `P(s(y)) = y` on `V` and `s` lifts
on `V` to an sc-smooth map into `Y[1]`. -/
def IsScPlusSectionOn (s : X → Y) (V : Set X) : Prop :=
  (∀ y ∈ V, P (s y) = y) ∧ ∃ G : X → B.One, (∀ y ∈ V, B.oneVal (G y) = s y) ∧
    PX.IsScSmoothOn B.toMPolyfold1 G V

/-- An sc⁺-section is an sc⁺-section on every open set. -/
theorem IsScPlusSection.isScPlusSectionOn {s : X → Y} (hs : B.IsScPlusSection s) {V : Set X}
    (hV : IsOpen V) : B.IsScPlusSectionOn s V := by
  obtain ⟨hsec, G, hG, hGs⟩ := (B.isScPlusSection_iff s).1 hs
  exact ⟨fun y _ => hsec y, G, fun y _ => congrFun hG y, hGs.mono hV (subset_univ _)⟩

/-- A local sc⁺-section on `V` is one on every open `W ⊆ V`. -/
theorem IsScPlusSectionOn.mono {s : X → Y} {V W : Set X} (hs : B.IsScPlusSectionOn s V)
    (hW : IsOpen W) (hWV : W ⊆ V) : B.IsScPlusSectionOn s W := by
  obtain ⟨hsec, G, hG, hGs⟩ := hs
  exact ⟨fun y hy => hsec y (hWV hy), G, fun y hy => hG y (hWV hy), hGs.mono hW hWV⟩

section Restrict

variable {V : Set X} (hV : IsOpen V) [Nonempty V] [ParacompactSpace V]
  [ParacompactSpace (pullbackSpace P (Subtype.val : V → X))]

include hV in
/-- **A local sc⁺-section on `V` is an sc⁺-section of the restriction `P|V`.** -/
theorem IsScPlusSectionOn.restrictOpen {s : X → Y} (hs : B.IsScPlusSectionOn s V)
    (hsec : IsSection P s) :
    (B.restrictOpen hV).IsScPlusSection (restrictSection P V s hsec) := by
  obtain ⟨-, G, hG, hGs⟩ := hs
  refine ((B.restrictOpen hV).isScPlusSection_iff _).2 ⟨isSection_restrictSection hsec,
    (B.restrictIso hV).Ψ₁ ∘ G ∘ Subtype.val, funext fun v => ?_, ?_⟩
  · have h1 : P (B.oneVal (G v.1)) ∈ V := by rw [hG v.1 v.2, hsec]; exact v.2
    change (B.restrictOpen hV).oneVal ((B.restrictIso hV).Ψ₁ (G v.1)) = _
    rw [(B.restrictIso hV).oneVal_Ψ₁ _ h1, hG v.1 v.2]
    exact ((B.restrictSection_eqOn_restrictIso hV hsec) (mem_univ v)).symm
  · have hGv : (PX.restrictOpen hV).IsScSmoothOn B.toMPolyfold1 (G ∘ Subtype.val) univ :=
      hGs.comp (B.restrictIso hV).base.isScSmoothOn fun v _ => v.2
    refine (B.restrictIso hV).one.isScSmoothOn_inv.comp hGv fun v _ => ?_
    change P (B.oneVal (G v.1)) ∈ V
    rw [hG v.1 v.2, hsec]; exact v.2

include hV in
/-- **A section whose restriction to `P|V` is sc-smooth is sc-smooth on `V`.** -/
theorem isScSmoothOn_of_restrictOpen {g : X → Y} (hg : IsSection P g)
    (h : (B.restrictOpen hV).IsScSmoothSection (restrictSection P V g hg)) :
    PX.IsScSmoothOn B.toMPolyfold0 g V := by
  have h1 := (B.restrictIso hV).zero.isScSmoothOn.comp h.2 (fun _ _ => mem_univ _)
  have h2 := h1.comp (B.restrictIso hV).base.isScSmoothOn_inv (fun _ _ => mem_univ _)
  refine h2.congr fun y hy => ?_
  change (restrictSection P V g hg ((B.restrictIso hV).g y)).1.2 = g y
  rw [B.restrictIso_g_of_mem hV hy]
  rfl

include hV in
/-- **A section sc-smooth on `V` restricts to an sc-smooth section of `P|V`.** -/
theorem isScSmoothSection_restrictOpen_of_isScSmoothOn {g : X → Y} (hg : IsSection P g)
    (h : PX.IsScSmoothOn B.toMPolyfold0 g V) :
    (B.restrictOpen hV).IsScSmoothSection (restrictSection P V g hg) := by
  refine ⟨isSection_restrictSection hg, ?_⟩
  have h1 := h.comp (B.restrictIso hV).base.isScSmoothOn fun v _ => v.2
  have h2 := (B.restrictIso hV).zero.isScSmoothOn_inv.comp h1 fun v _ => by
    change P (g v.1) ∈ V
    rw [hg]; exact v.2
  exact h2.congr (B.restrictSection_eqOn_restrictIso hV hg).symm

include hV in
/-- **`f + s` is sc-smooth on `V`** for an sc-smooth section `f` and a local sc⁺-section `s` on
`V` (Theorem 3.1.18 on `P|V`). -/
theorem IsScSmoothSection.isScSmoothOn_sectionAdd {f s : X → Y} (hf : B.IsScSmoothSection f)
    (hs : B.IsScPlusSectionOn s V) (hsec : IsSection P s) :
    PX.IsScSmoothOn B.toMPolyfold0 (Polyfold.sectionAdd P f s) V := by
  refine isScSmoothOn_of_restrictOpen hV (hf.1.sectionAdd hsec) ?_
  rw [restrictSection_sectionAdd hf.1 hsec]
  exact (hf.restrictOpen hV).sectionAdd (hs.restrictOpen hV hsec)

/-- The level-`1` point of `V` over a level-`1` point of `X` in `V`. -/
def levelPt (x : PX.Level 1) (hxV : PX.levelVal 1 x ∈ V) : (PX.restrictOpen hV).Level 1 :=
  (PX.restrictOpen hV).levelMk 1 ⟨_, hxV⟩
    ((MPolyfold.mem_levelSet_restrictOpen_iff hV _ 1).2 (PX.levelVal_mem x))

variable (B) in
/-- **The linearization at a zero of a section sc-smooth on `V`** (2021 §3.1 for the
restriction `P|V`): `g'(x) : T_xX → Y_x` is `(g|V)'(x)` read through `T_xV ≅ T_xX` and
`(Y|V)_x = Y_x`. -/
def linZeroAtOn {g : X → Y} (hg : IsSection P g) (hgV : PX.IsScSmoothOn B.toMPolyfold0 g V)
    (x : PX.Level 1) (hxV : PX.levelVal 1 x ∈ V) (h0 : IsZeroAt P g (PX.levelVal 1 x)) :
    PX.tangentFiber x →ₗ[ℝ] P ⁻¹' {PX.levelVal 1 x} :=
  (pullbackFiberCLE (P := P) (f := (Subtype.val : V → X)) ⟨_, hxV⟩).toLinearMap ∘ₗ
    (B.restrictOpen hV).linZeroAt (isScSmoothSection_restrictOpen_of_isScSmoothOn hV hg hgV)
      (levelPt hV x hxV) ((isZeroAt_restrictSection_iff' hg _).2 h0) ∘ₗ
    ((B.restrictIso hV).base.tangentFiberCLE (x := levelPt hV x hxV) (x' := x) (mem_univ _)
      rfl).symm.toLinearMap

/-- `levelVal (levelPt x) = x`. -/
@[simp] theorem levelVal_levelPt (x : PX.Level 1) (hxV : PX.levelVal 1 x ∈ V) :
    (PX.restrictOpen hV).levelVal 1 (levelPt hV x hxV) = ⟨PX.levelVal 1 x, hxV⟩ := rfl

/-- **For an sc-smooth section, `linZeroAtOn` is Part I's `g'(x)`** (`linZeroAt`): the
inclusion `Y|V → Y` carries the linearization (`LocalIso.linZeroAt_transport`). -/
theorem linZeroAtOn_eq_linZeroAt {g : X → Y} (hg : B.IsScSmoothSection g)
    (hgV : PX.IsScSmoothOn B.toMPolyfold0 g V) (x : PX.Level 1) (hxV : PX.levelVal 1 x ∈ V)
    (h0 : IsZeroAt P g (PX.levelVal 1 x)) :
    B.linZeroAtOn hV hg.1 hgV x hxV h0 = B.linZeroAt hg x h0 := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  set e := (B.restrictIso hV).base.tangentFiberCLE (x := levelPt hV x hxV) (x' := x)
    (mem_univ _) rfl with he
  have h := (B.restrictIso hV).linZeroAt_transport
    (isScSmoothSection_restrictOpen_of_isScSmoothOn hV hg.1 hgV) hg
    (B.restrictSection_eqOn_restrictIso hV hg.1) (x := levelPt hV x hxV) (x' := x) (mem_univ _)
    rfl ((isZeroAt_restrictSection_iff' hg.1 _).2 h0) h0 (e.symm v)
  have hv : tangentMapOnCLM (B.restrictIso hV).base.isScSmoothOn (mem_univ _) rfl (e.symm v) = v :=
    e.apply_symm_apply v
  rw [hv] at h
  exact h

/-- **The index of `(f + s)'(x)` for a local sc⁺-section `s` on `V`** is the local index of
`(f, x)` (Definition 6.2.1 with local sections, `IsIndexAtLocal`). -/
theorem linZeroAtOn_sectionAdd_index {f s : X → Y} (hf : B.IsScFredholmSection f)
    (hs : B.IsScPlusSectionOn s V) (hsec : IsSection P s) {x : PX.Level 1}
    (hxV : PX.levelVal 1 x ∈ V) (h0 : IsZeroAt P (Polyfold.sectionAdd P f s) (PX.levelVal 1 x))
    {i : ℤ} (hi : B.IsIndexAtLocal f (PX.levelVal 1 x) i) :
    HasFiniteIndex (B.linZeroAtOn hV (hf.isScSmooth.1.sectionAdd hsec)
        (hf.isScSmooth.isScSmoothOn_sectionAdd hV hs hsec) x hxV h0) ∧
      linIndex (B.linZeroAtOn hV (hf.isScSmooth.1.sectionAdd hsec)
        (hf.isScSmooth.isScSmoothOn_sectionAdd hV hs hsec) x hxV h0) = i := by
  have hfV := hf.restrictOpen hV
  have hsV := hs.restrictOpen hV hsec
  have h0V : IsZeroAt (pullbackProj P (Subtype.val : V → X))
      (Polyfold.sectionAdd (pullbackProj P (Subtype.val : V → X))
        (restrictSection P V f hf.isScSmooth.1) (restrictSection P V s hsec))
      ((PX.restrictOpen hV).levelVal 1 (levelPt hV x hxV)) := by
    rw [← restrictSection_sectionAdd hf.isScSmooth.1 hsec]
    exact (isZeroAt_restrictSection_iff' _ _).2 h0
  obtain ⟨j, hj⟩ := StrongBundle.exists_isIndexAt_of_isZeroAt_sectionAdd hfV hsV h0V
  have hij : i = j := hi.unique hf ⟨hf.isScSmooth.1, V, hV, hxV, hj⟩
  subst hij
  obtain ⟨h1, h2⟩ := StrongBundle.linZeroAt_sectionAdd_index hfV hsV h0V hj
  have hcongr : (B.restrictOpen hV).linZeroAt
      (isScSmoothSection_restrictOpen_of_isScSmoothOn hV (hf.isScSmooth.1.sectionAdd hsec)
        (hf.isScSmooth.isScSmoothOn_sectionAdd hV hs hsec)) (levelPt hV x hxV)
      ((isZeroAt_restrictSection_iff' (hf.isScSmooth.1.sectionAdd hsec) _).2 h0) =
      (B.restrictOpen hV).linZeroAt (hfV.isScSmooth.sectionAdd hsV) (levelPt hV x hxV) h0V :=
    StrongBundle.linZeroAt_congr (restrictSection_sectionAdd hf.isScSmooth.1 hsec) _ _ _ _ _
  have hc := hasFiniteIndex_conj
    ((B.restrictIso hV).base.tangentFiberCLE (x := levelPt hV x hxV) (x' := x) (mem_univ _)
      rfl).symm.toLinearEquiv
    (pullbackFiberCLE (P := P) (f := (Subtype.val : V → X)) ⟨_, hxV⟩).toLinearEquiv h1
  unfold linZeroAtOn
  rw [hcongr]
  exact ⟨hc.1, hc.2.trans h2⟩

include hV in
/-- At a zero of `f + s`, `s` a local sc⁺-section on `V`, `(f, x)` has a local index. -/
theorem exists_isIndexAtLocal_of_isZeroAt_sectionAdd {f s : X → Y}
    (hf : B.IsScFredholmSection f) (hs : B.IsScPlusSectionOn s V) (hsec : IsSection P s) {x : X}
    (hxV : x ∈ V) (h0 : IsZeroAt P (Polyfold.sectionAdd P f s) x) :
    ∃ i, B.IsIndexAtLocal f x i := by
  have h0V : IsZeroAt (pullbackProj P (Subtype.val : V → X))
      (Polyfold.sectionAdd (pullbackProj P (Subtype.val : V → X))
        (restrictSection P V f hf.isScSmooth.1) (restrictSection P V s hsec)) ⟨x, hxV⟩ := by
    rw [← restrictSection_sectionAdd hf.isScSmooth.1 hsec]
    exact (isZeroAt_restrictSection_iff' _ _).2 h0
  obtain ⟨j, hj⟩ := StrongBundle.exists_isIndexAt_of_isZeroAt_sectionAdd (hf.restrictOpen hV)
    (hs.restrictOpen hV hsec) h0V
  exact ⟨j, hf.isScSmooth.1, V, hV, hxV, hj⟩

end Restrict

section Transport

variable {X' : Type u} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {U : Set X} {U' : Set X'}
  {V : Set X} (hV : IsOpen V) [Nonempty V] [ParacompactSpace V]
  [ParacompactSpace (pullbackSpace P (Subtype.val : V → X))]
  {V' : Set X'} (hV' : IsOpen V') [Nonempty V'] [ParacompactSpace V']
  [ParacompactSpace (pullbackSpace P' (Subtype.val : V' → X'))]

/-- **The linearization at a zero of a section sc-smooth on `V` is carried along a local strong
bundle isomorphism**: for `g` sc-smooth on `V`, `g'` sc-smooth on `V'` with `g = Ψ ∘ g' ∘ ϕ` on
`U ∩ V ∩ ϕ⁻¹(V')`, `Φ (g'(x) α) = g''(x') (Tϕ(x) α)` (`linZeroAt_transport` on `P|V`, `P'|V'`). -/
theorem LocalIso.linZeroAtOn_transport (L : LocalIso B B' U U') {g : X → Y} {g' : X' → Y'}
    (hg : IsSection P g) (hgV : PX.IsScSmoothOn B.toMPolyfold0 g V) (hg' : IsSection P' g')
    (hg'V' : PX'.IsScSmoothOn B'.toMPolyfold0 g' V')
    (heq : EqOn g (L.Ψ ∘ g' ∘ L.ϕ) (U ∩ V ∩ L.ϕ ⁻¹' V')) {x : PX.Level 1} {x' : PX'.Level 1}
    (hxU : PX.levelVal 1 x ∈ U) (hxV : PX.levelVal 1 x ∈ V) (hx'V' : PX'.levelVal 1 x' ∈ V')
    (hxx' : L.ϕ (PX.levelVal 1 x) = PX'.levelVal 1 x') (h0 : IsZeroAt P g (PX.levelVal 1 x))
    (h0' : IsZeroAt P' g' (PX'.levelVal 1 x')) (v : PX.tangentFiber x) :
    L.Φ (B.linZeroAtOn hV hg hgV x hxV h0 v : Y) =
      (B'.linZeroAtOn hV' hg' hg'V' x' hx'V' h0'
        (tangentMapOnCLM L.base.isScSmoothOn hxU hxx' v) : Y') := by
  obtain ⟨w, rfl⟩ : ∃ w, v = ((B.restrictIso hV).base.tangentFiberCLE
      (x := levelPt hV x hxV) (x' := x) (mem_univ _) rfl) w :=
    ⟨((B.restrictIso hV).base.tangentFiberCLE (x := levelPt hV x hxV) (x' := x) (mem_univ _)
      rfl).symm v, (((B.restrictIso hV).base.tangentFiberCLE (x := levelPt hV x hxV) (x' := x)
      (mem_univ _) rfl).apply_symm_apply v).symm⟩
  have hgVs := isScSmoothSection_restrictOpen_of_isScSmoothOn hV hg hgV
  have hg'Vs := isScSmoothSection_restrictOpen_of_isScSmoothOn hV' hg' hg'V'
  have hxN : (PX.restrictOpen hV).levelVal 1 (levelPt hV x hxV) ∈
      ((univ ∩ (B.restrictIso hV).ϕ ⁻¹' U) ∩ ((B.restrictIso hV).trans L).ϕ ⁻¹' V') :=
    ⟨⟨mem_univ _, hxU⟩, by
      change L.ϕ (PX.levelVal 1 x) ∈ V'
      rw [hxx']; exact hx'V'⟩
  have hNx : (((B.restrictIso hV).trans L).trans (B'.restrictIso hV').symm).ϕ
      ((PX.restrictOpen hV).levelVal 1 (levelPt hV x hxV)) =
      (PX'.restrictOpen hV').levelVal 1 (levelPt hV' x' hx'V') := by
    change MPolyfold.openRetraction V' (L.ϕ (PX.levelVal 1 x)) = _
    rw [hxx']; exact MPolyfold.openRetraction_of_mem hx'V'
  have heqN : EqOn (restrictSection P V g hg)
      ((((B.restrictIso hV).trans L).trans (B'.restrictIso hV').symm).Ψ ∘
        restrictSection P' V' g' hg' ∘
          (((B.restrictIso hV).trans L).trans (B'.restrictIso hV').symm).ϕ)
      ((univ ∩ (B.restrictIso hV).ϕ ⁻¹' U) ∩ ((B.restrictIso hV).trans L).ϕ ⁻¹' V') := by
    rintro z ⟨⟨-, hzU⟩, hzV'⟩
    have hz' : L.ϕ z.1 ∈ V' := hzV'
    change restrictSection P V g hg z = B.restrictIsoInv V (L.Ψ
      ((restrictSection P' V' g' hg' (MPolyfold.openRetraction V' (L.ϕ z.1))).1.2))
    rw [MPolyfold.openRetraction_of_mem hz']
    change _ = B.restrictIsoInv V (L.Ψ (g' (L.ϕ z.1)))
    have hh : g z.1 = L.Ψ (g' (L.ϕ z.1)) := heq ⟨⟨hzU, z.2⟩, hz'⟩
    rw [← hh]
    exact (B.restrictSection_eqOn_restrictIso hV hg) (mem_univ z)
  have h0V := (isZeroAt_restrictSection_iff' hg ⟨_, hxV⟩).2 h0
  have h0V' := (isZeroAt_restrictSection_iff' hg' ⟨_, hx'V'⟩).2 h0'
  have key := (((B.restrictIso hV).trans L).trans (B'.restrictIso hV').symm).linZeroAt_transport
    hgVs hg'Vs heqN hxN hNx h0V h0V' w
  have hT : tangentMapOnCLM
      (((B.restrictIso hV).trans L).trans (B'.restrictIso hV').symm).base.isScSmoothOn hxN hNx w =
      ((B'.restrictIso hV').base.tangentFiberCLE (x := levelPt hV' x' hx'V') (x' := x')
        (mem_univ _) rfl).symm (tangentMapOnCLM L.base.isScSmoothOn hxU hxx'
          (((B.restrictIso hV).base.tangentFiberCLE (x := levelPt hV x hxV) (x' := x)
            (mem_univ _) rfl) w)) := by
    rw [ContinuousLinearEquiv.eq_symm_apply]
    apply Subtype.ext
    have he' : ((((B'.restrictIso hV').base.tangentFiberCLE (x := levelPt hV' x' hx'V')
        (x' := x') (mem_univ _) rfl) (tangentMapOnCLM
          (((B.restrictIso hV).trans L).trans (B'.restrictIso hV').symm).base.isScSmoothOn
            hxN hNx w) : PX'.tangentFiber x') : PX'.TangentSpace) =
        tangentMapOn (B'.restrictIso hV').base.isScSmoothOn (tangentMapOn
          (((B.restrictIso hV).trans L).trans (B'.restrictIso hV').symm).base.isScSmoothOn
            w.1) :=
      (tangentMapOnCLM_apply (B'.restrictIso hV').base.isScSmoothOn (mem_univ _) rfl _).trans
        (congrArg _ (tangentMapOnCLM_apply _ _ _ w))
    have he : ((((B.restrictIso hV).base.tangentFiberCLE (x := levelPt hV x hxV) (x' := x)
        (mem_univ _) rfl) w : PX.tangentFiber x) : PX.TangentSpace) =
        tangentMapOn (B.restrictIso hV).base.isScSmoothOn w.1 :=
      tangentMapOnCLM_apply (B.restrictIso hV).base.isScSmoothOn (mem_univ _) rfl w
    rw [he', tangentMapOnCLM_apply, he]
    have hD : IsOpen ((univ ∩ (B.restrictIso hV).ϕ ⁻¹' U) ∩
        ((B.restrictIso hV).trans L).ϕ ⁻¹' V') :=
      (((B.restrictIso hV).trans L).trans (B'.restrictIso hV').symm).isOpen_U
    have hwD : w.1 ∈ (PX.restrictOpen hV).tangentPreimage
        ((univ ∩ (B.restrictIso hV).ϕ ⁻¹' U) ∩ ((B.restrictIso hV).trans L).ϕ ⁻¹' V') := by
      rw [MPolyfold.mem_tangentPreimage,
        GCT.PolyfoldConstruction.levelVal_tangentProj_of_mem w.2]
      exact hxN
    have hιD : (PX.restrictOpen hV).IsScSmoothOn PX (B.restrictIso hV).ϕ
        ((univ ∩ (B.restrictIso hV).ϕ ⁻¹' U) ∩ ((B.restrictIso hV).trans L).ϕ ⁻¹' V') :=
      (B.restrictIso hV).base.isScSmoothOn.mono hD (subset_univ _)
    have hmapD : MapsTo (B.restrictIso hV).ϕ
        ((univ ∩ (B.restrictIso hV).ϕ ⁻¹' U) ∩ ((B.restrictIso hV).trans L).ϕ ⁻¹' V') U :=
      fun z hz => hz.1.2
    have c1 := tangentMapOn_comp (B'.restrictIso hV').base.isScSmoothOn
      (((B.restrictIso hV).trans L).trans (B'.restrictIso hV').symm).base.isScSmoothOn
      (mapsTo_univ _ _) hwD
    have c2 := tangentMapOn_comp L.base.isScSmoothOn hιD hmapD hwD
    have c3 := tangentMapOn_congr ((B'.restrictIso hV').base.isScSmoothOn.comp
      (((B.restrictIso hV).trans L).trans (B'.restrictIso hV').symm).base.isScSmoothOn
      (mapsTo_univ _ _)) (L.base.isScSmoothOn.comp hιD hmapD) hD subset_rfl subset_rfl
      (fun z hz => by
        have hz' : L.ϕ z.1 ∈ V' := hz.2
        change (MPolyfold.openRetraction V' (L.ϕ z.1)).1 = L.ϕ z.1
        rw [MPolyfold.openRetraction_of_mem hz']) hwD
    have c4 := tangentMapOn_congr hιD (B.restrictIso hV).base.isScSmoothOn hD subset_rfl
      (subset_univ _) (fun _ _ => rfl) hwD
    rw [Function.comp_apply] at c1 c2
    rw [← c1, c3, c2, c4]
  have hP : P' (L.Φ (((B.restrictOpen hV).linZeroAt hgVs (levelPt hV x hxV) h0V w :
      pullbackSpace P (Subtype.val : V → X)).1.2)) ∈ V' := by
    have hk : P (((B.restrictOpen hV).linZeroAt hgVs (levelPt hV x hxV) h0V w :
        pullbackSpace P (Subtype.val : V → X)).1.2) = PX.levelVal 1 x := by
      have h1 := (((B.restrictOpen hV).linZeroAt hgVs (levelPt hV x hxV) h0V w :
        pullbackSpace P (Subtype.val : V → X))).2
      have h2 : (((B.restrictOpen hV).linZeroAt hgVs (levelPt hV x hxV) h0V w :
          pullbackSpace P (Subtype.val : V → X))).1.1 = ⟨PX.levelVal 1 x, hxV⟩ :=
        ((B.restrictOpen hV).linZeroAt hgVs (levelPt hV x hxV) h0V w).2
      rw [h1, h2]
    rw [L.covers _ (by rw [hk]; exact hxU), hk, hxx']
    exact hx'V'
  change L.Φ (((B.restrictOpen hV).linZeroAt hgVs (levelPt hV x hxV) h0V
      (((B.restrictIso hV).base.tangentFiberCLE (x := levelPt hV x hxV) (x' := x) (mem_univ _)
        rfl).symm (((B.restrictIso hV).base.tangentFiberCLE (x := levelPt hV x hxV) (x' := x)
          (mem_univ _) rfl) w)) : pullbackSpace P (Subtype.val : V → X)).1.2) =
    (((B'.restrictOpen hV').linZeroAt hg'Vs (levelPt hV' x' hx'V') h0V'
      (((B'.restrictIso hV').base.tangentFiberCLE (x := levelPt hV' x' hx'V') (x' := x')
        (mem_univ _) rfl).symm (tangentMapOnCLM L.base.isScSmoothOn hxU hxx'
          (((B.restrictIso hV).base.tangentFiberCLE (x := levelPt hV x hxV) (x' := x)
            (mem_univ _) rfl) w))) :
        pullbackSpace P' (Subtype.val : V' → X')).1.2)
  rw [ContinuousLinearEquiv.symm_apply_apply, ← hT, ← key]
  exact (B'.restrictIsoInv_snd hP).symm

end Transport

section Loc

variable {X' : Type u} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {U : Set X} {U' : Set X'}

/-- **`f + s` is sc-smooth on `V`** for an sc-smooth section `f` and a local sc⁺-section `s` on
the open set `V` (`isScSmoothOn_sectionAdd`, with the instances of `V` supplied near each point). -/
theorem IsScSmoothSection.isScSmoothOn_sectionAdd' {V : Set X} (hV : IsOpen V) {f s : X → Y}
    (hf : B.IsScSmoothSection f) (hs : B.IsScPlusSectionOn s V) (hsec : IsSection P s) :
    PX.IsScSmoothOn B.toMPolyfold0 (Polyfold.sectionAdd P f s) V :=
  MPolyfold.IsScSmoothOn.of_locally hV fun x hx => ⟨V, hV, hx, subset_rfl, by
    have : Nonempty V := ⟨⟨x, hx⟩⟩
    have := PX.paracompactSpace_subtype V
    have := paracompactSpace_pullbackSpace (f := (Subtype.val : V → X)) (PX.restrictOpen hV) B
    exact hf.isScSmoothOn_sectionAdd hV hs hsec⟩

variable (B) in
/-- **The linearization at a zero `x ∈ V` of a section sc-smooth on the open set `V`**:
`linZeroAtOn` with the instances of `V` and `P|V` supplied. -/
def linZeroLoc {V : Set X} (hV : IsOpen V) {g : X → Y} (hg : IsSection P g)
    (hgV : PX.IsScSmoothOn B.toMPolyfold0 g V) (x : PX.Level 1) (hxV : PX.levelVal 1 x ∈ V)
    (h0 : IsZeroAt P g (PX.levelVal 1 x)) : PX.tangentFiber x →ₗ[ℝ] P ⁻¹' {PX.levelVal 1 x} :=
  haveI : Nonempty V := ⟨⟨_, hxV⟩⟩
  haveI := PX.paracompactSpace_subtype V
  haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : V → X)) (PX.restrictOpen hV) B
  B.linZeroAtOn hV hg hgV x hxV h0

/-- `linZeroLoc` is `linZeroAtOn` for any instances of `V` and `P|V`. -/
theorem linZeroLoc_eq {V : Set X} (hV : IsOpen V) [Nonempty V] [ParacompactSpace V]
    [ParacompactSpace (pullbackSpace P (Subtype.val : V → X))] {g : X → Y} (hg : IsSection P g)
    (hgV : PX.IsScSmoothOn B.toMPolyfold0 g V) (x : PX.Level 1) (hxV : PX.levelVal 1 x ∈ V)
    (h0 : IsZeroAt P g (PX.levelVal 1 x)) :
    B.linZeroLoc hV hg hgV x hxV h0 = B.linZeroAtOn hV hg hgV x hxV h0 := rfl

/-- **For an sc-smooth section, `linZeroLoc` is Part I's `g'(x)`.** -/
theorem linZeroLoc_eq_linZeroAt {V : Set X} (hV : IsOpen V) {g : X → Y}
    (hg : B.IsScSmoothSection g) (hgV : PX.IsScSmoothOn B.toMPolyfold0 g V) (x : PX.Level 1)
    (hxV : PX.levelVal 1 x ∈ V) (h0 : IsZeroAt P g (PX.levelVal 1 x)) :
    B.linZeroLoc hV hg.1 hgV x hxV h0 = B.linZeroAt hg x h0 := by
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have := PX.paracompactSpace_subtype V
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : V → X)) (PX.restrictOpen hV) B
  exact B.linZeroAtOn_eq_linZeroAt hV hg hgV x hxV h0

/-- **The index of `(f + s)'(x)` for a local sc⁺-section `s` on `V`** is the local index of
`(f, x)` (`linZeroAtOn_sectionAdd_index`). -/
theorem linZeroLoc_sectionAdd_index {V : Set X} (hV : IsOpen V) {f s : X → Y}
    (hf : B.IsScFredholmSection f) (hs : B.IsScPlusSectionOn s V) (hsec : IsSection P s)
    {x : PX.Level 1} (hxV : PX.levelVal 1 x ∈ V)
    (h0 : IsZeroAt P (Polyfold.sectionAdd P f s) (PX.levelVal 1 x))
    {i : ℤ} (hi : B.IsIndexAtLocal f (PX.levelVal 1 x) i) :
    HasFiniteIndex (B.linZeroLoc hV (hf.isScSmooth.1.sectionAdd hsec)
        (hf.isScSmooth.isScSmoothOn_sectionAdd' hV hs hsec) x hxV h0) ∧
      linIndex (B.linZeroLoc hV (hf.isScSmooth.1.sectionAdd hsec)
        (hf.isScSmooth.isScSmoothOn_sectionAdd' hV hs hsec) x hxV h0) = i := by
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have := PX.paracompactSpace_subtype V
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : V → X)) (PX.restrictOpen hV) B
  exact linZeroAtOn_sectionAdd_index hV hf hs hsec hxV h0 hi

/-- **At a zero of `f + s`, `s` a local sc⁺-section on `V ∋ x`, `(f, x)` has a local index.** -/
theorem exists_isIndexAtLocal_of_isZeroAt_sectionAdd' {V : Set X} (hV : IsOpen V) {f s : X → Y}
    (hf : B.IsScFredholmSection f) (hs : B.IsScPlusSectionOn s V) (hsec : IsSection P s) {x : X}
    (hxV : x ∈ V) (h0 : IsZeroAt P (Polyfold.sectionAdd P f s) x) :
    ∃ i, B.IsIndexAtLocal f x i := by
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have := PX.paracompactSpace_subtype V
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : V → X)) (PX.restrictOpen hV) B
  exact exists_isIndexAtLocal_of_isZeroAt_sectionAdd hV hf hs hsec hxV h0

/-- **`linZeroLoc` is carried along a local strong bundle isomorphism**
(`linZeroAtOn_transport`). -/
theorem LocalIso.linZeroLoc_transport (L : LocalIso B B' U U') {V : Set X} (hV : IsOpen V)
    {V' : Set X'} (hV' : IsOpen V') {g : X → Y} {g' : X' → Y'}
    (hg : IsSection P g) (hgV : PX.IsScSmoothOn B.toMPolyfold0 g V) (hg' : IsSection P' g')
    (hg'V' : PX'.IsScSmoothOn B'.toMPolyfold0 g' V')
    (heq : EqOn g (L.Ψ ∘ g' ∘ L.ϕ) (U ∩ V ∩ L.ϕ ⁻¹' V')) {x : PX.Level 1} {x' : PX'.Level 1}
    (hxU : PX.levelVal 1 x ∈ U) (hxV : PX.levelVal 1 x ∈ V) (hx'V' : PX'.levelVal 1 x' ∈ V')
    (hxx' : L.ϕ (PX.levelVal 1 x) = PX'.levelVal 1 x') (h0 : IsZeroAt P g (PX.levelVal 1 x))
    (h0' : IsZeroAt P' g' (PX'.levelVal 1 x')) (v : PX.tangentFiber x) :
    L.Φ (B.linZeroLoc hV hg hgV x hxV h0 v : Y) =
      (B'.linZeroLoc hV' hg' hg'V' x' hx'V' h0'
        (tangentMapOnCLM L.base.isScSmoothOn hxU hxx' v) : Y') := by
  have : Nonempty V := ⟨⟨_, hxV⟩⟩
  have := PX.paracompactSpace_subtype V
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : V → X)) (PX.restrictOpen hV) B
  have : Nonempty V' := ⟨⟨_, hx'V'⟩⟩
  have := PX'.paracompactSpace_subtype V'
  have := paracompactSpace_pullbackSpace (f := (Subtype.val : V' → X')) (PX'.restrictOpen hV') B'
  exact L.linZeroAtOn_transport hV hV' hg hgV hg' hg'V' heq hxU hxV hx'V' hxx' h0 h0' v

/-- **A local sc⁺-section is carried along a local strong bundle isomorphism**: for `s` a local
sc⁺-section on an open `W ⊆ U`, `Φ ∘ s ∘ g` is a local sc⁺-section on `U' ∩ g⁻¹(W)`, lifted by
`Φ[1] ∘ G ∘ g`. -/
theorem LocalIso.isScPlusSectionOn_transport (L : LocalIso B B' U U') {s : X → Y} {W : Set X}
    (hs : B.IsScPlusSectionOn s W) (hW : IsOpen W) (hWU : W ⊆ U) :
    B'.IsScPlusSectionOn (L.Φ ∘ s ∘ L.g) (U' ∩ L.g ⁻¹' W) := by
  obtain ⟨hsec, G, hG, hGs⟩ := hs
  have hO : IsOpen (U' ∩ L.g ⁻¹' W) :=
    L.base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage L.isOpen_U' hW
  refine ⟨fun y hy => ?_, L.Φ₁ ∘ G ∘ L.g, fun y hy => ?_, ?_⟩
  · have h1 : P (s (L.g y)) = L.g y := hsec _ hy.2
    change P' (L.Φ (s (L.g y))) = y
    rw [L.covers _ (by rw [h1]; exact hWU hy.2), h1, L.base.right_inv y hy.1]
  · have h1 : P (B.oneVal (G (L.g y))) ∈ U := by rw [hG _ hy.2, hsec _ hy.2]; exact hWU hy.2
    change B'.oneVal (L.Φ₁ (G (L.g y))) = L.Φ (s (L.g y))
    rw [L.oneVal_Φ₁ _ h1, hG _ hy.2]
  · have hg : PX'.IsScSmoothOn PX L.g (U' ∩ L.g ⁻¹' W) :=
      L.base.isScSmoothOn_inv.mono hO inter_subset_left
    have hGg := hGs.comp hg (fun y hy => hy.2)
    exact L.one.isScSmoothOn.comp hGg (fun y hy => by
      change P (B.oneVal (G (L.g y))) ∈ U
      rw [hG _ hy.2, hsec _ hy.2]; exact hWU hy.2)

end Loc

end StrongBundle

section ExtendByZero

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, Module ℝ (P ⁻¹' {x})]

open scoped Classical in
/-- **A section defined on `W`, extended by `0`**: `s` on `W` and the zero section off `W`. -/
def extendByZero (P : Y → X) [∀ x, AddCommGroup (P ⁻¹' {x})] (s : X → Y) (W : Set X) : X → Y :=
  fun y => if y ∈ W then s y else fiberZero P y

/-- On `W` the extension by `0` is `s`. -/
theorem extendByZero_of_mem {s : X → Y} {W : Set X} {y : X} (hy : y ∈ W) :
    extendByZero P s W y = s y := if_pos hy

/-- The extension by `0` of a section over `W` is a section. -/
theorem isSection_extendByZero {s : X → Y} {W : Set X} (hs : ∀ y ∈ W, P (s y) = y) :
    IsSection P (extendByZero P s W) := fun y => by
  by_cases hy : y ∈ W
  · rw [extendByZero_of_mem hy]; exact hs y hy
  · unfold extendByZero; rw [if_neg hy]; exact proj_fiberZero P y

end ExtendByZero

/-- The extension by `0` of a local sc⁺-section on `W` is a local sc⁺-section on `W`. -/
theorem StrongBundle.IsScPlusSectionOn.extendByZero {s : X → Y} {W : Set X}
    (hs : B.IsScPlusSectionOn s W) : B.IsScPlusSectionOn (Polyfold.extendByZero P s W) W := by
  obtain ⟨hsec, G, hG, hGs⟩ := hs
  exact ⟨fun y hy => by rw [extendByZero_of_mem hy]; exact hsec y hy, G,
    fun y hy => by rw [extendByZero_of_mem hy]; exact hG y hy, hGs⟩


end PartI

end Polyfold

namespace Polyfold

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory GroupoidalCategory.BanachFunctor StrongBundleUniformizerConstruction
  StrongBundleUniformizerData PolyfoldConstruction StrongRetr MPolyfold

variable {C : GCT.{u}} {V : C.VectorBundle} {S : C.PolyfoldConstruction}
  (Q : V.StrongPolyfoldBundleConstruction S) {f : V.SectionFunctor}

/-! ### `Lin(f, α)` with local sc⁺-sections -/

variable (f) in
/-- The operator `f'_s(α) : e ↦ Ψ̄(x)((f_Ψ̄ + s)'(x)(S_Ψ e))` of Definition 18.1.4 for a **local
sc⁺-section `s` defined near `x`**, on an open `W ∋ x`, with `(f_Ψ̄ + s)(x) = 0`. -/
def linOpLoc (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj) [Fact (S.TangentObj α)]
    {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) {W : Set Ψ.1.base.O} (hW : IsOpen W)
    (hxW : Ψ.1.base.P.levelVal 1 x ∈ W) {s : Ψ.1.base.O → Ψ.1.K} (hsec : IsSection Ψ.1.p s)
    (hs : Ψ.1.B.IsScPlusSectionOn s W)
    (h0 : IsZeroAt Ψ.1.p (sectionAdd Ψ.1.p (Ψ.1.localRep f) s) (Ψ.1.base.P.levelVal 1 x)) :
    S.TangentSpaceAt α →ₗ[ℝ] V.V α :=
  (V.fiberCast hx).toLinearMap ∘ₗ (Ψ.1.fiber (Ψ.1.base.P.levelVal 1 x)).toLinearMap ∘ₗ
    Ψ.1.B.linZeroLoc hW ((Ψ.1.isSection_localRep f).sectionAdd hsec)
      ((hf α Ψ.1 hΨ).isScSmoothOn_sectionAdd' hW hs hsec) x hxW h0 ∘ₗ
      (S.tangentChartCLE α (Q.baseUnif Ψ) x hx).toLinearMap

variable (f) in
/-- **`Lin(f, α)` with local sc⁺-sections, read through one `Ψ̄ ∈ F̄(α)`** and its point `x`
over `α`: the operators `f'_s(α)` for the local sc⁺-sections `s` defined near `x`
(Definition 18.1.4, p. 845, "a local sc⁺-section `s` defined near `q₀`"). -/
def linSetLocAt (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj) [Fact (S.TangentObj α)]
    {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) : Set (S.TangentSpaceAt α →ₗ[ℝ] V.V α) :=
  {L | ∃ (W : Set Ψ.1.base.O) (hW : IsOpen W) (hxW : Ψ.1.base.P.levelVal 1 x ∈ W)
    (s : Ψ.1.base.O → Ψ.1.K) (hsec : IsSection Ψ.1.p s) (hs : Ψ.1.B.IsScPlusSectionOn s W)
    (h0 : IsZeroAt Ψ.1.p (sectionAdd Ψ.1.p (Ψ.1.localRep f) s) (Ψ.1.base.P.levelVal 1 x)),
    L = Q.linOpLoc f hf α hΨ x hx hW hxW hsec hs h0}

variable (f) in
/-- **Definition 18.1.4, p. 845, `Lin(f, α)` with local sc⁺-sections**: the union over
`Ψ̄ ∈ F̄(α)` and the points `x` of `Ψ̄` over `α` of `linSetLocAt`. -/
def linSetLoc (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj) [Fact (S.TangentObj α)] :
    Set (S.TangentSpaceAt α →ₗ[ℝ] V.V α) :=
  {L | ∃ (Ψ : Q.Unif) (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α), L ∈ Q.linSetLocAt f hf α hΨ x hx}

/-- **`Lin(f, α)` with local sc⁺-sections is the union of the sets read through the
`Ψ̄ ∈ F̄(α)`.** -/
theorem mem_linSetLoc_iff (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] (L : S.TangentSpaceAt α →ₗ[ℝ] V.V α) :
    L ∈ Q.linSetLoc f hf α ↔ ∃ (Ψ : Q.Unif) (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
      (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α), L ∈ Q.linSetLocAt f hf α hΨ x hx :=
  Iff.rfl

/-- `(α, f'_s(α) e) = Ψ̄((f_Ψ̄ + s)'(x)(S_Ψ e))` for a local sc⁺-section `s`. -/
theorem objMk_linOpLoc (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj) [Fact (S.TangentObj α)]
    {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) {W : Set Ψ.1.base.O} (hW : IsOpen W)
    (hxW : Ψ.1.base.P.levelVal 1 x ∈ W) {s : Ψ.1.base.O → Ψ.1.K} (hsec : IsSection Ψ.1.p s)
    (hs : Ψ.1.B.IsScPlusSectionOn s W)
    (h0 : IsZeroAt Ψ.1.p (sectionAdd Ψ.1.p (Ψ.1.localRep f) s) (Ψ.1.base.P.levelVal 1 x))
    (e : S.TangentSpaceAt α) :
    V.objMk α (Q.linOpLoc f hf α hΨ x hx hW hxW hsec hs h0 e) =
      Ψ.1.obj (Ψ.1.B.linZeroLoc hW ((Ψ.1.isSection_localRep f).sectionAdd hsec)
        ((hf α Ψ.1 hΨ).isScSmoothOn_sectionAdd' hW hs hsec) x hxW h0
        (S.tangentChartCLE α (Q.baseUnif Ψ) x hx e)) := by
  set k := Ψ.1.B.linZeroLoc hW ((Ψ.1.isSection_localRep f).sectionAdd hsec)
    ((hf α Ψ.1 hΨ).isScSmoothOn_sectionAdd' hW hs hsec) x hxW h0
    (S.tangentChartCLE α (Q.baseUnif Ψ) x hx e)
  rw [Ψ.1.obj_of_eq k.2]
  exact V.objMk_fiberCast hx _

/-! ### Relation to `linSet` -/

/-- **A global sc⁺-section is a local one on `O`**: `f'_s(α)` of `linOp` is `f'_s(α)` of
`linOpLoc` with `W = O`. -/
theorem linOp_eq_linOpLoc (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) {s : Ψ.1.base.O → Ψ.1.K}
    (hs : Ψ.1.B.IsScPlusSection s)
    (h0 : IsZeroAt Ψ.1.p (sectionAdd Ψ.1.p (Ψ.1.localRep f) s) (Ψ.1.base.P.levelVal 1 x)) :
    Q.linOp f hf α hΨ x hx hs h0 = Q.linOpLoc f hf α hΨ x hx isOpen_univ (mem_univ _) hs.1
      (hs.isScPlusSectionOn isOpen_univ) h0 := by
  unfold linOp linOpLoc
  rw [StrongBundle.linZeroLoc_eq_linZeroAt isOpen_univ ((hf α Ψ.1 hΨ).sectionAdd hs)]

/-- **`Lin(f, α)` read through `Ψ̄` lies in its local form.** -/
theorem linSetAt_subset_linSetLocAt (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) :
    Q.linSetAt f hf α hΨ x hx ⊆ Q.linSetLocAt f hf α hΨ x hx := by
  rintro L ⟨s, hs, h0, rfl⟩
  exact ⟨univ, isOpen_univ, mem_univ _, s, hs.1, hs.isScPlusSectionOn isOpen_univ, h0,
    Q.linOp_eq_linOpLoc hf α hΨ x hx hs h0⟩

/-- **`Lin(f, α)` with global sc⁺-sections lies in `Lin(f, α)` with local ones.** -/
theorem linSet_subset_linSetLoc (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] : Q.linSet f hf α ⊆ Q.linSetLoc f hf α := by
  intro L hL
  obtain ⟨Ψ, hΨ, x, hx, hL⟩ := (Q.mem_linSet_iff hf α L).1 hL
  exact ⟨Ψ, hΨ, x, hx, Q.linSetAt_subset_linSetLocAt hf α hΨ x hx hL⟩

/-! ### The index -/

/-- **The elements of `Lin(f, α)` with local sc⁺-sections read through `Ψ̄` have the local index
of `(f_Ψ̄, q₀)`** (Definition 6.2.1 with local sections, `IsIndexAtLocal`). -/
theorem linSetLocAt_index (hF : Q.IsScFredholmSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) {i : ℤ}
    (hi : Ψ.1.B.IsIndexAtLocal (Ψ.1.localRep f) (Ψ.1.base.P.levelVal 1 x) i)
    {L : S.TangentSpaceAt α →ₗ[ℝ] V.V α}
    (hL : L ∈ Q.linSetLocAt f hF.isScSmoothSectionFunctor α hΨ x hx) :
    HasFiniteIndex L ∧ linIndex L = i := by
  obtain ⟨W, hW, hxW, s, hsec, hs, h0, rfl⟩ := hL
  obtain ⟨h1, h2⟩ := StrongBundle.linZeroLoc_sectionAdd_index hW (hF α Ψ.1 hΨ) hs hsec hxW h0 hi
  have hc := hasFiniteIndex_conj (S.tangentChartCLE α (Q.baseUnif Ψ) x hx).toLinearEquiv
    ((Ψ.1.fiber (Ψ.1.base.P.levelVal 1 x)).toLinearEquiv.trans (V.fiberCast hx).toLinearEquiv) h1
  exact ⟨hc.1, hc.2.trans h2⟩

/-- Every element of `Lin(f, α)` with local sc⁺-sections read through `Ψ̄` comes with a local
index of `(f_Ψ̄, q₀)`. -/
theorem exists_isIndexAtLocal_of_mem_linSetLocAt (hF : Q.IsScFredholmSectionFunctor f)
    (α : C.Obj) [Fact (S.TangentObj α)] {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α)
    (x : Ψ.1.base.P.Level 1) (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α)
    {L : S.TangentSpaceAt α →ₗ[ℝ] V.V α}
    (hL : L ∈ Q.linSetLocAt f hF.isScSmoothSectionFunctor α hΨ x hx) :
    ∃ i, Ψ.1.B.IsIndexAtLocal (Ψ.1.localRep f) (Ψ.1.base.P.levelVal 1 x) i := by
  obtain ⟨W, hW, hxW, s, hsec, hs, h0, -⟩ := hL
  exact StrongBundle.exists_isIndexAtLocal_of_isZeroAt_sectionAdd' hW (hF α Ψ.1 hΨ) hs hsec hxW h0

/-! ### Local sections related by `t̄` near a point of `M(Ψ, Ψ')` -/

/-- **The transition law of the linearizations for sections sc-smooth near the points and related
by `t̄` near `a`**: for sections `g` of `K → O` sc-smooth on an open `W ∋ s(a)` and `g'` of
`K' → O'` sc-smooth on an open `W' ∋ t(a)`, with `g'(t b) = T(b, g(s b))` for `b` in an open
`N ∋ a`, and zeros `x` of `g` over `s(a)` and `y` of `g'` over `t(a)` on level `1`,
`g''(y)(Tσ(x) h) = T(a, g'(x) h)` (`linZeroAt_transAct_of_eqOn` with sections sc-smooth on open
sets). -/
theorem linZeroLoc_transAct_of_eqOn (Ψ Ψ' : Q.Unif) (a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ'))
    {g : Ψ.1.base.O → Ψ.1.K} {g' : Ψ'.1.base.O → Ψ'.1.K}
    (hg : IsSection Ψ.1.p g) (hg' : IsSection Ψ'.1.p g')
    {W : Set Ψ.1.base.O} (hW : IsOpen W) {W' : Set Ψ'.1.base.O} (hW' : IsOpen W')
    (hgW : Ψ.1.base.P.IsScSmoothOn Ψ.1.B.toMPolyfold0 g W)
    (hg'W' : Ψ'.1.base.P.IsScSmoothOn Ψ'.1.B.toMPolyfold0 g' W')
    {N : Set (S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ'))} (hN : IsOpen N) (haN : a ∈ N)
    (hrel : ∀ b ∈ N, g' b.tgt = transAct b (g b.src) (hg b.src))
    {x : Ψ.1.base.P.Level 1} {y : Ψ'.1.base.P.Level 1} (hx : Ψ.1.base.P.levelVal 1 x = a.src)
    (hy : Ψ'.1.base.P.levelVal 1 y = a.tgt) (hxW : Ψ.1.base.P.levelVal 1 x ∈ W)
    (hyW' : Ψ'.1.base.P.levelVal 1 y ∈ W')
    (h0 : IsZeroAt Ψ.1.p g (Ψ.1.base.P.levelVal 1 x))
    (h0' : IsZeroAt Ψ'.1.p g' (Ψ'.1.base.P.levelVal 1 y))
    (v : Ψ.1.base.P.tangentFiber x) :
    (Ψ'.1.B.linZeroLoc hW' hg' hg'W' y hyW' h0' (S.transTangent a hx hy v) : Ψ'.1.K) =
      transAct a (Ψ.1.B.linZeroLoc hW hg hgW x hxW h0 v)
        ((show Ψ.1.p (Ψ.1.B.linZeroLoc hW hg hgW x hxW h0 v : Ψ.1.K) = _ from
          (Ψ.1.B.linZeroLoc hW hg hgW x hxW h0 v).2).trans hx) := by
  obtain ⟨Ws, Ws', has, his⟩ := Q.isLocalStrongBundleIso_src Ψ Ψ' a
  obtain ⟨Wt₁, Wt₁', hat₁, hit₁⟩ := Q.isLocalStrongBundleIso_trans Ψ Ψ' a
  obtain ⟨gb, hgb⟩ := hit₁.isScDiffeoOn_base
  have hWt : IsOpen (Wt₁ ∩ N) := hgb.isOpen_source.inter hN
  have hit := hit₁.restrict hgb hWt inter_subset_left
  have hat : a ∈ Wt₁ ∩ N := ⟨hat₁, haN⟩
  set Ls := his.toLocalIso with hLs
  set Lt := hit.toLocalIso with hLt
  have heqT : EqOn (Q.transSec Ψ Ψ' hg) (Lt.Ψ ∘ g' ∘ Lt.ϕ) (Wt₁ ∩ N) := by
    intro b hb
    have h1 := Lt.zero.left_inv (Q.transSec Ψ Ψ' hg b) hb
    have h2 : Lt.Φ (Q.transSec Ψ Ψ' hg b) = g' b.tgt := (hrel b hb.2).symm
    rw [← h1, h2]
    rfl
  have hVT : IsOpen (Ws ∩ Ls.ϕ ⁻¹' W) :=
    Ls.base.isScSmoothOn.continuousOn.isOpen_inter_preimage Ls.isOpen_U hW
  have haVT : a ∈ Ws ∩ Ls.ϕ ⁻¹' W := ⟨has, by
    change a.src ∈ W
    rw [← hx]; exact hxW⟩
  have hgs : (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).IsScSmoothOn
      (Q.transBundle Ψ Ψ').toMPolyfold0 (Q.transSec Ψ Ψ' hg) (Ws ∩ Ls.ϕ ⁻¹' W) := by
    have hmaps : MapsTo (g ∘ Ls.ϕ) (Ws ∩ Ls.ϕ ⁻¹' W) (Ψ.1.p ⁻¹' Ws') := fun b hb => by
      change Ψ.1.p (g (Ls.ϕ b)) ∈ Ws'
      rw [hg]; exact Ls.base.mapsTo hb.1
    exact (Ls.zero.isScSmoothOn_inv.comp
      (hgW.comp (Ls.base.isScSmoothOn.mono hVT inter_subset_left) fun b hb => hb.2)
      hmaps).congr fun b hb => (Q.eqOn_transSec_src Ψ Ψ' hg his hb.1).symm
  have hgsec : IsSection (pullbackProj Ψ.1.p fun a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ') => a.src)
      (Q.transSec Ψ Ψ' hg) := fun _ => rfl
  have hqs : Ψ.1.base.P.levelVal 1 x ∈ Ws' := by rw [hx]; exact Ls.base.mapsTo has
  have hga : Ls.g (Ψ.1.base.P.levelVal 1 x) = a := by rw [hx]; exact Ls.base.left_inv a has
  have ha1 : a ∈ (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelSet 1 :=
    (Ls.mem_levelSet_iff has 1).2 (by
      change a.src ∈ _
      rw [← hx]; exact Ψ.1.base.P.levelVal_mem x)
  set xa := (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelMk 1 a ha1 with hxadef
  have hxa : (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelVal 1 xa = a :=
    MPolyfold.levelVal_levelMk _ _ _
  have hxxa : Ls.symm.ϕ (Ψ.1.base.P.levelVal 1 x) =
      (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelVal 1 xa := hga.trans hxa.symm
  have hxaU : (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelVal 1 xa ∈ Wt₁ ∩ N := by
    rw [hxa]; exact hat
  have hxaVT : (S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelVal 1 xa ∈
      Ws ∩ Ls.ϕ ⁻¹' W := by
    rw [hxa]; exact haVT
  have hxay : Lt.ϕ ((S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelVal 1 xa) =
      Ψ'.1.base.P.levelVal 1 y := by rw [hxa, hy]; rfl
  have h0g : IsZeroAt _ (Q.transSec Ψ Ψ' hg)
      ((S.transPolyfold (Q.baseUnif Ψ) (Q.baseUnif Ψ')).levelVal 1 xa) :=
    Lt.isZeroAt_of_eqOn heqT hxaU (by rw [hxay]; exact h0')
  have heqA : EqOn g (Ls.symm.Ψ ∘ Q.transSec Ψ Ψ' hg ∘ Ls.symm.ϕ)
      (Ws' ∩ W ∩ Ls.symm.ϕ ⁻¹' (Ws ∩ Ls.ϕ ⁻¹' W)) :=
    fun q hq => by
      change g q = g (Ls.ϕ (Ls.g q))
      rw [Ls.base.right_inv q hq.1.1]
  have hA := Ls.symm.linZeroLoc_transport hW hVT hg hgW hgsec hgs heqA hqs hxW hxaVT hxxa h0 h0g v
  set w := tangentMapOnCLM Ls.symm.base.isScSmoothOn hqs hxxa v with hwdef
  have hB := Lt.linZeroLoc_transport hVT hW' hgsec hgs hg' hg'W' (fun b hb => heqT hb.1.1)
    hxaU hxaVT hyW' hxay h0g h0' w
  have hW2 : IsOpen (Ws ∩ (Wt₁ ∩ N)) := Ls.isOpen_U.inter Lt.isOpen_U
  let T : S.AdmissibleTriple a := ⟨_, Ws ∩ (Wt₁ ∩ N), _, Ls.g, Lt.g, ⟨has, hat⟩,
    Ls.base.restrict hW2 inter_subset_left, Lt.base.restrict hW2 inter_subset_right⟩
  have hTo : IsOpen T.srcSet := T.isScDiffeoOn_src.isOpen_target
  have hfs : Ψ.1.base.P.IsScSmoothOn _ Ls.g T.srcSet :=
    Ls.base.isScSmoothOn_inv.mono hTo inter_subset_left
  have hmaps : MapsTo Ls.g T.srcSet (Wt₁ ∩ N) := fun p hp => hp.2.2
  have hvmem : v.1 ∈ Ψ.1.base.P.tangentPreimage T.srcSet := by
    rw [MPolyfold.mem_tangentPreimage, GCT.PolyfoldConstruction.levelVal_tangentProj_of_mem v.2,
      hx]
    exact T.src_mem
  have hT : S.transTangent a hx hy v = tangentMapOnCLM Lt.base.isScSmoothOn hxaU hxay w := by
    refine Subtype.ext ?_
    rw [transTangent_apply, tangentMapOnCLM_apply, hwdef, tangentMapOnCLM_apply,
      transMap_eq T ((GCT.PolyfoldConstruction.levelVal_tangentProj_of_mem v.2).trans hx)]
    refine (MPolyfold.tangentMapOn_comp Lt.base.isScSmoothOn hfs hmaps hvmem).trans ?_
    exact congrArg _ (MPolyfold.tangentMapOn_congr hfs Ls.base.isScSmoothOn_inv hTo subset_rfl
      inter_subset_left (fun _ _ => rfl) hvmem)
  rw [hT, ← hB, ← hA]
  set k := (Ψ.1.B.linZeroLoc hW hg hgW x hxW h0 v : Ψ.1.K) with hkdef
  have hk : Ψ.1.p k = a.src :=
    (show Ψ.1.p k = _ from (Ψ.1.B.linZeroLoc hW hg hgW x hxW h0 v).2).trans hx
  have hkW : Ψ.1.p k ∈ Ws' := by rw [hk]; exact Ls.base.mapsTo has
  have e : Ls.Ψ k = (⟨(a, k), hk⟩ : Q.TransSpace Ψ Ψ') := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change pullbackProj Ψ.1.p _ (Ls.Ψ k) = a
      rw [Ls.covers_inv k hkW, hk]; exact Ls.base.left_inv a has
    · exact Ls.zero.right_inv k hkW
  change Q.transT Ψ Ψ' (Ls.Ψ k) = _
  rw [e]
  rfl

/-- **Transport of an element of `Lin(f, α)` with local sc⁺-sections along `a ∈ M(Ψ, Ψ')`**,
with no hypothesis: for a local sc⁺-section `s` on an open `W ∋ x` with `(f_Ψ̄ + s)(x) = 0`, `x`
over `s(a)`, the section `s' = t̄ ∘ s̄⁻¹ ∘ s ∘ s ∘ t⁻¹` near `t(a)` (extended by `0`) is a local
sc⁺-section on an open `W' ∋ y`, `y` over `t(a)`, with `(f_Ψ̄' + s')(y) = 0` and
`(f_Ψ̄' + s')'(y)(Tσ(x) h) = T(a, (f_Ψ̄ + s)'(x) h)`. -/
theorem exists_linZeroLoc_transAct (Ψ Ψ' : Q.Unif) (a : S.Tr (Q.baseUnif Ψ) (Q.baseUnif Ψ'))
    (hfΨ : Ψ.1.B.IsScSmoothSection (Ψ.1.localRep f))
    (hfΨ' : Ψ'.1.B.IsScSmoothSection (Ψ'.1.localRep f))
    {x : Ψ.1.base.P.Level 1} {y : Ψ'.1.base.P.Level 1} (hx : Ψ.1.base.P.levelVal 1 x = a.src)
    (hy : Ψ'.1.base.P.levelVal 1 y = a.tgt) {W : Set Ψ.1.base.O} (hW : IsOpen W)
    (hxW : Ψ.1.base.P.levelVal 1 x ∈ W) {s : Ψ.1.base.O → Ψ.1.K} (hsec : IsSection Ψ.1.p s)
    (hs : Ψ.1.B.IsScPlusSectionOn s W)
    (h0 : IsZeroAt Ψ.1.p (sectionAdd Ψ.1.p (Ψ.1.localRep f) s) (Ψ.1.base.P.levelVal 1 x)) :
    ∃ (W' : Set Ψ'.1.base.O) (hW' : IsOpen W') (hyW' : Ψ'.1.base.P.levelVal 1 y ∈ W')
      (s' : Ψ'.1.base.O → Ψ'.1.K) (hsec' : IsSection Ψ'.1.p s')
      (hs' : Ψ'.1.B.IsScPlusSectionOn s' W')
      (h0' : IsZeroAt Ψ'.1.p (sectionAdd Ψ'.1.p (Ψ'.1.localRep f) s')
        (Ψ'.1.base.P.levelVal 1 y)),
      ∀ v : Ψ.1.base.P.tangentFiber x,
        (Ψ'.1.B.linZeroLoc hW' ((Ψ'.1.isSection_localRep f).sectionAdd hsec')
            (hfΨ'.isScSmoothOn_sectionAdd' hW' hs' hsec') y hyW' h0'
            (S.transTangent a hx hy v) : Ψ'.1.K) =
          transAct a (Ψ.1.B.linZeroLoc hW ((Ψ.1.isSection_localRep f).sectionAdd hsec)
            (hfΨ.isScSmoothOn_sectionAdd' hW hs hsec) x hxW h0 v)
            ((show Ψ.1.p (Ψ.1.B.linZeroLoc hW ((Ψ.1.isSection_localRep f).sectionAdd hsec)
              (hfΨ.isScSmoothOn_sectionAdd' hW hs hsec) x hxW h0 v : Ψ.1.K) = _ from
              (Ψ.1.B.linZeroLoc hW ((Ψ.1.isSection_localRep f).sectionAdd hsec)
                (hfΨ.isScSmoothOn_sectionAdd' hW hs hsec) x hxW h0 v).2).trans hx) := by
  obtain ⟨Ws, Ws', has, his⟩ := Q.isLocalStrongBundleIso_src Ψ Ψ' a
  obtain ⟨Wt, Wt', hat, hit⟩ := Q.isLocalStrongBundleIso_trans Ψ Ψ' a
  set Ls := his.toLocalIso with hLs
  set Lt := hit.toLocalIso with hLt
  have hW₀ : IsOpen (W ∩ Ws') := hW.inter Ls.isOpen_U'
  have hsT := Ls.symm.isScPlusSectionOn_transport (hs.mono hW₀ inter_subset_left) hW₀
    inter_subset_right
  have hN : IsOpen (Wt ∩ (Ws ∩ Ls.ϕ ⁻¹' (W ∩ Ws'))) :=
    Lt.isOpen_U.inter (Ls.base.isScSmoothOn.continuousOn.isOpen_inter_preimage Ls.isOpen_U hW₀)
  have haN : a ∈ Wt ∩ (Ws ∩ Ls.ϕ ⁻¹' (W ∩ Ws')) :=
    ⟨hat, has, (by change a.src ∈ W; rw [← hx]; exact hxW), Ls.base.mapsTo has⟩
  have hs₂ := Lt.isScPlusSectionOn_transport (hsT.mono hN inter_subset_right) hN inter_subset_left
  have hW' : IsOpen (Wt' ∩ Lt.g ⁻¹' (Wt ∩ (Ws ∩ Ls.ϕ ⁻¹' (W ∩ Ws')))) :=
    Lt.base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage Lt.isOpen_U' hN
  have hsec' := isSection_extendByZero hs₂.1
  have hs' := hs₂.extendByZero
  have hmemN : ∀ b ∈ Wt ∩ (Ws ∩ Ls.ϕ ⁻¹' (W ∩ Ws')),
      Lt.ϕ b ∈ Wt' ∩ Lt.g ⁻¹' (Wt ∩ (Ws ∩ Ls.ϕ ⁻¹' (W ∩ Ws'))) := fun b hb =>
    ⟨Lt.base.mapsTo hb.1, by
      change Lt.g (Lt.ϕ b) ∈ Wt ∩ (Ws ∩ Ls.ϕ ⁻¹' (W ∩ Ws'))
      rw [Lt.base.left_inv b hb.1]; exact hb⟩
  have hrel : ∀ b ∈ Wt ∩ (Ws ∩ Ls.ϕ ⁻¹' (W ∩ Ws')),
      extendByZero Ψ'.1.p (Lt.Φ ∘ (Ls.symm.Φ ∘ s ∘ Ls.symm.g) ∘ Lt.g)
        (Wt' ∩ Lt.g ⁻¹' (Wt ∩ (Ws ∩ Ls.ϕ ⁻¹' (W ∩ Ws')))) b.tgt =
        transAct b (s b.src) (hsec b.src) := by
    intro b hb
    change extendByZero Ψ'.1.p _ _ (Lt.ϕ b) = _
    rw [extendByZero_of_mem (hmemN b hb)]
    change Lt.Φ (Ls.Ψ (s (Ls.ϕ (Lt.g (Lt.ϕ b))))) = _
    rw [Lt.base.left_inv b hb.1]
    have hk : Ψ.1.p (s (Ls.ϕ b)) ∈ Ws' := by rw [hsec]; exact hb.2.2.2
    have e : Ls.Ψ (s (Ls.ϕ b)) = (⟨(b, s b.src), hsec b.src⟩ : Q.TransSpace Ψ Ψ') := by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · change pullbackProj Ψ.1.p _ (Ls.Ψ (s (Ls.ϕ b))) = b
        rw [Ls.covers_inv _ hk, hsec]; exact Ls.base.left_inv b hb.2.1
      · exact Ls.zero.right_inv _ hk
    rw [e]
    rfl
  have hrel' : ∀ b ∈ Wt ∩ (Ws ∩ Ls.ϕ ⁻¹' (W ∩ Ws')),
      sectionAdd Ψ'.1.p (Ψ'.1.localRep f) (extendByZero Ψ'.1.p
        (Lt.Φ ∘ (Ls.symm.Φ ∘ s ∘ Ls.symm.g) ∘ Lt.g)
        (Wt' ∩ Lt.g ⁻¹' (Wt ∩ (Ws ∩ Ls.ϕ ⁻¹' (W ∩ Ws'))))) b.tgt =
        transAct b (sectionAdd Ψ.1.p (Ψ.1.localRep f) s b.src)
          (((Ψ.1.isSection_localRep f).sectionAdd hsec) b.src) :=
    fun b hb => Q.sectionAdd_localRep_transAct Ψ Ψ' hsec hsec' b (hrel b hb)
  have h0a : sectionAdd Ψ.1.p (Ψ.1.localRep f) s a.src = fiberZero Ψ.1.p a.src := by
    have h := h0
    unfold IsZeroAt at h
    rwa [hx] at h
  have h0' : IsZeroAt Ψ'.1.p (sectionAdd Ψ'.1.p (Ψ'.1.localRep f) (extendByZero Ψ'.1.p
        (Lt.Φ ∘ (Ls.symm.Φ ∘ s ∘ Ls.symm.g) ∘ Lt.g)
        (Wt' ∩ Lt.g ⁻¹' (Wt ∩ (Ws ∩ Ls.ϕ ⁻¹' (W ∩ Ws'))))))
      (Ψ'.1.base.P.levelVal 1 y) := by
    unfold IsZeroAt
    rw [hy, hrel' a haN]
    exact transAct_eq_fiberZero (Ψ := Ψ.1.toStrongBundleUniformizerData)
      (Ψ' := Ψ'.1.toStrongBundleUniformizerData) a _ h0a
  have hyW' : Ψ'.1.base.P.levelVal 1 y ∈ Wt' ∩ Lt.g ⁻¹' (Wt ∩ (Ws ∩ Ls.ϕ ⁻¹' (W ∩ Ws'))) := by
    rw [hy]; exact hmemN a haN
  exact ⟨_, hW', hyW', _, hsec', hs', h0', fun v => Q.linZeroLoc_transAct_of_eqOn Ψ Ψ' a _ _ hW
    hW' _ _ hN haN hrel' hx hy hxW hyW' h0 h0' v⟩

/-! ### Definition 18.1.4 with local sc⁺-sections: independence of `Ψ̄`, the index, and `φ_*` -/

/-- **`Lin(f, α)` with local sc⁺-sections read through `Ψ̄₁` lies in the one read through `Ψ̄₂`**,
along `(q₁, 1_α, q₂) ∈ M(Ψ₁, Ψ₂)`. -/
theorem linSetLocAt_subset (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] {Ψ₁ Ψ₂ : Q.Unif}
    (hΨ₁ : Ψ₁.1 ∈ Q.F α) (hΨ₂ : Ψ₂.1 ∈ Q.F α) (x₁ : Ψ₁.1.base.P.Level 1)
    (hx₁ : Ψ₁.1.base.obj (Ψ₁.1.base.P.levelVal 1 x₁) = α) (x₂ : Ψ₂.1.base.P.Level 1)
    (hx₂ : Ψ₂.1.base.obj (Ψ₂.1.base.P.levelVal 1 x₂) = α) :
    Q.linSetLocAt f hf α hΨ₁ x₁ hx₁ ⊆ Q.linSetLocAt f hf α hΨ₂ x₂ hx₂ := by
  rintro L ⟨W, hW, hxW, s, hsec, hs, h0, rfl⟩
  set a := S.unitTr (Ψ := Q.baseUnif Ψ₁) (Ψ' := Q.baseUnif Ψ₂) _ _ hx₁ hx₂
  obtain ⟨W', hW', hyW', s', hsec', hs', h0', hlin⟩ := Q.exists_linZeroLoc_transAct Ψ₁ Ψ₂ a
    (hf α Ψ₁.1 hΨ₁) (hf α Ψ₂.1 hΨ₂) (x := x₁) (y := x₂) rfl rfl hW hxW hsec hs h0
  refine ⟨W', hW', hyW', s', hsec', hs', h0', LinearMap.ext fun e => objMk_eq_iff.1 ?_⟩
  rw [objMk_linOpLoc, objMk_linOpLoc]
  have hTc : S.tangentChartCLE α (Q.baseUnif Ψ₂) x₂ hx₂ e =
      S.transTangent a rfl rfl (S.tangentChartCLE α (Q.baseUnif Ψ₁) x₁ hx₁ e) := by
    have h := tangentChart_symm_trans (S := S) (Q.baseUnif Ψ₁) (Q.base_mem α _ hΨ₁) x₁ hx₁
      (Q.baseUnif Ψ₂) (Q.base_mem α _ hΨ₂) x₂ hx₂ (S.tangentChartCLE α (Q.baseUnif Ψ₁) x₁ hx₁ e)
    rw [coe_tangentChartCLE α (Q.baseUnif Ψ₁) (Q.base_mem α _ hΨ₁) x₁ hx₁,
      Equiv.symm_apply_apply] at h
    rw [coe_tangentChartCLE α (Q.baseUnif Ψ₁) (Q.base_mem α _ hΨ₁) x₁ hx₁,
      coe_tangentChartCLE α (Q.baseUnif Ψ₂) (Q.base_mem α _ hΨ₂) x₂ hx₂]
    exact h
  rw [hTc, hlin]
  erw [obj_transAct]
  exact (act_unit' _ _).symm

/-- **Definition 18.1.4, "the collection is independent of the choice of `Ψ̄`"**, with local
sc⁺-sections and no further hypothesis: `Lin(f, α)` is the set read through any one
`Ψ̄ ∈ F̄(α)` and any one point `x` of `Ψ̄` over `α`. -/
theorem linSetLoc_eq_linSetLocAt (hf : Q.IsScSmoothSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] {Ψ : Q.Unif} (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
    (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α) :
    Q.linSetLoc f hf α = Q.linSetLocAt f hf α hΨ x hx := by
  refine Set.Subset.antisymm (fun L hL => ?_) fun L hL => (Q.mem_linSetLoc_iff hf α L).2
    ⟨Ψ, hΨ, x, hx, hL⟩
  obtain ⟨Ψ₁, hΨ₁, x₁, hx₁, hL₁⟩ := (Q.mem_linSetLoc_iff hf α L).1 hL
  exact Q.linSetLocAt_subset hf α hΨ₁ hΨ x₁ hx₁ x hx hL₁

/-- **Definition 18.1.4, "linear sc-Fredholm operators … which have the same index"**, with
local sc⁺-sections and no further hypothesis: there is one `i` with every `L ∈ Lin(f, α)` of
finite index `i`. -/
theorem exists_index_linSetLoc (hF : Q.IsScFredholmSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] :
    ∃ i : ℤ, ∀ L ∈ Q.linSetLoc f hF.isScSmoothSectionFunctor α,
      HasFiniteIndex L ∧ linIndex L = i := by
  by_cases h : (Q.linSetLoc f hF.isScSmoothSectionFunctor α).Nonempty
  · obtain ⟨L₀, hL₀⟩ := h
    obtain ⟨Ψ, hΨ, x, hx, hL₀'⟩ := (Q.mem_linSetLoc_iff _ α L₀).1 hL₀
    obtain ⟨i, hi⟩ := Q.exists_isIndexAtLocal_of_mem_linSetLocAt hF α hΨ x hx hL₀'
    refine ⟨i, fun L hL => Q.linSetLocAt_index hF α hΨ x hx hi ?_⟩
    rw [← Q.linSetLoc_eq_linSetLocAt _ α hΨ x hx]
    exact hL
  · exact ⟨0, fun L hL => (h ⟨L, hL⟩).elim⟩

/-- **`φ_*` maps `Lin(f, α)` with local sc⁺-sections read through `Ψ̄` into `Lin(f, α')` read
through `Ψ̄'`**, along `(q, φ, q') ∈ M(Ψ, Ψ')`. -/
theorem linPush_mem_linSetLocAt (hf : Q.IsScSmoothSectionFunctor f) {α α' : C.Obj}
    [Fact (S.TangentObj α)] [Fact (S.TangentObj α')] (φ : C.Mor)
    (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α') {Ψ Ψ' : Q.Unif}
    (hΨ : Ψ.1 ∈ Q.F α) (hΨ' : Ψ'.1 ∈ Q.F α')
    (x : Ψ.1.base.P.Level 1) (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α)
    (x' : Ψ'.1.base.P.Level 1) (hx' : Ψ'.1.base.obj (Ψ'.1.base.P.levelVal 1 x') = α')
    {L : S.TangentSpaceAt α →ₗ[ℝ] V.V α} (hL : L ∈ Q.linSetLocAt f hf α hΨ x hx) :
    linPush φ hs ht L ∈ Q.linSetLocAt f hf α' hΨ' x' hx' := by
  obtain ⟨W, hW, hxW, s, hsec, hsP, h0, rfl⟩ := hL
  set a := S.morTr (Ψ := Q.baseUnif Ψ) (Ψ' := Q.baseUnif Ψ') (Ψ.1.base.P.levelVal 1 x) φ
    (Ψ'.1.base.P.levelVal 1 x') hx hs hx' ht
  obtain ⟨W', hW', hyW', s', hsec', hs', h0', hlin⟩ := Q.exists_linZeroLoc_transAct Ψ Ψ' a
    (hf α Ψ.1 hΨ) (hf α' Ψ'.1 hΨ') (x := x) (y := x') rfl rfl hW hxW hsec hsP h0
  refine ⟨W', hW', hyW', s', hsec', hs', h0', LinearMap.ext fun e' => objMk_eq_iff.1 ?_⟩
  obtain ⟨e, rfl⟩ : ∃ e, e' = S.tangentMorCLE φ hs ht e :=
    ⟨(S.tangentMorCLE φ hs ht).symm e', (ContinuousLinearEquiv.apply_symm_apply _ _).symm⟩
  rw [objMk_linOpLoc, tangentChartCLE_tangentMorCLE φ hs ht (Q.baseUnif Ψ) (Q.baseUnif Ψ') x hx
    x' hx' e, hlin]
  change V.objMk α' (V.morFiber φ hs ht (Q.linOpLoc f hf α hΨ x hx hW hxW hsec hsP h0
    ((S.tangentMorCLE φ hs ht).symm (S.tangentMorCLE φ hs ht e)))) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, ← act_objMk_morFiber φ hs ht _ hs.symm]
  erw [obj_transAct]
  exact act_congr rfl (Q.objMk_linOpLoc hf α hΨ x hx hW hxW hsec hsP h0 e) _ _

/-- **Definition 18.1.4, "`φ_*` maps `Lin(f, α)` into `Lin(f, α')`"**, with local sc⁺-sections
and no further hypothesis (for `F̄(α') ≠ ∅`). -/
theorem linPush_mem_linSetLoc (hf : Q.IsScSmoothSectionFunctor f) {α α' : C.Obj}
    [Fact (S.TangentObj α)] [hα' : Fact (S.TangentObj α')] (φ : C.Mor)
    (hs : C.toGroupoidStr.src φ = α) (ht : C.toGroupoidStr.tgt φ = α') (hne' : (Q.F α').Nonempty)
    {L : S.TangentSpaceAt α →ₗ[ℝ] V.V α} (hL : L ∈ Q.linSetLoc f hf α) :
    linPush φ hs ht L ∈ Q.linSetLoc f hf α' := by
  obtain ⟨Ψ, hΨ, x, hx, hL⟩ := (Q.mem_linSetLoc_iff hf α L).1 hL
  exact (Q.mem_linSetLoc_iff hf α' _).2 ⟨Q.refBundleUnif hne', Q.refBundleUnif_mem hne', _,
    Q.obj_refBundlePoint hα'.out.1 hne', Q.linPush_mem_linSetLocAt hf φ hs ht hΨ
      (Q.refBundleUnif_mem hne') x hx _ _ hL⟩

/-- **Definition 18.1.4, p. 845, its further claims, with local sc⁺-sections** (no hypothesis
beyond Definition 18.1.1): `Lin(f, α)` contains the set built from global sc⁺-sections and is
the set read through any `Ψ̄ ∈ F̄(α)`; its elements have finite index, all the same; and `φ_*`
maps `Lin(f, α)` into `Lin(f, α')` for `φ : α → α'` with `F̄(α') ≠ ∅`. -/
theorem definition_18_1_4_local (hF : Q.IsScFredholmSectionFunctor f) (α : C.Obj)
    [Fact (S.TangentObj α)] :
    Q.linSet f hF.isScSmoothSectionFunctor α ⊆ Q.linSetLoc f hF.isScSmoothSectionFunctor α ∧
      (∀ (Ψ : Q.Unif) (hΨ : Ψ.1 ∈ Q.F α) (x : Ψ.1.base.P.Level 1)
        (hx : Ψ.1.base.obj (Ψ.1.base.P.levelVal 1 x) = α),
        Q.linSetLoc f hF.isScSmoothSectionFunctor α =
          Q.linSetLocAt f hF.isScSmoothSectionFunctor α hΨ x hx) ∧
      (∃ i : ℤ, ∀ L ∈ Q.linSetLoc f hF.isScSmoothSectionFunctor α,
        HasFiniteIndex L ∧ linIndex L = i) ∧
      ∀ (α' : C.Obj) [Fact (S.TangentObj α')] (φ : C.Mor) (hs : C.toGroupoidStr.src φ = α)
        (ht : C.toGroupoidStr.tgt φ = α'), (Q.F α').Nonempty →
        ∀ L ∈ Q.linSetLoc f hF.isScSmoothSectionFunctor α,
          linPush φ hs ht L ∈ Q.linSetLoc f hF.isScSmoothSectionFunctor α' :=
  ⟨Q.linSet_subset_linSetLoc _ α, fun _ hΨ x hx => Q.linSetLoc_eq_linSetLocAt _ α hΨ x hx,
    Q.exists_index_linSetLoc hF α,
    fun _ _ φ hs ht hne' _ hL => Q.linPush_mem_linSetLoc _ φ hs ht hne' hL⟩

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

end Polyfold
