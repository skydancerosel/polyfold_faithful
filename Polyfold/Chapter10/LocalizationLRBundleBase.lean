import Polyfold.Chapter10.LocalizationLREffectiveBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapters 8 and 10: **Definition 8.4.2** (§8.4, p. 382, new in the 2021 edition),
**Proposition 10.4.7** (§10.4, p. 501, new in the 2021 edition) and **Theorem 10.5.7** (§10.5,
p. 508; 2017: Theorem 10.10) for an effective target, without the (LR) of a base ep-groupoid
assumed in `LocalizationLREffectiveBundle.lean`.  Numbers and pages are the 2021 text's.

# Theorem 10.5.7 over an effective base from the local regularity property of strong bundles

## The text, paraphrased

(Definition 8.4.2) A strong bundle `(P : W → X, μ)` over an ep-groupoid has the local regularity
property if every object `x` has arbitrarily small open neighbourhoods `U(x)` with the natural
representation of `G_x` such that every strong bundle isomorphism `B : W|U(x) → W|U(x)` with
`|B(w)| = |w|` is `w ↦ g ∗ w = μ(Γ(g, P(w)), w)` for some `g ∈ G_x`.

(Proposition 10.4.7) For strong bundle equivalences `Φ, Ψ` with `|Φ| = |Ψ|` between strong
bundles with this property, every `x` has a neighbourhood `U(x)` with an sc-smooth `z ↦ α_z` such
that `μ'(α_z, Φ(v)) = Ψ(v)` for `P(v) = z`; the proof is a modification of that of Proposition
10.1.10 (1).

(Theorem 10.5.7) For strong bundles with the property, generalized strong bundle isomorphisms with
`|[D]| = |[D']|` are equal; the proof is Proposition 10.4.7.

## The question, and the answer

`SBLocalization.theorem_10_5_7_of_isEffective` assumes, besides an effective base of the target,
(LR) (Definition 7.4.19) of a base, because the formal `EpStrongBundle.IsLR` asks the conclusion
of Definition 8.4.2 only of strong bundle maps `Φ : W → W` defined on all of `W`, while the
text's `B` is a strong bundle isomorphism of `W|U(x)` only.

* `StrongBundle.IsLocalIsoOn` is a strong bundle isomorphism `W|U → W|U` with no condition off
  `W|U`, and `EpStrongBundle.IsLRLocal` is Definition 8.4.2 read with it.  It implies the formal
  `EpStrongBundle.IsLR` (`IsLRLocal.isLR`).  We do not know whether the converse holds: a strong
  bundle isomorphism of `W|U(x)` need not extend to a strong bundle map of `W`.
* **`SBLocalization.theorem_10_5_7_of_isEffective_of_isLRLocal`**: Theorem 10.5.7 holds when the
  target has `IsLRLocal` and its base is effective.  No (LR) of a base ep-groupoid is assumed, and
  the hypothesis on the source bundle is not needed (`theorem_10_5_7_of_isEffective_of_isLRLocal'`
  states the theorem with the text's hypotheses on both bundles).
* We do not derive (LR) of the base from `IsLRLocal`.  What it gives on the base is
  `IsLRLocal.exists_base`: the conclusion of Definition 7.4.19 for those orbit-preserving `β` of
  `U(x)` that are covered by an orbit-preserving strong bundle isomorphism of `W|U(x)`.  The proof
  uses it only for such `β`: the maps `γ = Q ∘ ϕ_F⁻¹` of (10.4), covered by
  `w ↦ μ'(ψ, G(F⁻¹(w)))`.
* Effectiveness is still needed under this reading:
  `LocalizationLRBundleBaseExamples.not_theorem_10_5_7_of_isLRLocal` (the example of Remark 10.5.5,
  over `ℤ/3 × ℝ ⇉ ℝ`, has `IsLRLocal`).

## What is formalized

* `StrongBundle.IsLocalIsoOn`, `IsLocalIsoOn.covers`, `IsStrongBundleIsoOn.isLocalIsoOn`,
  `isScDiffeoOn_one_of`; for the local inverse of a local strong bundle isomorphism,
  `IsStrongBundleIsoOn.oneVal_inv` and `IsStrongBundleIsoOn.exists_linear_inv`.
* `EpStrongBundle.IsLRLocal` (**Definition 8.4.2**), `IsLRLocal.isLR`, `IsLRLocal.exists_base`;
  satisfiable: `EpStrongBundle.isLRLocal_trivial`.
* `EpStrongBundle.lrAct` (`w ↦ μ(m, w)`), `lrActOne`, and their sc-smoothness along families of
  morphisms, `isScSmoothOn_lrAct`, `isScSmoothOn_lrActOne` (levels `[0]` and `[1]`).
* `SEP.exists_family_of_isLRLocal`: **Proposition 10.4.7** on the bases, with the property for
  the target only.
* `EpFunctor.naturallyEquivalent_of_isEffective_of_families` (the natural transformation of
  `EpFunctor.naturallyEquivalent_of_isEffective`, from local families) and
  `SEP.natEquiv_of_isEffective_of_isLRLocal`.
* **`SBLocalization.theorem_10_5_7_of_isEffective_of_isLRLocal`** and its primed form.  Hypotheses
  satisfiable: in `LocalizationLRBundleBaseExamples`,
  `theorem_10_5_7_of_isEffective_of_isLRLocal_hypotheses` and
  `naturallyEquivalent_of_isEffective_of_families_hypotheses`.

## The choices made

* The text assumes Definition 8.4.2 for both bundles.  We use it for the target `W'` of the two
  functors `Ψ ∘ ΠX, Ψ' ∘ ΠZ` out of the weak fibred product; this avoids Proposition 10.4.6 (the
  property under strong bundle equivalences), which is not formalized.  For `x` in the base of the
  weak fibred product, `ψ₀ : ϕ_G(x) → ϕ_F(x)`, `Q = ψ̂₀ ∘ ϕ_G` (`EpFunctor.TransportChart`) and the
  local inverse `F⁻¹` of `F` near `x` (Definition 10.4.1 (2)), the map
  `B(w) = μ'(ψ_{ϕ_F⁻¹(P'(w))}, G(F⁻¹(w)))` is a strong bundle isomorphism of `W'|U(ϕ_F(x))`
  covering `γ = Q ∘ ϕ_F⁻¹`, with inverse `w ↦ F(G⁻¹(μ'(ψ_{Q⁻¹(P'(w))}⁻¹, w)))`; Lemma 7.4.20
  gives `γ(U) = U`.
* "Strong bundle isomorphism `W|U(x) → W|U(x)`" is read as: linear on the fibres over `U(x)`,
  covering an sc-diffeomorphism of `U(x)`, and an sc-diffeomorphism of `W|U(x)` at level `[0]` and
  of `W[1]|U(x)` at level `[1]` (`IsStrongBundleIsoOn` without the strong bundle map on `W`).
* The effective base of the target is kept, as in `LocalizationLREffectiveBundle.lean`: it makes
  the families unique, so that they glue to a natural transformation.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter CategoryTheory

noncomputable section

namespace Polyfold

universe u v

/-! ### Local strong bundle isomorphisms `W|U → W|U` -/

section LocalIso

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

namespace StrongBundle

/-- **A strong bundle isomorphism `Y|U → Y|U` covering `β`**, with no condition off `Y|U`: `β` is
an sc-diffeomorphism of `U`, `Φ` is linear from `Y_x` to `Y_{β(x)}` for `x ∈ U`, and `Φ` is an
sc-diffeomorphism of `P⁻¹(U)` at level `[0]` and, through a map `Φ₁` of `Y[1]` agreeing with it,
at level `[1]`.  This is `IsStrongBundleIsoOn` without the requirement that `Φ` be a strong bundle
map on all of `Y`. -/
structure IsLocalIsoOn (B : StrongBundle PX P) (β : X → X) (Φ : Y → Y) (U : Set X) : Prop where
  fiber_linear : ∀ x ∈ U, ∃ L : P ⁻¹' {x} →ₗ[ℝ] P ⁻¹' {β x}, ∀ v, (L v : Y) = Φ v
  isScDiffeoOn_base : ∃ β' : X → X, PX.IsScDiffeoOn PX β β' U U
  isScDiffeoOn_zero : ∃ Ψ : Y → Y,
    B.toMPolyfold0.IsScDiffeoOn B.toMPolyfold0 Φ Ψ (P ⁻¹' U) (P ⁻¹' U)
  isScDiffeoOn_one : ∃ Φ₁ Ψ₁ : B.One → B.One,
    (∀ y, P (B.oneVal y) ∈ U → B.oneVal (Φ₁ y) = Φ (B.oneVal y)) ∧
    B.toMPolyfold1.IsScDiffeoOn B.toMPolyfold1 Φ₁ Ψ₁ ((P ∘ B.oneVal) ⁻¹' U)
      ((P ∘ B.oneVal) ⁻¹' U)

variable {B : StrongBundle PX P}

/-- The restriction to `Y|U` of a strong bundle map which is a strong bundle isomorphism
`Y|U → Y|U` is one in the sense of `IsLocalIsoOn`. -/
theorem IsStrongBundleIsoOn.isLocalIsoOn {β : X → X} {Φ : Y → Y}
    {hΦ : B.IsStrongBundleMap B β Φ} {U : Set X} (hi : B.IsStrongBundleIsoOn B hΦ U U) :
    B.IsLocalIsoOn β Φ U where
  fiber_linear x _ := ⟨hΦ.fiberLinearMap x, fun _ => rfl⟩
  isScDiffeoOn_base := hi.isScDiffeoOn_base
  isScDiffeoOn_zero := hi.isScDiffeoOn_zero
  isScDiffeoOn_one :=
    let ⟨Ψ₁, hΨ₁⟩ := hi.isScDiffeoOn_one
    ⟨_, Ψ₁, fun _ _ => rfl, hΨ₁⟩

end StrongBundle

end LocalIso

/-! ### Definition 8.4.2, read with strong bundle isomorphisms of `W|U(x)` -/

section BundleLR

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

/-- **2021 Definition 8.4.2, p. 382, with `B` a strong bundle isomorphism of `W|U(x)`**: inside
every open `O ∋ x` there is a natural representation `U(x)` such that every strong bundle
isomorphism `Φ : W|U(x) → W|U(x)` (`StrongBundle.IsLocalIsoOn`, no condition off `W|U(x)`) with
`|Φ(w)| = |w|` is `w ↦ g ∗ w` for some `g ∈ G_x`.  It implies `EpStrongBundle.IsLR`
(`IsLRLocal.isLR`); satisfiable: `EpStrongBundle.isLRLocal_trivial`. -/
def IsLRLocal (E : EpStrongBundle X B) : Prop :=
  ∀ (x : Obj) (O : Set Obj), IsOpen O → x ∈ O → ∃ R : X.NaturalRep x, R.U ⊆ O ∧
    ∀ (β : Obj → Obj) (Φ : W → W), B.IsLocalIsoOn β Φ R.U →
      (∀ w, P w ∈ R.U → E.toGroupoidStr.π (Φ w) = E.toGroupoidStr.π w) →
      ∃ g : X.Isotropy x, ∀ w (hw : P w ∈ R.U), Φ w = E.natLift R g w hw

/-- `IsLRLocal` implies the formal `IsLR`, which asks the same only of the strong bundle maps
defined on all of `W`. -/
theorem IsLRLocal.isLR {E : EpStrongBundle X B} (h : E.IsLRLocal) : E.IsLR := fun x O hO hxO =>
  let ⟨R, hRO, hR⟩ := h x O hO hxO
  ⟨R, hRO, fun β Φ _ hi hπ => hR β Φ hi.isLocalIsoOn hπ⟩

end EpStrongBundle

end BundleLR

section BundleLRWitness

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Z}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- **Witness** for `EpStrongBundle.IsLRLocal`: every strong bundle over a trivial ep-groupoid
has it (an orbit-preserving map of `W` is the identity, the action of `1`). -/
theorem EpStrongBundle.isLRLocal_trivial (B : StrongBundle PZ P) :
    (EpStrongBundle.trivial B).IsLRLocal := by
  intro x O hO hxO
  obtain ⟨R, hRO⟩ := (EpGroupoid.trivial PZ).theorem_7_1 x hO hxO
  refine ⟨R, hRO, fun β Φ _ hπ => ⟨1, fun w hw => ?_⟩⟩
  obtain ⟨q, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 (hπ w hw)
  exact h1.symm.trans h2

end BundleLRWitness

section LocalIsoHelpers

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type*} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type*} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type*} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]

namespace StrongBundle

variable {B : StrongBundle PX P} {B' : StrongBundle PX' P'}

/-- A local strong bundle isomorphism `Y|U → Y|U` covers its base map. -/
theorem IsLocalIsoOn.covers {β : X → X} {Φ : Y → Y} {U : Set X} (h : B.IsLocalIsoOn β Φ U)
    {w : Y} (hw : P w ∈ U) : P (Φ w) = β (P w) := by
  obtain ⟨L, hL⟩ := h.fiber_linear (P w) hw
  rw [← hL ⟨w, rfl⟩]
  exact (L ⟨w, rfl⟩).2

/-- The level-`[1]` part of a local strong bundle isomorphism from the level-`[0]` part: maps
`Φ₁, Ψ₁` of `Y[1]` agreeing with `Φ, Ψ` over `U` and sc-smooth on `Y[1]|U` are mutually inverse
sc-diffeomorphisms of `Y[1]|U`. -/
theorem isScDiffeoOn_one_of {Φ Ψ : Y → Y} {Φ₁ Ψ₁ : B.One → B.One} {U : Set X}
    (h0 : B.toMPolyfold0.IsScDiffeoOn B.toMPolyfold0 Φ Ψ (P ⁻¹' U) (P ⁻¹' U))
    (hΦ₁ : ∀ y, P (B.oneVal y) ∈ U → B.oneVal (Φ₁ y) = Φ (B.oneVal y))
    (hΨ₁ : ∀ y, P (B.oneVal y) ∈ U → B.oneVal (Ψ₁ y) = Ψ (B.oneVal y))
    (s₁ : B.toMPolyfold1.IsScSmoothOn B.toMPolyfold1 Φ₁ ((P ∘ B.oneVal) ⁻¹' U))
    (s₂ : B.toMPolyfold1.IsScSmoothOn B.toMPolyfold1 Ψ₁ ((P ∘ B.oneVal) ⁻¹' U)) :
    B.toMPolyfold1.IsScDiffeoOn B.toMPolyfold1 Φ₁ Ψ₁ ((P ∘ B.oneVal) ⁻¹' U)
      ((P ∘ B.oneVal) ⁻¹' U) := by
  have hm : ∀ y, P (B.oneVal y) ∈ U → P (B.oneVal (Φ₁ y)) ∈ U := fun y hy => by
    rw [hΦ₁ y hy]; exact h0.mapsTo hy
  have hm' : ∀ y, P (B.oneVal y) ∈ U → P (B.oneVal (Ψ₁ y)) ∈ U := fun y hy => by
    rw [hΨ₁ y hy]; exact h0.mapsTo_inv hy
  exact ⟨s₁, s₂, fun y hy => hm y hy, fun y hy => hm' y hy,
    fun y hy => B.oneVal_injective (by rw [hΨ₁ _ (hm y hy), hΦ₁ y hy, h0.left_inv _ hy]),
    fun y hy => B.oneVal_injective (by rw [hΦ₁ _ (hm' y hy), hΨ₁ y hy, h0.right_inv _ hy])⟩

variable {f : X → X'} {Φ : Y → Y'} {h : B.IsStrongBundleMap B' f Φ} {U : Set X} {U' : Set X'}
  {g : X' → X} {Ψ : Y' → Y}

include h in
/-- The level-`[1]` inverse of a local strong bundle isomorphism agrees with the level-`[0]`
inverse. -/
theorem IsStrongBundleIsoOn.oneVal_inv
    (hΨ : B.toMPolyfold0.IsScDiffeoOn B'.toMPolyfold0 Φ Ψ (P ⁻¹' U) (P' ⁻¹' U'))
    {Ψ₁ : B'.One → B.One}
    (hΨ₁ : B.toMPolyfold1.IsScDiffeoOn B'.toMPolyfold1 (oneRestrict B B' Φ h.mapsTo_oneSet) Ψ₁
      ((P ∘ B.oneVal) ⁻¹' U) ((P' ∘ B'.oneVal) ⁻¹' U')) {y : B'.One}
    (hy : P' (B'.oneVal y) ∈ U') : B.oneVal (Ψ₁ y) = Ψ (B'.oneVal y) := by
  have h1 : P (B.oneVal (Ψ₁ y)) ∈ U := hΨ₁.mapsTo_inv hy
  have h2 := congrArg B'.oneVal (hΨ₁.right_inv y hy)
  rw [oneVal_oneRestrict] at h2
  rw [← hΨ.left_inv _ h1, h2]

/-- The level-`[0]` inverse of a local strong bundle isomorphism is linear on the fibres. -/
theorem IsStrongBundleIsoOn.exists_linear_inv (hi : B.IsStrongBundleIsoOn B' h U U')
    (hg : PX.IsScDiffeoOn PX' f g U U')
    (hΨ : B.toMPolyfold0.IsScDiffeoOn B'.toMPolyfold0 Φ Ψ (P ⁻¹' U) (P' ⁻¹' U')) {y : X'}
    (hy : y ∈ U') : ∃ L : P' ⁻¹' {y} →ₗ[ℝ] P ⁻¹' {g y}, ∀ v, (L v : Y) = Ψ v := by
  have hx : g y ∈ U := hg.mapsTo_inv hy
  set e := hi.fiberEquiv hx
  refine ⟨(e.symm : P' ⁻¹' {f (g y)} →ₗ[ℝ] P ⁻¹' {g y}).comp
    (fiberCast P' (hg.right_inv y hy).symm), fun v => ?_⟩
  set u := fiberCast P' (hg.right_inv y hy).symm v
  have h1 : Φ (e.symm u : Y) = (u : Y') := by
    have := congrArg Subtype.val (e.apply_symm_apply u)
    rwa [IsStrongBundleIsoOn.fiberEquiv_apply] at this
  have h2 : (e.symm u : Y) ∈ P ⁻¹' U := by
    change P (e.symm u : Y) ∈ U; rw [(e.symm u).2]; exact hx
  change (e.symm u : Y) = Ψ v
  rw [← hΨ.left_inv _ h2, h1, fiberCast_val]

end StrongBundle

end LocalIsoHelpers

/-! ### The action `w ↦ μ(m, w)` along a family of morphisms -/

section Act

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  (E : EpStrongBundle X B)
  {V : Type*} [TopologicalSpace V] [T2Space V] [ParacompactSpace V] {Q : MPolyfold V}

namespace EpStrongBundle

open scoped Classical in
/-- `μ(m, w)` when `P(w) = s(m)`, and `w` otherwise. -/
def lrAct (m : Mor) (w : W) : W :=
  if h : P w = X.src m then E.μ ⟨(m, w), h⟩ else w

variable {E}

theorem lrAct_eq {m : Mor} {w : W} (h : P w = X.src m) : E.lrAct m w = E.μ ⟨(m, w), h⟩ := dif_pos h

theorem P_lrAct {m : Mor} {w : W} (h : P w = X.src m) : P (E.lrAct m w) = X.tgt m := by
  rw [lrAct_eq h, E.P_μ]

theorem π_lrAct {m : Mor} {w : W} (h : P w = X.src m) :
    E.toGroupoidStr.π (E.lrAct m w) = E.toGroupoidStr.π w := by
  rw [lrAct_eq h]
  exact (GroupoidStr.π_src_eq_π_tgt _ (⟨(m, w), h⟩ : pullbackSpace P X.src)).symm

theorem lrAct_inv_lrAct {m : Mor} {w : W} (h : P w = X.src m) :
    E.lrAct (X.inv m) (E.lrAct m w) = w := by
  have h' : P (E.lrAct m w) = X.src (X.inv m) := by rw [P_lrAct h, X.src_inv]
  rw [lrAct_eq h']
  refine Eq.trans ?_ (E.μ_inv_μ ⟨(m, w), h⟩ (by rw [← lrAct_eq h]; exact h'))
  exact E.μ_congr (Prod.ext rfl (lrAct_eq (E := E) h))

theorem lrAct_lrAct_inv {m : Mor} {w : W} (h : P w = X.src (X.inv m)) :
    E.lrAct m (E.lrAct (X.inv m) w) = w := by
  have h' : P (E.lrAct (X.inv m) w) = X.src m := by rw [P_lrAct h, X.tgt_inv]
  rw [lrAct_eq h']
  refine Eq.trans ?_ (E.μ_μ_inv m w h (by rw [← lrAct_eq h]; exact h'))
  exact E.μ_congr (Prod.ext rfl (lrAct_eq (E := E) h))

theorem lrAct_mem_oneSet {m : Mor} {w : W} (hw : w ∈ B.oneSet) : E.lrAct m w ∈ B.oneSet := by
  have := B.paracompactSpace_pullback X.PMor X.src
  unfold lrAct
  split_ifs with h
  · exact E.isStrongBundleMap.mapsTo_oneSet
      ((B.mem_oneSet_pullback_iff X.isScSmoothMap_src _).2 hw)
  · exact hw

/-- **`v ↦ μ(a(v), b(v))` is sc-smooth** where `a`, `b` are and `P ∘ b = s ∘ a`. -/
theorem isScSmoothOn_lrAct {a : V → Mor} {b : V → W} {U : Set V}
    (ha : Q.IsScSmoothOn X.PMor a U) (hb : Q.IsScSmoothOn B.toMPolyfold0 b U)
    (hab : ∀ v ∈ U, P (b v) = X.src (a v)) :
    Q.IsScSmoothOn B.toMPolyfold0 (fun v => E.lrAct (a v) (b v)) U := by
  classical
  have := B.paracompactSpace_pullback X.PMor X.src
  let ι : V → pullbackSpace P X.src := fun v =>
    if h : P (b v) = X.src (a v) then ⟨(a v, b v), h⟩ else X.unitPair (b v)
  have hι := B.isScSmoothOn_to_pullback_of_eqOn X.isScSmoothMap_src (ι := ι) ha hb fun v hv => by
    simp only [ι, dif_pos (hab v hv)]
  refine (MPolyfold.IsScSmoothOn.comp E.isStrongBundleMap.isScSmoothMap hι
    (mapsTo_univ _ _)).congr fun v hv => ?_
  simp only [Function.comp_apply, ι, dif_pos (hab v hv), lrAct]

variable (E) in
/-- The level-`[1]` form of `lrAct`. -/
def lrActOne (m : Mor) (w : B.One) : B.One :=
  B.oneMk (E.lrAct m (B.oneVal w)) (lrAct_mem_oneSet (B.oneVal_mem w))

@[simp] theorem oneVal_lrActOne (m : Mor) (w : B.One) :
    B.oneVal (E.lrActOne m w) = E.lrAct m (B.oneVal w) := rfl

/-- **`v ↦ μ(a(v), b(v))` is sc-smooth at level `[1]`** where `a` and `b : V → W[1]` are and
`P ∘ b = s ∘ a`. -/
theorem isScSmoothOn_lrActOne {a : V → Mor} {b : V → B.One} {U : Set V}
    (ha : Q.IsScSmoothOn X.PMor a U) (hb : Q.IsScSmoothOn B.toMPolyfold1 b U)
    (hab : ∀ v ∈ U, P (B.oneVal (b v)) = X.src (a v)) :
    Q.IsScSmoothOn B.toMPolyfold1 (fun v => E.lrActOne (a v) (b v)) U := by
  classical
  have := B.paracompactSpace_pullback X.PMor X.src
  let ι : V → pullbackSpace P X.src := fun v =>
    if h : P (B.oneVal (b v)) = X.src (a v) then ⟨(a v, B.oneVal (b v)), h⟩
    else X.unitPair (B.oneVal (b v))
  have hι2 : ∀ v, (ι v : Mor × W).2 = B.oneVal (b v) := fun v => by
    dsimp only [ι]; split_ifs <;> rfl
  have hι1 : ∀ v, ι v ∈ (B.pullback X.isScSmoothMap_src).oneSet := fun v =>
    (B.mem_oneSet_pullback_iff X.isScSmoothMap_src _).2 (by rw [hι2]; exact B.oneVal_mem _)
  let ι₁ : V → (B.pullback X.isScSmoothMap_src).One := fun v =>
    (B.pullback X.isScSmoothMap_src).oneMk (ι v) (hι1 v)
  have ha' : Q.IsScSmoothOn X.PMor
      (pullbackProj P X.src ∘ (B.pullback X.isScSmoothMap_src).oneVal ∘ ι₁) U :=
    ha.congr fun v hv => by
      change a v = (ι v : Mor × W).1
      simp only [ι, dif_pos (hab v hv)]
  have hb' : Q.IsScSmoothOn B.toMPolyfold1 (B.pullbackProj'One X.isScSmoothMap_src ∘ ι₁) U :=
    hb.congr fun v _ => B.oneVal_injective (by
      change B.oneVal (b v) = (ι v : Mor × W).2
      rw [hι2])
  have hι₁ := B.isScSmoothOn_to_pullback_one X.isScSmoothMap_src ha' hb'
  refine (MPolyfold.IsScSmoothOn.comp E.isStrongBundleMap.isScSmoothMap_one hι₁
    (mapsTo_univ _ _)).congr fun v hv => B.oneVal_injective ?_
  change E.μ (ι v) = E.lrAct (a v) (B.oneVal (b v))
  simp only [ι, lrAct, dif_pos (hab v hv)]

end EpStrongBundle

end Act

/-! ### What Definition 8.4.2 gives on the base -/

section BaseConsequence

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

namespace EpStrongBundle

/-- **(LR) of the base for the liftable maps**: in the natural representations `U(x)` of
`IsLRLocal`, an sc-diffeomorphism `β` of `U(x)` covered by a strong bundle isomorphism `Φ` of
`W|U(x)` with `|Φ(w)| = |w|` is `ĝ` for some `g ∈ G_x` (evaluate `Φ = g ∗ ·` on the zero
section).  Definition 7.4.19 asks this of every orbit-preserving `β`, lifted or not. -/
theorem IsLRLocal.exists_base {E : EpStrongBundle X B} (h : E.IsLRLocal) (x : Obj)
    {O : Set Obj} (hO : IsOpen O) (hxO : x ∈ O) :
    ∃ R : X.NaturalRep x, R.U ⊆ O ∧ ∀ (β : Obj → Obj) (Φ : W → W), B.IsLocalIsoOn β Φ R.U →
      (∀ w, P w ∈ R.U → E.toGroupoidStr.π (Φ w) = E.toGroupoidStr.π w) →
      ∃ g : X.Isotropy x, ∀ y ∈ R.U, β y = R.Φ g y := by
  obtain ⟨R, hRO, hR⟩ := h x O hO hxO
  refine ⟨R, hRO, fun β Φ hΦ hπ => ?_⟩
  obtain ⟨g, hg⟩ := hR β Φ hΦ hπ
  refine ⟨g, fun y hy => ?_⟩
  have hw : P (fiberZero P y) ∈ R.U := by rw [isSection_fiberZero (P := P) y]; exact hy
  have h1 := hΦ.covers hw
  rw [hg _ hw] at h1
  unfold natLift at h1
  rw [E.P_μ, R.tgt_Γ g _ hw, isSection_fiberZero (P := P) y] at h1
  exact h1.symm

end EpStrongBundle

end BaseConsequence

/-! ### Proposition 10.4.7 with Definition 8.4.2 for the target -/

namespace SEP

open EpStrongBundle StrongBundle

variable {C A : SEP.{u}}

/-- **2021 Proposition 10.4.7, p. 501, on the bases, with Definition 8.4.2 for the target**: if
`F, G : W'' → W'` are strong bundle equivalences with `|F| = |G|` and `W'` has the local
regularity property (`IsLRLocal`), every object `x` of the base of `W''` has an open
neighbourhood `U` with an sc-smooth `U → 𝐗'`, `z ↦ α_z : ϕ_F(z) → ϕ_G(z)`.  Proof: with
`ψ₀ : ϕ_G(x) → ϕ_F(x)` and `Q = ψ̂₀ ∘ ϕ_G`, the map `γ = Q ∘ ϕ_F⁻¹` of a neighbourhood of
`ϕ_F(x)` preserves orbits and fixes `ϕ_F(x)`, and it is covered by the strong bundle isomorphism
`w ↦ μ'(ψ_{ϕ_F⁻¹(P'(w))}, G(F⁻¹(w)))` with `|B(w)| = |w|`; on `U(ϕ_F(x))` (Lemma 7.4.20) the
local regularity property makes `B = g ∗ ·`, hence `γ = ĝ`, and `α_z = ψ_z⁻¹ ∘ Γ(g, ϕ_F(z))`. -/
theorem exists_family_of_isLRLocal {F G : C ⟶ A} (hF : SEP.equivalences F)
    (hG : SEP.equivalences G) (hFG : (Hom.Φ F).orbitMap = (Hom.Φ G).orbitMap)
    (hA : A.E.IsLRLocal) (x : C.Obj) :
    ∃ U : Set C.Obj, IsOpen U ∧ x ∈ U ∧ ∃ α : C.Obj → A.Mor,
      C.X.PObj.IsScSmoothOn A.X.PMor α U ∧
      ∀ z ∈ U, A.X.src (α z) = (Hom.ϕ F).obj z ∧ A.X.tgt (α z) = (Hom.ϕ G).obj z := by
  have hsF := Hom.isStrongBundleFunctor F
  have hsG := Hom.isStrongBundleFunctor G
  have hπb : ∀ z, A.X.π ((Hom.ϕ F).obj z) = A.X.π ((Hom.ϕ G).obj z) := fun z => by
    rw [← (Hom.ϕ F).orbitMap_π, ← (Hom.ϕ G).orbitMap_π, orbitMap_base_eq hFG]
  have hπW : ∀ c, A.E.toGroupoidStr.π ((Hom.Φ F).obj c) =
      A.E.toGroupoidStr.π ((Hom.Φ G).obj c) := fun c => by
    have := congrFun hFG (C.E.toEpGroupoid.π c)
    rwa [GroupoidFunctor.orbitMap_π, GroupoidFunctor.orbitMap_π] at this
  -- `ψ₀ : ϕ_G(x) → ϕ_F(x)` and the chart `Q = ψ̂₀ ∘ ϕ_G` near `x`
  obtain ⟨ψ₀, hs₀, ht₀⟩ := A.X.π_eq_π_iff.1 (hπb x).symm
  obtain ⟨T, -⟩ := EpFunctor.exists_transportChart
    hG.isEquivalence_base.isLocalScDiffeo_obj hs₀ ht₀
  -- `F` and `G` are strong bundle isomorphisms near `x`
  obtain ⟨UF, UF', hxF, hiF⟩ := hF.isLocalStrongBundleIso_obj x
  obtain ⟨UG, UG', hxG, hiG⟩ := hG.isLocalStrongBundleIso_obj x
  obtain ⟨gF, hgF⟩ := hiF.isScDiffeoOn_base
  obtain ⟨gG, hgG⟩ := hiG.isScDiffeoOn_base
  obtain ⟨ΨF, hΨF⟩ := hiF.isScDiffeoOn_zero
  obtain ⟨ΨG, hΨG⟩ := hiG.isScDiffeoOn_zero
  obtain ⟨ΨF₁, hΨF₁⟩ := hiF.isScDiffeoOn_one
  obtain ⟨ΨG₁, hΨG₁⟩ := hiG.isScDiffeoOn_one
  -- `W₀ = U_F ∩ U_G ∩ W` and `D = U_F' ∩ g_F⁻¹(W₀)`
  have hW₀o : IsOpen (UF ∩ UG ∩ T.W) :=
    (hgF.isOpen_source.inter hgG.isOpen_source).inter T.isOpen_W
  have hDo : IsOpen (UF' ∩ gF ⁻¹' (UF ∩ UG ∩ T.W)) :=
    hgF.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage hgF.isOpen_target hW₀o
  have hxD : (Hom.ϕ F).obj x ∈ UF' ∩ gF ⁻¹' (UF ∩ UG ∩ T.W) :=
    ⟨hgF.mapsTo hxF, by rw [mem_preimage, hgF.left_inv x hxF]; exact ⟨⟨hxF, hxG⟩, T.mem_W⟩⟩
  -- the base map `γ = Q ∘ g_F` on `D`
  have h1 := hgF.symm.restrict hDo inter_subset_left
  have hsubW : UF ∩ (Hom.ϕ F).obj ⁻¹' (UF' ∩ gF ⁻¹' (UF ∩ UG ∩ T.W)) ⊆ T.W := fun z hz => by
    have h := hz.2.2
    rw [mem_preimage, hgF.left_inv z hz.1] at h
    exact h.2
  have hγ := (T.isScDiffeoOn_image h1.isOpen_target hsubW).comp h1
  obtain ⟨R, hRD, hRLR⟩ := hA _ _ hDo hxD
  have hγR := hγ.restrict R.isOpen_U hRD
  have e := hγR.image_eq
  rw [← e] at hγR
  have hγx : (T.Q ∘ gF) ((Hom.ϕ F).obj x) = (Hom.ϕ F).obj x := by
    rw [Function.comp_apply, hgF.left_inv x hxF, T.Q_self]
  have hγπ : ∀ y ∈ R.U, A.X.π ((T.Q ∘ gF) y) = A.X.π y := fun y hy => by
    have hy' := hRD hy
    rw [Function.comp_apply, T.π_Q hy'.2.2, ← hπb, hgF.right_inv y hy'.1]
  -- Lemma 7.4.20: `γ` is an sc-diffeomorphism of `U(ϕ_F(x))`
  obtain ⟨-, hγRR⟩ := A.X.lemma_7_4_20_2021 R hγR hγx hγπ
  have hQ : ∀ y ∈ R.U, T.Qinv y ∈ UF ∩ UG ∩ T.W ∧ T.Q (T.Qinv y) = y := fun y hy => by
    have h₁ := hγRR.mapsTo_inv hy
    have h₂ := hγRR.right_inv y hy
    have h₃ := (hRD h₁).2
    have h₄ : T.Qinv y = gF ((Hom.ϕ F).obj (T.Qinv y)) := by
      conv_lhs => rw [← h₂]
      exact T.isScDiffeoOn_Q.left_inv _ h₃.2
    rw [h₄]
    exact ⟨h₃, h₂⟩
  have hQW' : ∀ y ∈ R.U, y ∈ T.W' := fun y hy =>
    (hQ y hy).2 ▸ T.isScDiffeoOn_Q.mapsTo (hQ y hy).1.2
  -- the strong bundle isomorphism `B` of `W'|U(ϕ_F(x))` covering `γ`, and its inverse
  let a : A.W → A.Mor := fun w => T.ψ (gF (A.P w))
  let b : A.W → A.W := fun w => (Hom.Φ G).obj (ΨF w)
  let Bm : A.W → A.W := fun w => A.E.lrAct (a w) (b w)
  let a' : A.W → A.Mor := fun w => A.X.inv (T.ψ (T.Qinv (A.P w)))
  let Bm' : A.W → A.W := fun w => (Hom.Φ F).obj (ΨG (A.E.lrAct (a' w) w))
  have hPΨF : ∀ w, A.P w ∈ UF' → C.P (ΨF w) = gF (A.P w) := fun w hw =>
    IsStrongBundleIsoOn.P_inv (h := hsF.isStrongBundleMap_obj) hgF hΨF hw
  have hab : ∀ w, A.P w ∈ R.U → A.P (b w) = A.X.src (a w) := fun w hw => by
    have hw' := hRD hw
    show A.P ((Hom.Φ G).obj (ΨF w)) = A.X.src (T.ψ (gF (A.P w)))
    rw [hsG.isStrongBundleMap_obj.covers, hPΨF w hw'.1, T.src_ψ _ hw'.2.2]
  have hPBm : ∀ w, A.P w ∈ R.U → A.P (Bm w) = (T.Q ∘ gF) (A.P w) := fun w hw => by
    show A.P (A.E.lrAct (a w) (b w)) = _
    rw [P_lrAct (hab w hw)]
    exact T.tgt_ψ _ (hRD hw).2.2
  have hab' : ∀ w, A.P w ∈ R.U → A.P w = A.X.src (a' w) := fun w hw => by
    show A.P w = A.X.src (A.X.inv (T.ψ (T.Qinv (A.P w))))
    rw [A.X.src_inv, T.tgt_ψ _ (hQ _ hw).1.2, (hQ _ hw).2]
  have hPact' : ∀ w, A.P w ∈ R.U →
      A.P (A.E.lrAct (a' w) w) = (Hom.ϕ G).obj (T.Qinv (A.P w)) := fun w hw => by
    rw [P_lrAct (hab' w hw)]
    show A.X.tgt (A.X.inv (T.ψ (T.Qinv (A.P w)))) = _
    rw [A.X.tgt_inv, T.src_ψ _ (hQ _ hw).1.2]
  have hGUG' : ∀ w, A.P w ∈ R.U → A.P (A.E.lrAct (a' w) w) ∈ UG' := fun w hw => by
    rw [hPact' w hw]; exact hgG.mapsTo (hQ _ hw).1.1.2
  have hPΨG : ∀ w, A.P w ∈ R.U → C.P (ΨG (A.E.lrAct (a' w) w)) = T.Qinv (A.P w) := fun w hw => by
    rw [IsStrongBundleIsoOn.P_inv (h := hsG.isStrongBundleMap_obj) hgG hΨG (hGUG' w hw),
      hPact' w hw, hgG.left_inv _ (hQ _ hw).1.1.2]
  have hPBm' : ∀ w, A.P w ∈ R.U → A.P (Bm' w) = ((Hom.ϕ F).obj ∘ T.Qinv) (A.P w) :=
    fun w hw => by
      show A.P ((Hom.Φ F).obj _) = _
      rw [hsF.isStrongBundleMap_obj.covers, hPΨG w hw]; rfl
  -- level `[0]`
  have hUo : IsOpen (A.P ⁻¹' R.U) := R.isOpen_U.preimage A.B.continuous
  have hPs : A.B.toMPolyfold0.IsScSmoothOn A.X.PObj A.P (A.P ⁻¹' R.U) :=
    A.B.isScSmoothMap_proj.mono hUo (subset_univ _)
  have ha_s : A.B.toMPolyfold0.IsScSmoothOn A.X.PMor a (A.P ⁻¹' R.U) :=
    MPolyfold.IsScSmoothOn.comp T.isScSmoothOn_ψ
      (MPolyfold.IsScSmoothOn.comp hgF.isScSmoothOn_inv hPs fun w hw => (hRD hw).1)
      fun w hw => (hRD hw).2.2
  have hb_s : A.B.toMPolyfold0.IsScSmoothOn A.B.toMPolyfold0 b (A.P ⁻¹' R.U) :=
    MPolyfold.IsScSmoothOn.comp hsG.isStrongBundleMap_obj.isScSmoothMap
      (hΨF.isScSmoothOn_inv.mono hUo fun w hw => (hRD hw).1) (mapsTo_univ _ _)
  have hBm_s : A.B.toMPolyfold0.IsScSmoothOn A.B.toMPolyfold0 Bm (A.P ⁻¹' R.U) :=
    isScSmoothOn_lrAct ha_s hb_s hab
  have ha'_s : A.B.toMPolyfold0.IsScSmoothOn A.X.PMor a' (A.P ⁻¹' R.U) :=
    MPolyfold.IsScSmoothOn.comp A.X.isScSmoothMap_inv
      (MPolyfold.IsScSmoothOn.comp T.isScSmoothOn_ψ
        (MPolyfold.IsScSmoothOn.comp T.isScDiffeoOn_Q.isScSmoothOn_inv hPs
          fun w hw => hQW' _ hw) fun w hw => (hQ _ hw).1.2) (mapsTo_univ _ _)
  have hid_s : A.B.toMPolyfold0.IsScSmoothOn A.B.toMPolyfold0 id (A.P ⁻¹' R.U) :=
    MPolyfold.isScSmoothMap_id.mono hUo (subset_univ _)
  have hact'_s : A.B.toMPolyfold0.IsScSmoothOn A.B.toMPolyfold0
      (fun w => A.E.lrAct (a' w) (id w)) (A.P ⁻¹' R.U) :=
    isScSmoothOn_lrAct ha'_s hid_s fun w hw => hab' w hw
  have hBm'_s : A.B.toMPolyfold0.IsScSmoothOn A.B.toMPolyfold0 Bm' (A.P ⁻¹' R.U) :=
    MPolyfold.IsScSmoothOn.comp hsF.isStrongBundleMap_obj.isScSmoothMap
      (MPolyfold.IsScSmoothOn.comp hΨG.isScSmoothOn_inv hact'_s fun w hw => hGUG' w hw)
      (mapsTo_univ _ _)
  have hB0 : A.B.toMPolyfold0.IsScDiffeoOn A.B.toMPolyfold0 Bm Bm' (A.P ⁻¹' R.U)
      (A.P ⁻¹' R.U) := by
    refine ⟨hBm_s, hBm'_s, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
    · change A.P (Bm w) ∈ R.U
      rw [hPBm w hw]; exact hγRR.mapsTo hw
    · change A.P (Bm' w) ∈ R.U
      rw [hPBm' w hw]; exact hγRR.mapsTo_inv hw
    · have hw' := hRD hw
      have hQB : T.Qinv (A.P (Bm w)) = gF (A.P w) := by
        rw [hPBm w hw]; exact T.isScDiffeoOn_Q.left_inv _ hw'.2.2
      have h1 : A.E.lrAct (a' (Bm w)) (Bm w) = b w := by
        show A.E.lrAct (A.X.inv (T.ψ (T.Qinv (A.P (Bm w))))) (A.E.lrAct (a w) (b w)) = b w
        rw [hQB]; exact lrAct_inv_lrAct (hab w hw)
      show (Hom.Φ F).obj (ΨG (A.E.lrAct (a' (Bm w)) (Bm w))) = w
      rw [h1]
      show (Hom.Φ F).obj (ΨG ((Hom.Φ G).obj (ΨF w))) = w
      rw [hΨG.left_inv _ (show C.P (ΨF w) ∈ UG by rw [hPΨF w hw'.1]; exact hw'.2.1.2),
        hΨF.right_inv w hw'.1]
    · have hq := hQ _ hw
      have hv : C.P (ΨG (A.E.lrAct (a' w) w)) ∈ UF := by rw [hPΨG w hw]; exact hq.1.1.1
      have hgFB : gF (A.P (Bm' w)) = T.Qinv (A.P w) := by
        rw [hPBm' w hw]; exact hgF.left_inv _ hq.1.1.1
      have hbB : b (Bm' w) = A.E.lrAct (a' w) w := by
        show (Hom.Φ G).obj (ΨF ((Hom.Φ F).obj (ΨG (A.E.lrAct (a' w) w)))) = _
        rw [hΨF.left_inv _ hv, hΨG.right_inv _ (hGUG' w hw)]
      show A.E.lrAct (T.ψ (gF (A.P (Bm' w)))) (b (Bm' w)) = w
      rw [hgFB, hbB]
      exact lrAct_lrAct_inv (hab' w hw)
  -- level `[1]`
  let ΦG₁ := oneRestrict C.B A.B (Hom.Φ G).obj hsG.isStrongBundleMap_obj.mapsTo_oneSet
  let ΦF₁ := oneRestrict C.B A.B (Hom.Φ F).obj hsF.isStrongBundleMap_obj.mapsTo_oneSet
  let Bm₁ : A.B.One → A.B.One := fun y => A.E.lrActOne (a (A.B.oneVal y)) (ΦG₁ (ΨF₁ y))
  let Bm'₁ : A.B.One → A.B.One := fun y => ΦF₁ (ΨG₁ (A.E.lrActOne (a' (A.B.oneVal y)) y))
  have hΨF₁v : ∀ y : A.B.One, A.P (A.B.oneVal y) ∈ UF' →
      C.B.oneVal (ΨF₁ y) = ΨF (A.B.oneVal y) := fun y hy =>
    IsStrongBundleIsoOn.oneVal_inv (h := hsF.isStrongBundleMap_obj) hΨF hΨF₁ hy
  have hΨG₁v : ∀ y : A.B.One, A.P (A.B.oneVal y) ∈ UG' →
      C.B.oneVal (ΨG₁ y) = ΨG (A.B.oneVal y) := fun y hy =>
    IsStrongBundleIsoOn.oneVal_inv (h := hsG.isStrongBundleMap_obj) hΨG hΨG₁ hy
  have hBm₁v : ∀ y, A.P (A.B.oneVal y) ∈ R.U → A.B.oneVal (Bm₁ y) = Bm (A.B.oneVal y) :=
    fun y hy => by
      show A.E.lrAct (a (A.B.oneVal y)) (A.B.oneVal (ΦG₁ (ΨF₁ y))) =
        A.E.lrAct (a (A.B.oneVal y)) (b (A.B.oneVal y))
      rw [oneVal_oneRestrict, hΨF₁v y (hRD hy).1]
  have hBm'₁v : ∀ y, A.P (A.B.oneVal y) ∈ R.U → A.B.oneVal (Bm'₁ y) = Bm' (A.B.oneVal y) :=
    fun y hy => by
      show (Hom.Φ F).obj (C.B.oneVal (ΨG₁ (A.E.lrActOne (a' (A.B.oneVal y)) y))) =
        (Hom.Φ F).obj (ΨG (A.E.lrAct (a' (A.B.oneVal y)) (A.B.oneVal y)))
      rw [hΨG₁v _ (by rw [oneVal_lrActOne]; exact hGUG' _ hy), oneVal_lrActOne]
  have hU1o : IsOpen ((A.P ∘ A.B.oneVal) ⁻¹' R.U) :=
    R.isOpen_U.preimage (A.B.continuous.comp A.B.continuous_oneVal)
  have hov : A.B.toMPolyfold1.IsScSmoothOn A.B.toMPolyfold0 A.B.oneVal
      ((A.P ∘ A.B.oneVal) ⁻¹' R.U) :=
    A.B.isScSmoothMap_oneVal.mono hU1o (subset_univ _)
  have hBm₁_s : A.B.toMPolyfold1.IsScSmoothOn A.B.toMPolyfold1 Bm₁
      ((A.P ∘ A.B.oneVal) ⁻¹' R.U) := by
    refine isScSmoothOn_lrActOne
      (MPolyfold.IsScSmoothOn.comp (f := A.B.oneVal) (g := a) ha_s hov fun y hy => hy)
      (MPolyfold.IsScSmoothOn.comp hsG.isStrongBundleMap_obj.isScSmoothMap_one
        (hΨF₁.isScSmoothOn_inv.mono hU1o fun y hy => (hRD hy).1) (mapsTo_univ _ _))
      fun y hy => ?_
    show A.P (A.B.oneVal (ΦG₁ (ΨF₁ y))) = A.X.src (a (A.B.oneVal y))
    rw [oneVal_oneRestrict, hΨF₁v y (hRD hy).1]
    exact hab _ hy
  have hBm'₁_s : A.B.toMPolyfold1.IsScSmoothOn A.B.toMPolyfold1 Bm'₁
      ((A.P ∘ A.B.oneVal) ⁻¹' R.U) := by
    have hact'1 : A.B.toMPolyfold1.IsScSmoothOn A.B.toMPolyfold1
        (fun y => A.E.lrActOne ((a' ∘ A.B.oneVal) y) (id y)) ((A.P ∘ A.B.oneVal) ⁻¹' R.U) :=
      isScSmoothOn_lrActOne
        (MPolyfold.IsScSmoothOn.comp (f := A.B.oneVal) (g := a') ha'_s hov fun y hy => hy)
        (MPolyfold.isScSmoothMap_id.mono hU1o (subset_univ _)) fun y hy => hab' _ hy
    exact MPolyfold.IsScSmoothOn.comp hsF.isStrongBundleMap_obj.isScSmoothMap_one
      (MPolyfold.IsScSmoothOn.comp hΨG₁.isScSmoothOn_inv hact'1 fun y hy => by
        show A.P (A.B.oneVal (A.E.lrActOne _ _)) ∈ UG'
        rw [oneVal_lrActOne]; exact hGUG' _ hy) (mapsTo_univ _ _)
  have hB1 := isScDiffeoOn_one_of hB0 hBm₁v hBm'₁v hBm₁_s hBm'₁_s
  -- linearity on the fibres
  have hlin : ∀ y ∈ R.U, ∃ L : A.P ⁻¹' {y} →ₗ[ℝ] A.P ⁻¹' {(T.Q ∘ gF) y},
      ∀ v, (L v : A.W) = Bm v := by
    intro y hy
    have hy' := hRD hy
    obtain ⟨L₁, hL₁⟩ := hiF.exists_linear_inv hgF hΨF hy'.1
    have hs : (Hom.ϕ G).obj (gF y) = A.X.src (T.ψ (gF y)) := (T.src_ψ _ hy'.2.2).symm
    have ht : A.X.tgt (T.ψ (gF y)) = (T.Q ∘ gF) y := T.tgt_ψ _ hy'.2.2
    refine ⟨(fiberCast A.P ht).comp ((A.E.fiberMor (T.ψ (gF y))).toLinearMap.comp
      ((fiberCast A.P hs).comp ((hsG.isStrongBundleMap_obj.fiberLinearMap (gF y)).comp L₁))),
      fun v => ?_⟩
    have hv : A.P (v : A.W) = y := v.2
    have hvU : A.P (v : A.W) ∈ R.U := by rw [hv]; exact hy
    rw [show Bm v = A.E.μ ⟨(a v, b v), hab v hvU⟩ from lrAct_eq (hab v hvU)]
    simp only [LinearMap.coe_comp, Function.comp_apply, fiberCast_val,
      ContinuousLinearMap.coe_coe, fiberMor_apply]
    refine A.E.μ_congr (Prod.ext ?_ ?_)
    · show T.ψ (gF y) = T.ψ (gF (A.P v)); rw [hv]
    · show (Hom.Φ G).obj (L₁ v : C.W) = (Hom.Φ G).obj (ΨF v); rw [hL₁]
  -- orbits
  have hπB : ∀ w, A.P w ∈ R.U → A.E.toGroupoidStr.π (Bm w) = A.E.toGroupoidStr.π w :=
    fun w hw => by
      show A.E.toGroupoidStr.π (A.E.lrAct (a w) (b w)) = _
      rw [π_lrAct (hab w hw)]
      show A.E.toGroupoidStr.π ((Hom.Φ G).obj (ΨF w)) = _
      rw [← hπW, hΨF.right_inv w (hRD hw).1]
  -- Definition 8.4.2: `B = g ∗ ·`, hence `γ = ĝ`
  obtain ⟨k, hk⟩ := hRLR (T.Q ∘ gF) Bm ⟨hlin, ⟨_, hγRR⟩, ⟨_, hB0⟩, ⟨Bm₁, Bm'₁, hBm₁v, hB1⟩⟩ hπB
  have hγk : ∀ y ∈ R.U, T.Q (gF y) = R.Φ k y := fun y hy => by
    have hw : A.P (fiberZero A.P y) ∈ R.U := by rw [isSection_fiberZero (P := A.P) y]; exact hy
    have h1 := congrArg A.P (hk _ hw)
    have h2 : A.P (A.E.natLift R k _ hw) = R.Φ k (A.P (fiberZero A.P y)) := by
      unfold EpStrongBundle.natLift
      rw [A.E.P_μ]
      exact R.tgt_Γ k _ hw
    rw [h2, hPBm _ hw, isSection_fiberZero (P := A.P) y] at h1
    exact h1
  -- the family `α_z = ψ_z⁻¹ ∘ Γ(g, ϕ_F(z))`
  have hVo : IsOpen (UF ∩ (Hom.ϕ F).obj ⁻¹' R.U) :=
    hgF.isScSmoothOn.continuousOn.isOpen_inter_preimage hgF.isOpen_source R.isOpen_U
  have hzT : ∀ z ∈ UF ∩ (Hom.ϕ F).obj ⁻¹' R.U,
      z ∈ T.W ∧ T.Q z = R.Φ k ((Hom.ϕ F).obj z) := fun z hz => by
    have h := (hRD hz.2).2
    rw [mem_preimage, hgF.left_inv z hz.1] at h
    refine ⟨h.2, ?_⟩
    have := hγk _ hz.2
    rwa [hgF.left_inv z hz.1] at this
  have hc : ∀ z ∈ UF ∩ (Hom.ϕ F).obj ⁻¹' R.U,
      A.X.src (A.X.inv (T.ψ z)) = A.X.tgt (R.Γ k ((Hom.ϕ F).obj z)) := fun z hz => by
    rw [A.X.src_inv, T.tgt_ψ z (hzT z hz).1, (hzT z hz).2, R.tgt_Γ k _ hz.2]
  refine ⟨_, hVo, ⟨hxF, R.mem_U⟩,
    fun z => A.X.comp (A.X.inv (T.ψ z)) (R.Γ k ((Hom.ϕ F).obj z)), ?_, fun z hz => ⟨?_, ?_⟩⟩
  · exact A.X.isScSmoothOn_comp_of
      (MPolyfold.IsScSmoothOn.comp A.X.isScSmoothMap_inv
        (T.isScSmoothOn_ψ.mono hVo fun z hz => (hzT z hz).1) (mapsTo_univ _ _))
      (MPolyfold.IsScSmoothOn.comp (R.isScSmoothOn_Γ k)
        ((Hom.ϕ F).isScSmoothMap_obj.mono hVo (subset_univ _)) fun z hz => hz.2) hc
  · rw [A.X.src_comp _ _ (hc z hz), R.src_Γ k _ hz.2]
  · rw [A.X.tgt_comp _ _ (hc z hz), A.X.tgt_inv, T.src_ψ z (hzT z hz).1]

end SEP

/-! ### Natural equivalence from local families over an effective target -/

section Effective

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- **A natural transformation from local families over an effective target**
(`EpFunctor.naturallyEquivalent_of_isEffective` with the families of Proposition 10.1.10 (1) as
the hypothesis in place of (LR)): if `H` is an equivalence, `Y` is effective and every `x` has an
open neighbourhood with a continuous family `α_z : H(z) → H'(z)`, then `H ≃ H'`. -/
theorem EpFunctor.naturallyEquivalent_of_isEffective_of_families {H H' : EpFunctor X Y}
    (hH : H.IsEquivalence) (hY : Y.IsEffective)
    (hfam : ∀ x, ∃ U : Set Obj, IsOpen U ∧ x ∈ U ∧ ∃ α : Obj → Mor',
      X.PObj.IsScSmoothOn Y.PMor α U ∧ ∀ z ∈ U, Y.src (α z) = H.obj z ∧ Y.tgt (α z) = H'.obj z) :
    H.NaturallyEquivalent H' := by
  choose U hU hxU α hα hαst using hfam
  set a : Obj → Mor' := fun z => α z z
  have hloc : ∀ x, ∀ z ∈ U x, a z = α x z := fun x z hz =>
    EpFunctor.eqOn_of_isEffective hH.isLocalScDiffeo_obj hY ((hU z).inter (hU x))
      ((hα z).continuousOn.mono inter_subset_left) ((hα x).continuousOn.mono inter_subset_right)
      (fun w hw => (hαst z w hw.1).1) (fun w hw => (hαst z w hw.1).2)
      (fun w hw => (hαst x w hw.2).1) (fun w hw => (hαst x w hw.2).2) ⟨hxU z, hz⟩
  have hsa : ∀ z, Y.src (a z) = H.obj z := fun z => (hαst z z (hxU z)).1
  have hta : ∀ z, Y.tgt (a z) = H'.obj z := fun z => (hαst z z (hxU z)).2
  have hsm : X.PObj.IsScSmoothMap Y.PMor a :=
    MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x _ => ⟨U x, hU x, hxU x, subset_univ _,
      (hα x).congr fun z hz => (hloc x z hz).symm⟩
  have hca : Continuous a := continuousOn_univ.1 hsm.continuousOn
  refine ⟨⟨a, hsm, hsa, hta, fun h => ?_⟩⟩
  obtain ⟨N, S, σ, hN, hσ⟩ := X.isLocalScDiffeo_src h
  have hσS : ∀ z ∈ S, X.src (σ z) = z := hσ.right_inv
  have hσc : ContinuousOn σ S := hσ.isScSmoothOn_inv.continuousOn
  have hSa : X.src h ∈ S := hσ.mapsTo hN
  have hσh : σ (X.src h) = h := hσ.left_inv h hN
  have hc1 : ∀ φ, Y.src (Y.inv (H'.mor φ)) = Y.tgt (a (X.tgt φ)) := fun φ => by
    rw [Y.src_inv, H'.tgt_mor, hta]
  have hc2 : ∀ φ, Y.src (Y.comp (Y.inv (H'.mor φ)) (a (X.tgt φ))) = Y.tgt (H.mor φ) :=
    fun φ => by rw [Y.src_comp _ _ (hc1 φ), hsa, H.tgt_mor]
  have hβ : ContinuousOn (fun z => Y.comp (Y.comp (Y.inv (H'.mor (σ z))) (a (X.tgt (σ z))))
      (H.mor (σ z))) S :=
    Y.continuousOn_comp_of (Y.continuousOn_comp_of
      (Y.continuous_inv.comp_continuousOn (H'.continuous_mor.comp_continuousOn hσc))
      (hca.comp_continuousOn (X.continuous_tgt.comp_continuousOn hσc)) fun z _ => hc1 (σ z))
      (H.continuous_mor.comp_continuousOn hσc) fun z _ => hc2 (σ z)
  have he := EpFunctor.eqOn_of_isEffective hH.isLocalScDiffeo_obj hY hσ.isOpen_target
    hca.continuousOn hβ (fun z _ => hsa z) (fun z _ => hta z)
    (fun z hz => by rw [Y.src_comp _ _ (hc2 (σ z)), H.src_mor, hσS z hz])
    (fun z hz => by
      rw [Y.tgt_comp _ _ (hc2 (σ z)), Y.tgt_comp _ _ (hc1 (σ z)), Y.tgt_inv, H'.src_mor,
        hσS z hz]) hSa
  simp only [hσh] at he
  have hcan := GroupoidStr.inv_comp_cancel_left (G := Y.toGroupoidStr)
    (φ := Y.inv (H'.mor h)) (ψ := Y.comp (a (X.tgt h)) (H.mor h))
    (by rw [Y.src_inv, Y.tgt_comp _ _ (by rw [hsa, H.tgt_mor]), H'.tgt_mor, hta])
  rw [GroupoidStr.inv_inv] at hcan
  rw [he, Y.comp_assoc _ _ _ (hc1 h) (by rw [hsa, H.tgt_mor])]
  exact hcan.symm

end Effective

namespace SEP

open EpStrongBundle

variable {C A : SEP.{u}}

/-- **Natural equivalence of strong bundle equivalences over an effective base, from Definition
8.4.2 for the target** (`SEP.natEquiv_of_isEffective` with `IsLRLocal` of `W'` in place of (LR)
of the base of `W''`): if `F, G : W'' → W'` are strong bundle equivalences with `|F| = |G|`, `W'`
has the local regularity property and its base `X'` is effective, then `F ≃ G`. -/
theorem natEquiv_of_isEffective_of_isLRLocal {F G : C ⟶ A} (hF : SEP.equivalences F)
    (hG : SEP.equivalences G) (hFG : (Hom.Φ F).orbitMap = (Hom.Φ G).orbitMap)
    (hLR : A.E.IsLRLocal) (hA : A.X.IsEffective) : SEP.NatEquiv F G := by
  obtain ⟨τ⟩ := EpFunctor.naturallyEquivalent_of_isEffective_of_families
    hF.isEquivalence_base hA (exists_family_of_isLRLocal hF hG hFG hLR)
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

/-! ### Theorem 10.5.7 for an effective target, from Definition 8.4.2 -/

namespace SBLocalization

open SEP

/-- **2021 Theorem 10.5.7, p. 508 (2017: Theorem 10.10), for an effective target, from
Definition 8.4.2 alone**: if the target `W'` has the local regularity property, read with strong
bundle isomorphisms of `W'|U(x)` (`EpStrongBundle.IsLRLocal`), and its base `X'` is effective,
generalized strong bundle isomorphisms `[D], [D'] : W → W'` with `|[D]| = |[D']|` are equal.  No
(LR) of a base ep-groupoid is assumed.  Proof: as `theorem_10_5_7_of_isEffective`, with
`SEP.natEquiv_of_isEffective_of_isLRLocal` for the functors `Ψ ∘ ΠX, Ψ' ∘ ΠZ` from the weak
fibred product into `W'`. -/
theorem theorem_10_5_7_of_isEffective_of_isLRLocal {A A' : SEP.{u}} (hA' : A'.E.IsLRLocal)
    (hEff : A'.X.IsEffective) {f f' : GenSBMap A A'} (hf : f.IsGeneralizedIso)
    (hf' : f'.IsGeneralizedIso) (h : f.orbitMap = f'.orbitMap) : f = f' := by
  obtain ⟨D, rfl, hΨ⟩ := hf
  obtain ⟨D', rfl, hΨ'⟩ := hf'
  have h' : D.orbitMap = D'.orbitMap := h
  -- the weak fibred product `W'' ×_W V''` of `Φ` and `Φ'`
  obtain ⟨hZ, hnat, -, -⟩ := SBWeakFibredProduct.theorem_10_2_2 D.isEquivalence_Φ D'.Φ
  have hX := SBWeakFibredProduct.theorem_10_2_2_right D.isEquivalence_Φ D'.Φ D'.isEquivalence_Φ
  set pX := SBWeakFibredProduct.projX D.isEquivalence_Φ D'.Φ
  set pZ := SBWeakFibredProduct.projZ D.isEquivalence_Φ D'.Φ
  have hXΨ := SEP.equivalences.comp_mem _ _ hX hΨ
  have hZΨ := SEP.equivalences.comp_mem _ _ hZ hΨ'
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
  have key := SEP.natEquiv_of_isEffective_of_isLRLocal hXΨ hZΨ horb hA' hEff
  exact SDiagram.cls_eq_cls_of_equiv ⟨D.precomp pX hX, D.isRefinement_precomp pX hX,
    ⟨pZ, hZ, hnat.symm, key.symm⟩⟩

/-- **Theorem 10.5.7 for an effective target, with the text's hypotheses**: both strong bundles
have the local regularity property (Definition 8.4.2, as `IsLRLocal`) and the base of the target
is effective.  Only the hypothesis on the target is used. -/
theorem theorem_10_5_7_of_isEffective_of_isLRLocal' {A A' : SEP.{u}} (_hA : A.E.IsLRLocal)
    (hA' : A'.E.IsLRLocal) (hEff : A'.X.IsEffective) {f f' : GenSBMap A A'}
    (hf : f.IsGeneralizedIso) (hf' : f'.IsGeneralizedIso) (h : f.orbitMap = f'.orbitMap) :
    f = f' :=
  theorem_10_5_7_of_isEffective_of_isLRLocal hA' hEff hf hf' h

end SBLocalization

/-! ### Witnesses; effectiveness is still needed -/

namespace LocalizationLRBundleBaseExamples

open StrongBundleEquivalenceExamples StrongBundleLocalizationExamples SBLocalization
  EpGroupoid.Examples

/-- **Witness** for `SBLocalization.theorem_10_5_7_of_isEffective_of_isLRLocal` (and its primed
form), `SEP.natEquiv_of_isEffective_of_isLRLocal` and `SEP.exists_family_of_isLRLocal`: for
`W = ℝⁿ × ℝᵏ → ℝⁿ` over the trivial ep-groupoid of `ℝⁿ` (`epSEP n k`), the bundle has the local
regularity property in the sense of `IsLRLocal`, the base is effective, `1_W` is a strong bundle
equivalence and `[1_W]` is a generalized strong bundle isomorphism. -/
theorem theorem_10_5_7_of_isEffective_of_isLRLocal_hypotheses (n k : ℕ) :
    (epSEP n k).E.IsLRLocal ∧ (epSEP n k).X.IsEffective ∧ SEP.equivalences (𝟙 (epSEP n k)) ∧
      (SDiagram.id (epSEP n k)).cls.IsGeneralizedIso :=
  ⟨EpStrongBundle.isLRLocal_trivial _, EpGroupoid.isEffective_trivial _,
    SEP.equivalences.id_mem _, ⟨SDiagram.id _, rfl, SEP.equivalences.id_mem _⟩⟩

/-- **Witness** for `EpFunctor.naturallyEquivalent_of_isEffective_of_families`: `H = H' = 1` on
the point ep-groupoid, with the units as the families. -/
theorem naturallyEquivalent_of_isEffective_of_families_hypotheses :
    (EpFunctor.id pointEP.X).IsEquivalence ∧ pointEP.X.IsEffective ∧
      ∀ x, ∃ U : Set pointEP.Obj, IsOpen U ∧ x ∈ U ∧ ∃ α : pointEP.Obj → pointEP.Mor,
        pointEP.X.PObj.IsScSmoothOn pointEP.X.PMor α U ∧ ∀ z ∈ U,
          pointEP.X.src (α z) = (EpFunctor.id pointEP.X).obj z ∧
            pointEP.X.tgt (α z) = (EpFunctor.id pointEP.X).obj z :=
  ⟨EpFunctor.IsEquivalence.id _, EquivalenceLREffectiveExamples.isEffective_pointEP, fun x =>
    ⟨univ, isOpen_univ, mem_univ x, pointEP.X.unit, pointEP.X.isScSmoothMap_unit,
      fun z _ => ⟨pointEP.X.src_unit z, pointEP.X.tgt_unit z⟩⟩⟩

/-- **The strong bundle `ℝ × ℝᵏ → ℝ` over `ℤ/3 × ℝ ⇉ ℝ` (trivial `μ`) has the local regularity
property in the sense of `IsLRLocal`**: its orbits are points. -/
theorem isLRLocal_z3EpBundle (k : ℕ) : (z3EpBundle k).IsLRLocal := by
  intro x O hO hxO
  obtain ⟨R, hRO⟩ := trivialZ3EpGroupoid.theorem_7_1 x hO hxO
  refine ⟨R, hRO, fun β Φ _ hπ => ⟨1, fun w hw => ?_⟩⟩
  obtain ⟨q, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 (hπ w hw)
  exact h1.symm.trans h2

/-- **Theorem 10.5.7 with Definition 8.4.2 read as `IsLRLocal`, without effectiveness, does not
hold as we read it**: the example of `LocalizationLRCounterexample.not_theorem_10_5_7` (Remark
10.5.5, base `ℤ/3 × ℝ ⇉ ℝ`, not effective) has `IsLRLocal`.  So the effectiveness hypothesis of
`theorem_10_5_7_of_isEffective_of_isLRLocal` is not removed by the reading of Definition 8.4.2. -/
theorem not_theorem_10_5_7_of_isLRLocal :
    ¬ ∀ A A' : SEP.{0}, A.E.IsLRLocal → A'.E.IsLRLocal → ∀ f f' : GenSBMap A A',
      f.IsGeneralizedIso → f'.IsGeneralizedIso → f.orbitMap = f'.orbitMap → f = f' := fun h =>
  (remark_10_5_5 0).2.2.2.2 (h _ _ (isLRLocal_z3EpBundle 0) (isLRLocal_z3EpBundle 0) _ _
    (remark_10_5_5 0).1 (remark_10_5_5 0).2.1 (remark_10_5_5 0).2.2.1)

end LocalizationLRBundleBaseExamples

end Polyfold
