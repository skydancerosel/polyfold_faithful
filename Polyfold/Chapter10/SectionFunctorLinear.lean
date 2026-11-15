import Polyfold.Chapter10.StrongBundleLocalizationSections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, **Theorem 10.4.5** (pp. 500–501; 2017: Theorem 10.8, p. 362) and
**Theorem 10.5.4** (pp. 507–508; 2017: Theorem 10.9, p. 367): the push-forwards are linear.

# Push-forward and pull-back of section functors are linear isomorphisms

## The text, paraphrased

(Definition 8.3.4) `Γ(P, μ)` is the vector space of sc-smooth section functors, `Γ⁺(P, μ)` the
subspace of sc⁺-section functors.  (Theorem 10.4.5) For a strong bundle equivalence `Φ`,
`Φ_* : Γ(P, μ) → Γ(P', μ')` is a bijection with inverse `Φ^*`.  (Theorem 10.5.4) For a
generalized strong bundle isomorphism `[D]`, `[D]_* : Γ(P, μ) → Γ(P', μ')` is a well-defined
isomorphism with inverse `[D]^*`, and the same for `Γ⁺`.

## What is formalized

`Chapter10/StrongBundleLocalizationSections.lean` proves the bijections (`theorem_10_5_4`); this
file adds the linear structure.
* Pointwise linearity, for all sections (no functoriality needed):
  `IsStrongBundleEquivalence.pullback_sectionAdd`, `pullback_sectionSmul`,
  `pushforward_sectionAdd`, `pushforward_sectionSmul`; along diagrams
  `SDiagram.pushforward_sectionAdd`, `…_sectionSmul`, `SDiagram.pullback_sectionAdd`,
  `…_sectionSmul`; for classes `GenSBMap.pushforward_sectionAdd`, … .
* The vector spaces: `EpStrongBundle.sectionSpace E`, `plusSectionSpace E` (`Γ(P, μ)`, `Γ⁺(P, μ)`
  as submodules of `Π x, W_x`; `mem_sectionSpace_iff`).
* **Theorem 10.5.4, "isomorphism"**: `GenSBMap.pushforwardEquiv hf : Γ(P, μ) ≃ₗ[ℝ] Γ(P', μ')`
  (`pushforwardEquiv_apply`, `pushforwardEquiv_symm_apply`: the inverse is `[D]^*`), and
  `plusPushforwardEquiv hf : Γ⁺(P, μ) ≃ₗ[ℝ] Γ⁺(P', μ')`.

## Choices

* `Γ(P, μ)` is a set of maps `X → W` in the project; here it is also realised as a submodule of
  `Π x, W_x` (a section `s` corresponds to `x ↦ s(x)`), which carries the vector space structure
  of Definition 8.3.4.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function

noncomputable section

namespace Polyfold

universe u

/-! ### Changing the fibre index of a sum -/

section Cast

variable {X Y : Type*} {P : Y → X} [∀ x, AddCommGroup (P ⁻¹' {x})]

/-- The sum of two points of a fibre does not depend on how the fibre is indexed. -/
theorem fiber_add_val_congr {a b : X} (e : a = b) {w₁ w₂ : Y} (h₁ : P w₁ = a) (h₂ : P w₂ = a) :
    (((⟨w₁, h₁⟩ : P ⁻¹' {a}) + ⟨w₂, h₂⟩ : P ⁻¹' {a}) : Y) =
      (((⟨w₁, h₁.trans e⟩ : P ⁻¹' {b}) + ⟨w₂, h₂.trans e⟩ : P ⁻¹' {b}) : Y) := by
  subst e; rfl

/-- The scalar multiple of a point of a fibre does not depend on how the fibre is indexed. -/
theorem fiber_smul_val_congr [∀ x, Module ℝ (P ⁻¹' {x})] {a b : X} (e : a = b) (c : ℝ) {w : Y}
    (h : P w = a) :
    ((c • (⟨w, h⟩ : P ⁻¹' {a}) : P ⁻¹' {a}) : Y) =
      ((c • (⟨w, h.trans e⟩ : P ⁻¹' {b}) : P ⁻¹' {b}) : Y) := by
  subst e; rfl

variable [∀ x, Module ℝ (P ⁻¹' {x})]

/-- An element of `Π x, Y_x` as a section `X → Y`. -/
def piToSection (s : ∀ x, P ⁻¹' {x}) : X → Y := fun x => s x

theorem isSection_piToSection (s : ∀ x, P ⁻¹' {x}) : IsSection P (piToSection s) := fun x => (s x).2

theorem piToSection_injective : Injective (piToSection (P := P)) := fun _ _ h =>
  funext fun x => Subtype.ext (congrFun h x)

theorem piToSection_zero : piToSection (0 : ∀ x, P ⁻¹' {x}) = fiberZero P := rfl

theorem piToSection_add (s t : ∀ x, P ⁻¹' {x}) :
    piToSection (s + t) = sectionAdd P (piToSection s) (piToSection t) :=
  funext fun x => (sectionAdd_apply (isSection_piToSection s) (isSection_piToSection t) x).symm

theorem piToSection_smul (c : ℝ) (s : ∀ x, P ⁻¹' {x}) :
    piToSection (c • s) = sectionSmul P (fun _ => c) (piToSection s) :=
  funext fun x => (sectionSmul_apply (f := fun _ => c) (isSection_piToSection s) x).symm

/-- A section `f` as an element of `Π x, Y_x`. -/
def sectionToPi (f : X → Y) (hf : IsSection P f) : ∀ x, P ⁻¹' {x} := fun x => ⟨f x, hf x⟩

@[simp] theorem piToSection_sectionToPi (f : X → Y) (hf : IsSection P f) :
    piToSection (sectionToPi f hf) = f := rfl

/-- **The subspace of `Π x, Y_x` given by a set of sections** closed under the zero section, sums
and scalar multiples (the vector space structure of Definition 8.3.4). -/
def sectionSubmodule (S : Set (X → Y)) (h0 : fiberZero P ∈ S)
    (hadd : ∀ {f g}, f ∈ S → g ∈ S → sectionAdd P f g ∈ S)
    (hsmul : ∀ (c : ℝ) {f}, f ∈ S → sectionSmul P (fun _ => c) f ∈ S) :
    Submodule ℝ (∀ x, P ⁻¹' {x}) where
  carrier := {s | piToSection s ∈ S}
  zero_mem' := h0
  add_mem' {s t} hs ht := by
    change piToSection (s + t) ∈ S
    rw [piToSection_add]; exact hadd hs ht
  smul_mem' c s hs := by
    change piToSection (c • s) ∈ S
    rw [piToSection_smul]; exact hsmul c hs

end Cast

section Functors

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

namespace EpStrongBundle

variable (E) in
/-- **`Γ(P, μ)` as a vector space** (2021 Definition 8.3.4 (1)): the sc-smooth section functors,
as a subspace of `Π x, W_x`. -/
def sectionSpace : Submodule ℝ (∀ x, P ⁻¹' {x}) :=
  sectionSubmodule E.sectionFunctors E.fiberZero_mem_sectionFunctors
    E.sectionAdd_mem_sectionFunctors fun c _ hf => E.sectionSmul_mem_sectionFunctors c hf

variable (E) in
/-- **`Γ⁺(P, μ)` as a vector space** (2021 Definition 8.3.4 (2)). -/
def plusSectionSpace : Submodule ℝ (∀ x, P ⁻¹' {x}) :=
  sectionSubmodule E.plusSectionFunctors E.fiberZero_mem_plusSectionFunctors
    E.sectionAdd_mem_plusSectionFunctors
    fun c _ hf => E.sectionSmul_mem_plusSectionFunctors c hf

theorem mem_sectionSpace_iff {s : ∀ x, P ⁻¹' {x}} :
    s ∈ E.sectionSpace ↔ piToSection s ∈ E.sectionFunctors := Iff.rfl

theorem mem_plusSectionSpace_iff {s : ∀ x, P ⁻¹' {x}} :
    s ∈ E.plusSectionSpace ↔ piToSection s ∈ E.plusSectionFunctors := Iff.rfl

theorem plusSectionSpace_le : E.plusSectionSpace ≤ E.sectionSpace :=
  fun _ hs => E.plusSectionFunctors_subset hs

namespace IsStrongBundleEquivalence

variable {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (h : E.IsStrongBundleEquivalence E' ϕ Φ)
include h

/-! ### Linearity of `Φ^*` and `Φ_*` -/

/-- `Φ^*(f' + g') = Φ^* f' + Φ^* g'`. -/
theorem pullback_sectionAdd {f' g' : Obj' → W'} (hf' : IsSection P' f') (hg' : IsSection P' g') :
    h.pullback (sectionAdd P' f' g') = sectionAdd P (h.pullback f') (h.pullback g') := by
  funext x
  rw [sectionAdd_apply (h.isSection_pullback f') (h.isSection_pullback g')]
  have ha : h.fiberEquiv x ⟨h.pullback f' x, h.P_pullback f' x⟩ = ⟨f' (ϕ.obj x), hf' _⟩ :=
    Subtype.ext (h.obj_pullback hf' x)
  have hb : h.fiberEquiv x ⟨h.pullback g' x, h.P_pullback g' x⟩ = ⟨g' (ϕ.obj x), hg' _⟩ :=
    Subtype.ext (h.obj_pullback hg' x)
  let a : P ⁻¹' {x} := ⟨h.pullback f' x, h.P_pullback f' x⟩
  let b : P ⁻¹' {x} := ⟨h.pullback g' x, h.P_pullback g' x⟩
  refine h.pullback_eq (hf'.sectionAdd hg') (a + b).2 ?_
  rw [sectionAdd_apply hf' hg', ← ha, ← hb, ← map_add]
  rfl

/-- `Φ^*(c · f') = c · Φ^* f'`. -/
theorem pullback_sectionSmul (c : ℝ) {f' : Obj' → W'} (hf' : IsSection P' f') :
    h.pullback (sectionSmul P' (fun _ => c) f') = sectionSmul P (fun _ => c) (h.pullback f') := by
  funext x
  rw [sectionSmul_apply (h.isSection_pullback f')]
  have ha : h.fiberEquiv x ⟨h.pullback f' x, h.P_pullback f' x⟩ = ⟨f' (ϕ.obj x), hf' _⟩ :=
    Subtype.ext (h.obj_pullback hf' x)
  let a : P ⁻¹' {x} := ⟨h.pullback f' x, h.P_pullback f' x⟩
  refine h.pullback_eq hf'.sectionSmul (c • a).2 ?_
  rw [sectionSmul_apply hf', ← ha, ← map_smul]
  rfl

/-- `Φ(f(y) + g(y))`, as a sum in the fibre over `s(σ)` for `s(σ) = ϕ(y)`. -/
theorem obj_sectionAdd_eq {f g : Obj → W} (hf : IsSection P f) (hg : IsSection P g) {y : Obj}
    {σ : Mor'} (hs : X'.src σ = ϕ.obj y) (hfs : P' (Φ.obj (f y)) = X'.src σ)
    (hgs : P' (Φ.obj (g y)) = X'.src σ) :
    Φ.obj (sectionAdd P f g y) =
      (((⟨Φ.obj (f y), hfs⟩ : P' ⁻¹' {X'.src σ}) + ⟨Φ.obj (g y), hgs⟩ :
        P' ⁻¹' {X'.src σ}) : W') := by
  rw [sectionAdd_apply hf hg, ← h.fiberEquiv_apply, map_add]
  exact fiber_add_val_congr (P := P') hs.symm (w₁ := Φ.obj (f y)) (w₂ := Φ.obj (g y))
    (hfs.trans hs) (hgs.trans hs)

/-- `Φ(c · f(y))`, as a multiple in the fibre over `s(σ)` for `s(σ) = ϕ(y)`. -/
theorem obj_sectionSmul_eq (c : ℝ) {f : Obj → W} (hf : IsSection P f) {y : Obj} {σ : Mor'}
    (hs : X'.src σ = ϕ.obj y) (hfs : P' (Φ.obj (f y)) = X'.src σ) :
    Φ.obj (sectionSmul P (fun _ => c) f y) =
      ((c • (⟨Φ.obj (f y), hfs⟩ : P' ⁻¹' {X'.src σ}) : P' ⁻¹' {X'.src σ}) : W') := by
  rw [sectionSmul_apply hf, ← h.fiberEquiv_apply, map_smul]
  exact fiber_smul_val_congr (P := P') hs.symm c (w := Φ.obj (f y)) (hfs.trans hs)

/-- `Φ_*(f + g) = Φ_* f + Φ_* g`: `μ'(σ, Φ(f(x) + g(x))) = μ'(σ, Φ(f(x))) + μ'(σ, Φ(g(x)))`. -/
theorem pushforward_sectionAdd {f g : Obj → W} (hf : IsSection P f) (hg : IsSection P g) :
    h.pushforward (sectionAdd P f g) = sectionAdd P' (h.pushforward f) (h.pushforward g) := by
  funext x'
  have hs := h.src_preMor x'
  have ht := h.tgt_preMor x'
  have hfs : P' (Φ.obj (f (h.preObj x'))) = X'.src (h.preMor x') := by rw [h.covers, hf, hs]
  have hgs : P' (Φ.obj (g (h.preObj x'))) = X'.src (h.preMor x') := by rw [h.covers, hg, hs]
  have e1 : (⟨E'.μ ⟨(h.preMor x', Φ.obj (f (h.preObj x'))), hfs⟩, (E'.P_μ _).trans ht⟩ :
      P' ⁻¹' {x'}) = ⟨h.pushforward f x', h.P_pushforward f x'⟩ :=
    Subtype.ext (h.pushforward_def hf x').symm
  have e2 : (⟨E'.μ ⟨(h.preMor x', Φ.obj (g (h.preObj x'))), hgs⟩, (E'.P_μ _).trans ht⟩ :
      P' ⁻¹' {x'}) = ⟨h.pushforward g x', h.P_pushforward g x'⟩ :=
    Subtype.ext (h.pushforward_def hg x').symm
  rw [h.pushforward_def (hf.sectionAdd hg),
    sectionAdd_apply (h.isSection_pushforward f) (h.isSection_pushforward g), ← e1, ← e2]
  refine (E'.μ_mk_congr rfl (h.obj_sectionAdd_eq hf hg hs hfs hgs) _
    (Subtype.property (_ : P' ⁻¹' {X'.src (h.preMor x')}))).trans ?_
  exact (E'.μ_add _ _ _).trans (fiber_add_val_congr ht _ _)

/-- `Φ_*(c · f) = c · Φ_* f`. -/
theorem pushforward_sectionSmul (c : ℝ) {f : Obj → W} (hf : IsSection P f) :
    h.pushforward (sectionSmul P (fun _ => c) f) =
      sectionSmul P' (fun _ => c) (h.pushforward f) := by
  funext x'
  have hs := h.src_preMor x'
  have ht := h.tgt_preMor x'
  have hfs : P' (Φ.obj (f (h.preObj x'))) = X'.src (h.preMor x') := by rw [h.covers, hf, hs]
  have e1 : (⟨E'.μ ⟨(h.preMor x', Φ.obj (f (h.preObj x'))), hfs⟩, (E'.P_μ _).trans ht⟩ :
      P' ⁻¹' {x'}) = ⟨h.pushforward f x', h.P_pushforward f x'⟩ :=
    Subtype.ext (h.pushforward_def hf x').symm
  rw [h.pushforward_def hf.sectionSmul, sectionSmul_apply (h.isSection_pushforward f), ← e1]
  refine (E'.μ_mk_congr rfl (h.obj_sectionSmul_eq c hf hs hfs) _
    (Subtype.property (_ : P' ⁻¹' {X'.src (h.preMor x')}))).trans ?_
  exact (E'.μ_smul _ _ _).trans (fiber_smul_val_congr ht c _)

end IsStrongBundleEquivalence

end EpStrongBundle

end Functors

namespace SBLocalization

open EPLocalization EpStrongBundle

variable {A A' : SEP.{u}}

namespace SDiagram

variable (D : SDiagram A A') (hΨ : SEP.equivalences D.Ψ)

theorem isSection_pushforward (f : A.Obj → A.W) : IsSection A'.P (D.pushforward hΨ f) :=
  (sbe hΨ).isSection_pushforward _

theorem isSection_pullback (g : A'.Obj → A'.W) : IsSection A.P (D.pullback hΨ g) :=
  (D.symm hΨ).isSection_pushforward D.isEquivalence_Φ g

/-- `[D]_*(f + g) = [D]_* f + [D]_* g` for sections `f`, `g`. -/
theorem pushforward_sectionAdd {f g : A.Obj → A.W} (hf : IsSection A.P f)
    (hg : IsSection A.P g) : D.pushforward hΨ (sectionAdd A.P f g) =
      sectionAdd A'.P (D.pushforward hΨ f) (D.pushforward hΨ g) := by
  change (sbe hΨ).pushforward (D.hΦ.pullback _) = _
  rw [D.hΦ.pullback_sectionAdd hf hg, (sbe hΨ).pushforward_sectionAdd
    (D.hΦ.isSection_pullback f) (D.hΦ.isSection_pullback g)]
  rfl

/-- `[D]_*(c · f) = c · [D]_* f` for a section `f`. -/
theorem pushforward_sectionSmul (c : ℝ) {f : A.Obj → A.W} (hf : IsSection A.P f) :
    D.pushforward hΨ (sectionSmul A.P (fun _ => c) f) =
      sectionSmul A'.P (fun _ => c) (D.pushforward hΨ f) := by
  change (sbe hΨ).pushforward (D.hΦ.pullback _) = _
  rw [D.hΦ.pullback_sectionSmul c hf, (sbe hΨ).pushforward_sectionSmul c
    (D.hΦ.isSection_pullback f)]
  rfl

/-- `[D]^*(f' + g') = [D]^* f' + [D]^* g'`. -/
theorem pullback_sectionAdd {f' g' : A'.Obj → A'.W} (hf' : IsSection A'.P f')
    (hg' : IsSection A'.P g') : D.pullback hΨ (sectionAdd A'.P f' g') =
      sectionAdd A.P (D.pullback hΨ f') (D.pullback hΨ g') :=
  (D.symm hΨ).pushforward_sectionAdd D.isEquivalence_Φ hf' hg'

/-- `[D]^*(c · f') = c · [D]^* f'`. -/
theorem pullback_sectionSmul (c : ℝ) {f' : A'.Obj → A'.W} (hf' : IsSection A'.P f') :
    D.pullback hΨ (sectionSmul A'.P (fun _ => c) f') =
      sectionSmul A.P (fun _ => c) (D.pullback hΨ f') :=
  (D.symm hΨ).pushforward_sectionSmul D.isEquivalence_Φ c hf'

end SDiagram

namespace GenSBMap

variable {f : GenSBMap A A'} (hf : f.IsGeneralizedIso)

theorem isSection_pushforward (g : A.Obj → A.W) : IsSection A'.P (pushforward hf g) :=
  (rep hf).isSection_pushforward _ g

theorem isSection_pullback (g : A'.Obj → A'.W) : IsSection A.P (pullback hf g) :=
  (rep hf).isSection_pullback _ g

/-- The linear map `Π x, W_x → Π x', W'_{x'}` underlying `[D]_*`. -/
def pushforwardPi : (∀ x, A.P ⁻¹' {x}) →ₗ[ℝ] ∀ x', A'.P ⁻¹' {x'} where
  toFun s := sectionToPi (pushforward hf (piToSection s)) (isSection_pushforward hf _)
  map_add' s t := piToSection_injective <| by
    rw [piToSection_add, piToSection_sectionToPi, piToSection_add]
    exact (rep hf).pushforward_sectionAdd _ (isSection_piToSection s) (isSection_piToSection t)
  map_smul' c s := piToSection_injective <| by
    rw [piToSection_smul, piToSection_sectionToPi, RingHom.id_apply, piToSection_smul]
    exact (rep hf).pushforward_sectionSmul _ c (isSection_piToSection s)

/-- The linear map `Π x', W'_{x'} → Π x, W_x` underlying `[D]^*`. -/
def pullbackPi : (∀ x', A'.P ⁻¹' {x'}) →ₗ[ℝ] ∀ x, A.P ⁻¹' {x} where
  toFun s := sectionToPi (pullback hf (piToSection s)) (isSection_pullback hf _)
  map_add' s t := piToSection_injective <| by
    rw [piToSection_add, piToSection_sectionToPi, piToSection_add]
    exact (rep hf).pullback_sectionAdd _ (isSection_piToSection s) (isSection_piToSection t)
  map_smul' c s := piToSection_injective <| by
    rw [piToSection_smul, piToSection_sectionToPi, RingHom.id_apply, piToSection_smul]
    exact (rep hf).pullback_sectionSmul _ c (isSection_piToSection s)

@[simp] theorem piToSection_pushforwardPi (s : ∀ x, A.P ⁻¹' {x}) :
    piToSection (pushforwardPi hf s) = pushforward hf (piToSection s) := rfl

@[simp] theorem piToSection_pullbackPi (s : ∀ x', A'.P ⁻¹' {x'}) :
    piToSection (pullbackPi hf s) = pullback hf (piToSection s) := rfl

/-- A linear isomorphism between subspaces of `Π x, W_x` and `Π x', W'_{x'}` from `[D]_*` and
`[D]^*`, given that they map the subspaces into each other and are inverse there. -/
def linearEquivOfInvOn {S : Set (A.Obj → A.W)} {S' : Set (A'.Obj → A'.W)}
    (M : Submodule ℝ (∀ x, A.P ⁻¹' {x})) (M' : Submodule ℝ (∀ x', A'.P ⁻¹' {x'}))
    (hM : ∀ s, s ∈ M ↔ piToSection s ∈ S) (hM' : ∀ s, s ∈ M' ↔ piToSection s ∈ S')
    (h₁ : MapsTo (pushforward hf) S S') (h₂ : MapsTo (pullback hf) S' S)
    (h₃ : InvOn (pullback hf) (pushforward hf) S S') : M ≃ₗ[ℝ] M' where
  toFun s := ⟨pushforwardPi hf s, (hM' _).2 (h₁ ((hM _).1 s.2))⟩
  map_add' s t := Subtype.ext ((pushforwardPi hf).map_add s t)
  map_smul' c s := Subtype.ext ((pushforwardPi hf).map_smul c s)
  invFun s := ⟨pullbackPi hf s, (hM _).2 (h₂ ((hM' _).1 s.2))⟩
  left_inv s := Subtype.ext (piToSection_injective (h₃.1 ((hM _).1 s.2)))
  right_inv s := Subtype.ext (piToSection_injective (h₃.2 ((hM' _).1 s.2)))

/-- **2021 Theorem 10.5.4, pp. 507–508 (2017: Theorem 10.9, p. 367), the isomorphism**: for a
generalized strong bundle isomorphism `[D]`, `[D]_* : Γ(P, μ) → Γ(P', μ')` is an isomorphism of
vector spaces, with inverse `[D]^*` (`pushforwardEquiv_apply`, `pushforwardEquiv_symm_apply`). -/
def pushforwardEquiv : A.E.sectionSpace ≃ₗ[ℝ] A'.E.sectionSpace :=
  linearEquivOfInvOn hf _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (theorem_10_5_4 hf).2.1.1 (theorem_10_5_4 hf).2.1.2.1 (theorem_10_5_4 hf).2.1.2.2.1

/-- **The same for `Γ⁺`**: `[D]_* : Γ⁺(P, μ) → Γ⁺(P', μ')` is an isomorphism of vector spaces. -/
def plusPushforwardEquiv : A.E.plusSectionSpace ≃ₗ[ℝ] A'.E.plusSectionSpace :=
  linearEquivOfInvOn hf _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
    (theorem_10_5_4 hf).2.2.2.1.1 (theorem_10_5_4 hf).2.2.2.1.2.1
    ((theorem_10_5_4 hf).2.1.2.2.1.mono A.E.plusSectionFunctors_subset
      A'.E.plusSectionFunctors_subset)

theorem pushforwardEquiv_apply (s : A.E.sectionSpace) :
    piToSection (pushforwardEquiv hf s : ∀ x', A'.P ⁻¹' {x'}) =
      pushforward hf (piToSection (s : ∀ x, A.P ⁻¹' {x})) := rfl

theorem pushforwardEquiv_symm_apply (s : A'.E.sectionSpace) :
    piToSection ((pushforwardEquiv hf).symm s : ∀ x, A.P ⁻¹' {x}) =
      pullback hf (piToSection (s : ∀ x', A'.P ⁻¹' {x'})) := rfl

theorem plusPushforwardEquiv_apply (s : A.E.plusSectionSpace) :
    piToSection (plusPushforwardEquiv hf s : ∀ x', A'.P ⁻¹' {x'}) =
      pushforward hf (piToSection (s : ∀ x, A.P ⁻¹' {x})) := rfl

/-- **`[D]_*` and `[D]^*` are linear** on all sections (the content of "isomorphism" beyond the
bijection of `theorem_10_5_4`). -/
theorem pushforward_sectionAdd {g₁ g₂ : A.Obj → A.W} (h₁ : IsSection A.P g₁)
    (h₂ : IsSection A.P g₂) :
    pushforward hf (sectionAdd A.P g₁ g₂) =
      sectionAdd A'.P (pushforward hf g₁) (pushforward hf g₂) :=
  (rep hf).pushforward_sectionAdd _ h₁ h₂

theorem pushforward_sectionSmul (c : ℝ) {g : A.Obj → A.W} (h : IsSection A.P g) :
    pushforward hf (sectionSmul A.P (fun _ => c) g) =
      sectionSmul A'.P (fun _ => c) (pushforward hf g) :=
  (rep hf).pushforward_sectionSmul _ c h

theorem pullback_sectionAdd {g₁ g₂ : A'.Obj → A'.W} (h₁ : IsSection A'.P g₁)
    (h₂ : IsSection A'.P g₂) :
    pullback hf (sectionAdd A'.P g₁ g₂) = sectionAdd A.P (pullback hf g₁) (pullback hf g₂) :=
  (rep hf).pullback_sectionAdd _ h₁ h₂

theorem pullback_sectionSmul (c : ℝ) {g : A'.Obj → A'.W} (h : IsSection A'.P g) :
    pullback hf (sectionSmul A'.P (fun _ => c) g) =
      sectionSmul A.P (fun _ => c) (pullback hf g) :=
  (rep hf).pullback_sectionSmul _ c h

end GenSBMap

end SBLocalization

end Polyfold
