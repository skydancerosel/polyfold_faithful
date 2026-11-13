import Polyfold.Chapter10.FredholmEquivalence
import Polyfold.Chapter12.ChartPull

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 592–594: the local strong bundle isomorphism `Φ̂` of a morphism used in the proof of
**Lemma 12.5.1** (2017: Lemma 12.2) and recalled before Theorem 12.5.3.

# The local strong bundle isomorphism of a morphism

## The text, paraphrased

(Proof of Lemma 12.5.1, p. 592; recalled on p. 594) For a morphism `φ : x → x'` take open
`U(φ)`, `U(x)`, `U(x')` with `s : U(φ) → U(x)` and `t : U(φ) → U(x')` sc-diffeomorphisms; then
`φ̂ = t ∘ (s|U(φ))⁻¹ : U(x) → U(x')`, and `Φ̂ : W|U(x) → W|U(x')`, `Φ̂(w) = μ((s|U(φ))⁻¹(P w), w)`,
is a strong bundle isomorphism covering `φ̂`, equal to `μ(φ, ·)` on `W_x`.

## What is formalized

* `EpStrongBundle.morIso E σ`: for a morphism `σ` and the sheet `X.sheetAt σ` (a neighbourhood of
  `σ` on which `s` and `t` are sc-diffeomorphisms), the local strong bundle isomorphism
  `W|t(sheet) → W|s(sheet)` with base map `y ↦ s(τ(y))` and bundle map
  `w ↦ μ(τ(P w)⁻¹, w)`, `τ = (t|sheet)⁻¹`.  This is the inverse `Φ̂⁻¹` of the text, in the
  direction of `StrongBundle.LocalIso.transportChart` (charts at `x` are carried to `x'`).  The
  construction is that of `exists_localIso_mor` (Chapter 10), with the data kept.
* `morIso_ϕ_tgt`, `tgt_mem_morIso`, `eqOn_morIso`: `t(σ)` lies in its domain, it maps `t(σ)` to
  `s(σ)`, and every functorial section is invariant under it (functoriality (8.3.4)).
* `morIso_Φ_eq`: on the fibre over `t(σ)` the bundle map is `μ(σ⁻¹, ·)`.
* `germAgree_morIso_comp`: **for composable `φ`, `ψ`, the composite of the isomorphisms of `φ` and
  `ψ` agrees near `t(ψ)` with the isomorphism of `ψ ∘ φ`** (`LocalIso.GermAgree`), by local
  uniqueness of the inverses of `t` and the axiom `μ(ψ ∘ γ, w) = μ(ψ, μ(γ, w))`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

section Mor

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

namespace EpStrongBundle

variable (E : EpStrongBundle X B)

variable (X) in
/-- The local section `y ↦ τ(y)⁻¹` of `s` near `t(σ)`, `τ = (t|sheet)⁻¹`. -/
def morInvSec (σ : Mor) : Obj → Mor := fun y => X.inv ((X.sheetAt σ).tgtInv y)

/-- `τ(y)⁻¹` starts at `y`. -/
lemma src_morInvSec (σ : Mor) {y : Obj} (hy : y ∈ (X.sheetAt σ).tgtSet) :
    X.src (morInvSec X σ y) = y := by
  rw [morInvSec, X.src_inv, (X.sheetAt σ).isScDiffeoOn_tgt.right_inv y hy]

/-- The base map `y ↦ s(τ(y))` is an sc-diffeomorphism `t(sheet) → s(sheet)`. -/
theorem isScDiffeoOn_morBase (σ : Mor) :
    X.PObj.IsScDiffeoOn X.PObj (X.src ∘ (X.sheetAt σ).tgtInv) (X.tgt ∘ (X.sheetAt σ).srcInv)
      (X.sheetAt σ).tgtSet (X.sheetAt σ).srcSet :=
  (X.sheetAt σ).isScDiffeoOn_src.comp (X.sheetAt σ).isScDiffeoOn_tgt.symm

theorem isScSmoothOn_morInvSec (σ : Mor) :
    X.PObj.IsScSmoothOn X.PMor (morInvSec X σ) (X.sheetAt σ).tgtSet :=
  MPolyfold.IsScSmoothOn.comp X.isScSmoothMap_inv
    (X.sheetAt σ).isScDiffeoOn_tgt.isScSmoothOn_inv (mapsTo_univ _ _)

omit [ParacompactSpace (pullbackSpace P X.src)] in
lemma P_sectionAct_morInvSec (σ : Mor) {w : W} (hw : P w ∈ (X.sheetAt σ).tgtSet) :
    P (E.sectionAct (morInvSec X σ) w) = (X.src ∘ (X.sheetAt σ).tgtInv) (P w) := by
  rw [E.P_sectionAct_of_eq _ (src_morInvSec σ hw).symm]; exact X.tgt_inv _

omit [ParacompactSpace (pullbackSpace P X.src)] in
lemma P_sectionAct_srcInv (σ : Mor) {w : W} (hw : P w ∈ (X.sheetAt σ).srcSet) :
    P (E.sectionAct (X.sheetAt σ).srcInv w) = (X.tgt ∘ (X.sheetAt σ).srcInv) (P w) :=
  E.P_sectionAct_of_eq _ ((X.sheetAt σ).isScDiffeoOn_src.right_inv _ hw).symm

omit [ParacompactSpace (pullbackSpace P X.src)] in
lemma sectionAct_srcInv_morInvSec (σ : Mor) {w : W} (hw : P w ∈ (X.sheetAt σ).tgtSet) :
    E.sectionAct (X.sheetAt σ).srcInv (E.sectionAct (morInvSec X σ) w) = w := by
  set S := X.sheetAt σ
  have hs := S.isScDiffeoOn_src
  have ht := S.isScDiffeoOn_tgt
  have hρ : S.tgtInv (P w) ∈ S.carrier := ht.mapsTo_inv hw
  have hy1 : P w = X.src (morInvSec X σ (P w)) := (src_morInvSec σ hw).symm
  have hcov := E.P_sectionAct_morInvSec σ hw
  have hw1 : P (E.sectionAct (morInvSec X σ) w) =
      X.src (S.srcInv (P (E.sectionAct (morInvSec X σ) w))) :=
    (hs.right_inv _ (by rw [hcov]; exact hs.mapsTo hρ)).symm
  have hτρ : S.srcInv (P (E.sectionAct (morInvSec X σ) w)) = S.tgtInv (P w) := by
    rw [hcov]; exact hs.left_inv _ hρ
  have hP' : P (E.μ ⟨(X.inv (S.tgtInv (P w)), w), hy1⟩) = X.src (S.tgtInv (P w)) := by
    rw [E.P_μ]; exact X.tgt_inv _
  rw [E.sectionAct_of_eq S.srcInv hw1]
  refine (E.μ_congr (q' := ⟨(S.tgtInv (P w), E.μ ⟨(X.inv (S.tgtInv (P w)), w), hy1⟩), hP'⟩)
    ?_).trans (E.μ_μ_inv _ w hy1 hP')
  exact Prod.ext hτρ (E.sectionAct_of_eq _ hy1)

omit [ParacompactSpace (pullbackSpace P X.src)] in
lemma sectionAct_morInvSec_srcInv (σ : Mor) {w : W} (hw : P w ∈ (X.sheetAt σ).srcSet) :
    E.sectionAct (morInvSec X σ) (E.sectionAct (X.sheetAt σ).srcInv w) = w := by
  set S := X.sheetAt σ
  have hs := S.isScDiffeoOn_src
  have ht := S.isScDiffeoOn_tgt
  have hρ : S.srcInv (P w) ∈ S.carrier := hs.mapsTo_inv hw
  have hy1 : P w = X.src (S.srcInv (P w)) := (hs.right_inv _ hw).symm
  have hcov := E.P_sectionAct_srcInv σ hw
  have hmem : P (E.sectionAct S.srcInv w) ∈ S.tgtSet := by rw [hcov]; exact ht.mapsTo hρ
  have hw1 : P (E.sectionAct S.srcInv w) =
      X.src (morInvSec X σ (P (E.sectionAct S.srcInv w))) := (src_morInvSec σ hmem).symm
  have hτρ : morInvSec X σ (P (E.sectionAct S.srcInv w)) = X.inv (S.srcInv (P w)) := by
    change X.inv (S.tgtInv (P (E.sectionAct S.srcInv w))) = _
    rw [hcov]; exact congrArg X.inv (ht.left_inv _ hρ)
  have hP' : P (E.μ ⟨(S.srcInv (P w), w), hy1⟩) = X.src (X.inv (S.srcInv (P w))) := by
    rw [E.P_μ, X.src_inv]
  rw [E.sectionAct_of_eq (morInvSec X σ) hw1]
  refine (E.μ_congr (q' := ⟨(X.inv (S.srcInv (P w)), E.μ ⟨(S.srcInv (P w), w), hy1⟩), hP'⟩)
    ?_).trans (E.μ_inv_μ ⟨(S.srcInv (P w), w), hy1⟩ hP')
  exact Prod.ext hτρ (E.sectionAct_of_eq _ hy1)

omit [ParacompactSpace (pullbackSpace P X.src)] in
lemma mapsTo_sectionAct_morInvSec (σ : Mor) :
    MapsTo (E.sectionAct (morInvSec X σ)) (P ⁻¹' (X.sheetAt σ).tgtSet)
      (P ⁻¹' (X.sheetAt σ).srcSet) := fun w hw => by
  change P (E.sectionAct (morInvSec X σ) w) ∈ (X.sheetAt σ).srcSet
  rw [E.P_sectionAct_morInvSec σ hw]; exact (isScDiffeoOn_morBase σ).mapsTo hw

omit [ParacompactSpace (pullbackSpace P X.src)] in
lemma mapsTo_sectionAct_srcInv (σ : Mor) :
    MapsTo (E.sectionAct (X.sheetAt σ).srcInv) (P ⁻¹' (X.sheetAt σ).srcSet)
      (P ⁻¹' (X.sheetAt σ).tgtSet) := fun w hw => by
  change P (E.sectionAct (X.sheetAt σ).srcInv w) ∈ (X.sheetAt σ).tgtSet
  rw [E.P_sectionAct_srcInv σ hw]; exact (isScDiffeoOn_morBase σ).mapsTo_inv hw

/-- **The local strong bundle isomorphism of a morphism `σ`** (the inverse of the text's `Φ̂`):
`W|t(sheet) → W|s(sheet)`, `w ↦ μ(τ(P w)⁻¹, w)` over `y ↦ s(τ(y))`, `τ = (t|sheet)⁻¹`, for the
sheet `X.sheetAt σ`. -/
def morIso (σ : Mor) :
    StrongBundle.LocalIso B B (X.sheetAt σ).tgtSet (X.sheetAt σ).srcSet where
  ϕ := X.src ∘ (X.sheetAt σ).tgtInv
  g := X.tgt ∘ (X.sheetAt σ).srcInv
  Φ := E.sectionAct (morInvSec X σ)
  Ψ := E.sectionAct (X.sheetAt σ).srcInv
  Φ₁ := StrongBundle.oneRestrict B B (E.sectionAct (morInvSec X σ))
    (E.mapsTo_oneSet_sectionAct _)
  Ψ₁ := StrongBundle.oneRestrict B B (E.sectionAct (X.sheetAt σ).srcInv)
    (E.mapsTo_oneSet_sectionAct _)
  base := isScDiffeoOn_morBase σ
  zero :=
    ⟨E.isScSmoothOn_sectionAct (X.sheetAt σ).isScDiffeoOn_tgt.isOpen_target
        (isScSmoothOn_morInvSec σ) fun _ hy => src_morInvSec σ hy,
      E.isScSmoothOn_sectionAct (X.sheetAt σ).isScDiffeoOn_src.isOpen_target
        (X.sheetAt σ).isScDiffeoOn_src.isScSmoothOn_inv (X.sheetAt σ).isScDiffeoOn_src.right_inv,
      E.mapsTo_sectionAct_morInvSec σ, E.mapsTo_sectionAct_srcInv σ,
      fun _ hw => E.sectionAct_srcInv_morInvSec σ hw,
      fun _ hw => E.sectionAct_morInvSec_srcInv σ hw⟩
  one :=
    ⟨E.isScSmoothOn_sectionAct_one (X.sheetAt σ).isScDiffeoOn_tgt.isOpen_target
        (isScSmoothOn_morInvSec σ) fun _ hy => src_morInvSec σ hy,
      E.isScSmoothOn_sectionAct_one (X.sheetAt σ).isScDiffeoOn_src.isOpen_target
        (X.sheetAt σ).isScDiffeoOn_src.isScSmoothOn_inv (X.sheetAt σ).isScDiffeoOn_src.right_inv,
      fun _ hw => E.mapsTo_sectionAct_morInvSec σ hw,
      fun _ hw => E.mapsTo_sectionAct_srcInv σ hw,
      fun _ hw => B.oneVal_injective (E.sectionAct_srcInv_morInvSec σ hw),
      fun _ hw => B.oneVal_injective (E.sectionAct_morInvSec_srcInv σ hw)⟩
  covers _ hw := E.P_sectionAct_morInvSec σ hw
  oneVal_Φ₁ _ _ := rfl
  fiber_linear _ _ hy hy' :=
    E.isLinearMap_sectionAct (fun _ hy => src_morInvSec σ hy) hy ((X.tgt_inv _).trans hy')

@[simp] lemma morIso_ϕ (σ : Mor) (y : Obj) :
    (E.morIso σ).ϕ y = X.src ((X.sheetAt σ).tgtInv y) := rfl

@[simp] lemma morIso_g (σ : Mor) (y : Obj) :
    (E.morIso σ).g y = X.tgt ((X.sheetAt σ).srcInv y) := rfl

@[simp] lemma morIso_Φ (σ : Mor) (w : W) :
    (E.morIso σ).Φ w = E.sectionAct (morInvSec X σ) w := rfl

@[simp] lemma morIso_Ψ (σ : Mor) (w : W) :
    (E.morIso σ).Ψ w = E.sectionAct (X.sheetAt σ).srcInv w := rfl

/-- `τ(t σ) = σ`. -/
lemma tgtInv_tgt (σ : Mor) : (X.sheetAt σ).tgtInv (X.tgt σ) = σ :=
  (X.sheetAt σ).isScDiffeoOn_tgt.left_inv σ (X.mem_sheetAt σ)

/-- `t(σ)` lies in the domain of the isomorphism of `σ`. -/
lemma tgt_mem_morIso (σ : Mor) : X.tgt σ ∈ (X.sheetAt σ).tgtSet :=
  (X.sheetAt σ).isScDiffeoOn_tgt.mapsTo (X.mem_sheetAt σ)

/-- The base map of the isomorphism of `σ` maps `t(σ)` to `s(σ)`. -/
lemma morIso_ϕ_tgt (σ : Mor) : (E.morIso σ).ϕ (X.tgt σ) = X.src σ := by
  rw [morIso_ϕ, tgtInv_tgt]

/-- `s(σ)` lies in the target of the isomorphism of `σ`. -/
lemma src_mem_morIso (σ : Mor) : X.src σ ∈ (X.sheetAt σ).srcSet :=
  (X.sheetAt σ).isScDiffeoOn_src.mapsTo (X.mem_sheetAt σ)

/-- **Functorial sections are invariant under the isomorphism of a morphism**:
`f = Ψ ∘ f ∘ ϕ` on `t(sheet)` (the functoriality `f(t φ) = μ(φ, f(s φ))`). -/
theorem eqOn_morIso (σ : Mor) {f : Obj → W} (hf : IsSection P f) (hfun : E.IsFunctorialSection hf) :
    EqOn f ((E.morIso σ).Ψ ∘ f ∘ (E.morIso σ).ϕ) (X.sheetAt σ).tgtSet := by
  intro y hy
  set S := X.sheetAt σ
  have hs := S.isScDiffeoOn_src
  have ht := S.isScDiffeoOn_tgt
  have hρ : S.tgtInv y ∈ S.carrier := ht.mapsTo_inv hy
  have hsρ : X.src (S.tgtInv y) ∈ S.srcSet := hs.mapsTo hρ
  have h1 : P (f (X.src (S.tgtInv y))) = X.src (S.srcInv (P (f (X.src (S.tgtInv y))))) :=
    (hs.right_inv _ (by rw [hf]; exact hsρ)).symm
  have h2 : S.srcInv (P (f (X.src (S.tgtInv y)))) = S.tgtInv y := by rw [hf, hs.left_inv _ hρ]
  change f y = E.sectionAct S.srcInv (f (X.src (S.tgtInv y)))
  rw [E.sectionAct_of_eq S.srcInv h1]
  exact (congrArg f (ht.right_inv y hy).symm).trans
    ((hfun (S.tgtInv y)).trans (E.μ_congr (Prod.ext h2.symm rfl)))

/-- **On the fibre over `t(σ)` the bundle map is `μ(σ⁻¹, ·)`.** -/
theorem morIso_Φ_eq (σ : Mor) {w : W} (hw : P w = X.tgt σ) :
    (E.morIso σ).Φ w = E.μ ⟨(X.inv σ, w), hw.trans (X.src_inv σ).symm⟩ := by
  have hm : P w ∈ (X.sheetAt σ).tgtSet := by rw [hw]; exact tgt_mem_morIso σ
  rw [morIso_Φ, E.sectionAct_of_eq _ (src_morInvSec σ hm).symm]
  refine E.μ_congr (Prod.ext ?_ rfl)
  change X.inv ((X.sheetAt σ).tgtInv (P w)) = X.inv σ
  rw [hw, tgtInv_tgt]

/-! ### Composition -/

/-- **The isomorphisms of `φ`, `ψ` and of `ψ ∘ φ` agree near `t(ψ)`**: near `y = t(ψ)` the local
inverse of `t` at `ψ ∘ φ` is `y ↦ τ_ψ(y) ∘ τ_φ(s(τ_ψ(y)))` (both are continuous inverses of
`t` through `ψ ∘ φ`, and `t` is injective on the sheet of `ψ ∘ φ`), so the base maps agree, and
the bundle maps agree by `μ((a ∘ b)⁻¹, w) = μ(b⁻¹, μ(a⁻¹, w))`. -/
theorem germAgree_morIso_comp {φ ψ : Mor} (h : X.src ψ = X.tgt φ) :
    StrongBundle.LocalIso.GermAgree (E.morIso φ) (E.morIso ψ) (E.morIso (X.comp ψ φ))
      (X.tgt ψ) := by
  set S₁ := X.sheetAt φ with hS₁
  set S₂ := X.sheetAt ψ with hS₂
  set S₃ := X.sheetAt (X.comp ψ φ) with hS₃
  have ht₁ := S₁.isScDiffeoOn_tgt
  have ht₂ := S₂.isScDiffeoOn_tgt
  have ht₃ := S₃.isScDiffeoOn_tgt
  have hs₂ := S₂.isScDiffeoOn_src
  -- the two local maps
  set b : Obj → Mor := fun y => S₁.tgtInv (X.src (S₂.tgtInv y)) with hbdef
  set c : Obj → Mor := fun y => X.comp (S₂.tgtInv y) (b y) with hcdef
  set D : Set Obj := S₂.tgtSet ∩ (X.src ∘ S₂.tgtInv) ⁻¹' S₁.tgtSet with hDdef
  have hDo : IsOpen D := (isScDiffeoOn_morBase (X := X) ψ).isScSmoothOn.continuousOn
    |>.isOpen_inter_preimage ht₂.isOpen_target ht₁.isOpen_target
  have hbc : ContinuousOn b D :=
    ht₁.isScSmoothOn_inv.continuousOn.comp
      ((isScDiffeoOn_morBase (X := X) ψ).isScSmoothOn.continuousOn.mono inter_subset_left)
      fun y hy => hy.2
  have hcomp := X.isScSmoothCompSheet S₂.srcInv S₂.carrier S₂.srcSet hs₂
  have hcD : ∀ y ∈ D, c y = (fun m => X.comp (S₂.srcInv (X.tgt m)) m) (b y) := by
    intro y hy
    have h1 : X.tgt (b y) = X.src (S₂.tgtInv y) := ht₁.right_inv _ hy.2
    change X.comp (S₂.tgtInv y) (b y) = X.comp (S₂.srcInv (X.tgt (b y))) (b y)
    rw [h1, hs₂.left_inv _ (ht₂.mapsTo_inv hy.1)]
  have hbmaps : MapsTo b D (X.tgt ⁻¹' S₂.srcSet) := fun y hy => by
    change X.tgt (b y) ∈ S₂.srcSet
    rw [show X.tgt (b y) = X.src (S₂.tgtInv y) from ht₁.right_inv _ hy.2]
    exact hs₂.mapsTo (ht₂.mapsTo_inv hy.1)
  have hcc : ContinuousOn c D :=
    (hcomp.continuousOn.comp hbc hbmaps).congr hcD
  -- the point
  have hyD : X.tgt ψ ∈ D := ⟨tgt_mem_morIso ψ, by
    change X.src (S₂.tgtInv (X.tgt ψ)) ∈ S₁.tgtSet
    rw [tgtInv_tgt, h]; exact tgt_mem_morIso φ⟩
  have hc0 : c (X.tgt ψ) = X.comp ψ φ := by
    simp only [hcdef, hbdef]
    rw [tgtInv_tgt, h, tgtInv_tgt]
  set N : Set Obj := D ∩ c ⁻¹' S₃.carrier ∩ S₃.tgtSet with hNdef
  have hNo : IsOpen N :=
    (hcc.isOpen_inter_preimage hDo S₃.isScDiffeoOn_src.isScSmoothOn.isOpen).inter
    ht₃.isOpen_target
  have hxN : X.tgt ψ ∈ N := ⟨⟨hyD, by rw [mem_preimage, hc0]; exact X.mem_sheetAt _⟩, by
    rw [show X.tgt ψ = X.tgt (X.comp ψ φ) from (X.tgt_comp ψ φ h).symm]
    exact tgt_mem_morIso _⟩
  -- the local inverses agree on `N`
  have hsrcb : ∀ y ∈ D, X.src (S₂.tgtInv y) = X.tgt (b y) := fun y hy =>
    (ht₁.right_inv _ hy.2).symm
  have hτ : ∀ y ∈ N, S₃.tgtInv y = c y := by
    intro y hy
    have htc : X.tgt (c y) = y := by
      simp only [hcdef]
      rw [X.tgt_comp _ _ (hsrcb y hy.1.1), ht₂.right_inv _ hy.1.1.1]
    calc S₃.tgtInv y = S₃.tgtInv (X.tgt (c y)) := by rw [htc]
      _ = c y := ht₃.left_inv _ hy.1.2
  refine ⟨⟨N, hNo, hxN, fun y hy => hy.1.1.1, fun y hy => hy.2, fun y hy => ?_, fun w hw => ?_⟩⟩
  · rw [morIso_ϕ, morIso_ϕ, morIso_ϕ, hτ y hy]
    simp only [hcdef]
    rw [X.src_comp _ _ (hsrcb y hy.1.1)]
  · -- the bundle maps
    have hy := hw
    have hP1 : P w = X.src (morInvSec X ψ (P w)) := (src_morInvSec ψ hy.1.1.1).symm
    have hPw₁ : P (E.μ ⟨(morInvSec X ψ (P w), w), hP1⟩) = X.src (S₂.tgtInv (P w)) := by
      rw [E.P_μ]; exact X.tgt_inv _
    have h2 : P (E.μ ⟨(morInvSec X ψ (P w), w), hP1⟩) =
        X.src (morInvSec X φ (P (E.μ ⟨(morInvSec X ψ (P w), w), hP1⟩))) := by
      rw [src_morInvSec φ (by rw [hPw₁]; exact hy.1.1.2)]
    have hP3 : P w = X.src (morInvSec X (X.comp ψ φ) (P w)) := (src_morInvSec _ hy.2).symm
    have hcb : X.src (S₂.tgtInv (P w)) = X.tgt (b (P w)) := hsrcb _ hy.1.1
    have hinv : morInvSec X (X.comp ψ φ) (P w) =
        X.comp (X.inv (b (P w))) (X.inv (S₂.tgtInv (P w))) := by
      change X.inv (S₃.tgtInv (P w)) = _
      rw [hτ _ hy]; exact X.inv_comp_rev hcb
    have hcomp' : X.src (X.inv (b (P w))) = X.tgt (X.inv (S₂.tgtInv (P w))) := by
      rw [X.src_inv, X.tgt_inv, hcb]
    have key := E.μ_comp (X.inv (b (P w))) (X.inv (S₂.tgtInv (P w))) w hP1 hcomp'
    have hb' : morInvSec X φ (P (E.μ ⟨(morInvSec X ψ (P w), w), hP1⟩)) = X.inv (b (P w)) := by
      change X.inv (S₁.tgtInv (P (E.μ ⟨(morInvSec X ψ (P w), w), hP1⟩))) =
        X.inv (S₁.tgtInv (X.src (S₂.tgtInv (P w))))
      rw [hPw₁]
    rw [morIso_Φ, morIso_Φ, morIso_Φ, E.sectionAct_of_eq (morInvSec X ψ) hP1,
      E.sectionAct_of_eq (morInvSec X φ) h2, E.sectionAct_of_eq (morInvSec X (X.comp ψ φ)) hP3]
    have e1 : E.μ ⟨(morInvSec X φ (P (E.μ ⟨(morInvSec X ψ (P w), w), hP1⟩)),
        E.μ ⟨(morInvSec X ψ (P w), w), hP1⟩), h2⟩ =
        E.μ ⟨(X.inv (b (P w)), E.μ ⟨(X.inv (S₂.tgtInv (P w)), w), hP1⟩),
          h2.trans (congrArg X.src hb')⟩ := E.μ_congr (Prod.ext hb' rfl)
    have e3 : E.μ ⟨(X.comp (X.inv (b (P w))) (X.inv (S₂.tgtInv (P w))), w),
        hP3.trans (congrArg X.src hinv)⟩ = E.μ ⟨(morInvSec X (X.comp ψ φ) (P w), w), hP3⟩ :=
      E.μ_congr (Prod.ext hinv.symm rfl)
    exact e1.trans ((E.μ_congr rfl).trans (key.symm.trans ((E.μ_congr rfl).trans e3)))

end EpStrongBundle

end Mor

end Polyfold
