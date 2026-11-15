import Polyfold.Chapter12.OrientationRepresentativeIndep
import Polyfold.Chapter10.StrongBundleLocalFamilies

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, **Theorem 12.5.7** (2017: Theorem 12.12), with **Proposition 10.4.7** (pp. 501–502)
and **Definition 8.4.2** (p. 382): strong bundle equivalences with the same map of orbit spaces
induce the same map of orientations.

## The text, paraphrased

(Proposition 10.4.7) For strong bundle equivalences `Φ, Ψ : W → W'` with `|Φ| = |Ψ|` between
strong bundles with the local regularity property, every `x` has a neighbourhood `U(x)` and an
sc-smooth `z ↦ α_z : ϕ(z) → ψ(z)` on it with `μ'(α_z, Φ(v)) = Ψ(v)` for `P(v) = z`.

(Theorem 12.5.7) A generalized strong bundle isomorphism induces a map of the orientation
bundles; an orientation has a push-forward.

## What is formalized

For strong bundle equivalences `Φ, Ψ : W → W'` covering `ϕ, ψ`, an sc-Fredholm section functor
`f'` of `W'` and `f = Φ^* f' = Ψ^* f'`:

* `germ_of_family`: a family `α_z : ϕ(z) → ψ(z)`, continuous near `a`, with
  `μ'(α_z, Φ(v)) = Ψ(v)`, makes `Φ̂'_{α_a} ∘ Ψ = Φ` near `a` (the proof of `germ_nat` for a
  family given only near `a`, with no compatibility with the morphisms).
* `eT_of_germ`, `eK_of_germ`, `orEqv_of_germ`: for a morphism `σ : ϕ(a) → ψ(a)` with
  `Φ̂'_σ ∘ Ψ = Φ` near `a`, the identification `Or^{f'}_{ψ(a)} ≃ Or^f_a` of `Ψ` after `σ_*` is
  that of `Φ`.
* **`orbitOrMap_eq_of_orbitMap_eq`**: if `|Φ| = |Ψ|` on `|W|` and `W'` has the local regularity
  property (Definition 8.4.2, read as `EpStrongBundle.IsLRLocal`), then `|Φ|_* = |Ψ|_*` on
  `|O_f|`.  No natural transformation `Φ ⇒ Ψ` is needed: for a non-effective base there need not
  be one, and the families of Proposition 10.4.7 suffice.
* `smoothOrbitMap_eq_of_orbitMap_eq`: `|ϕ| = |ψ|` on `|X_∞|` (no regularity needed).
* **`theorem_12_5_7_rep_indep_of_orbitMap_eq`**: two diagrams `W ←Φ₁– V₁ –Φ₂→ W'` and
  `W ←Γ₁– V₂ –Γ₂→ W'` with equivalences `H₁ : V₃ → V₁`, `H₂ : V₃ → V₂` such that
  `Φ₁ ∘ H₁ ≃ Γ₁ ∘ H₂` and `|Φ₂ ∘ H₁| = |Γ₂ ∘ H₂|` induce the same map `|O_f| → |O_{f'}|`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

open StrongRetr

universe u

section Germ

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

variable {ϕ ψ : EpFunctor X X'} {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (hΦ : E.IsStrongBundleEquivalence E' ϕ Φ) (hΨ : E.IsStrongBundleEquivalence E' ψ Ψ)

include hΦ hΨ in
/-- **A local family `α_z : ϕ(z) → ψ(z)` with `μ'(α_z, Φ(v)) = Ψ(v)` identifies the local
isomorphisms of `Φ` and `Ψ`**: near `a`, `Φ̂'_{α_a} ∘ Ψ = Φ` (base and bundle maps), since
`α_y` lies in the sheet of `α_a` for `y` near `a`. -/
theorem germ_of_family {U : Set Obj} {α : Obj → Mor'} (hU : IsOpen U)
    (hα : ContinuousOn α U)
    (hfam : ∀ z ∈ U, X'.src (α z) = ϕ.obj z ∧ X'.tgt (α z) = ψ.obj z ∧
      ∀ v, P v = z → E'.lrAct (α z) (Φ.obj v) = Ψ.obj v) {a : Obj} (ha : a ∈ U) :
    ∃ N : Set Obj, IsOpen N ∧ a ∈ N ∧
      (∀ y ∈ N, (E'.morIso (α a)).ϕ ((hΨ.locIso a).ϕ y) = (hΦ.locIso a).ϕ y) ∧
      ∀ w, P w ∈ N →
        (E'.morIso (α a)).Φ ((hΨ.locIso a).Φ w) = (hΦ.locIso a).Φ w := by
  set S := X'.sheetAt (α a) with hS
  refine ⟨U ∩ α ⁻¹' S.carrier, hα.isOpen_inter_preimage hU S.isScDiffeoOn_tgt.isOpen_source,
    ⟨ha, X'.mem_sheetAt _⟩, ?_, ?_⟩
  · rintro y ⟨hyU, hy⟩
    change X'.src (S.tgtInv (ψ.obj y)) = ϕ.obj y
    rw [← (hfam y hyU).2.1, S.isScDiffeoOn_tgt.left_inv _ hy, (hfam y hyU).1]
  · rintro w ⟨hwU, hw⟩
    obtain ⟨hsw, htw, hμw⟩ := hfam (P w) hwU
    have hcov : P' (Ψ.obj w) = ψ.obj (P w) := hΨ.covers w
    have hτ : S.tgtInv (ψ.obj (P w)) = α (P w) := by
      rw [← htw]; exact S.isScDiffeoOn_tgt.left_inv _ hw
    have hT : P' (Ψ.obj w) ∈ S.tgtSet := by
      rw [hcov, ← htw]; exact S.isScDiffeoOn_tgt.mapsTo hw
    change E'.sectionAct (morInvSec X' (α a)) (Ψ.obj w) = Φ.obj w
    rw [E'.sectionAct_of_eq _ (src_morInvSec (α a) hT).symm]
    have hinv : morInvSec X' (α a) (P' (Ψ.obj w)) = X'.inv (α (P w)) := by
      change X'.inv (S.tgtInv (P' (Ψ.obj w))) = _
      rw [hcov, hτ]
    have hΦw : P' (Φ.obj w) = X'.src (α (P w)) := by
      rw [hsw]; exact hΦ.covers w
    have hΨw : Ψ.obj w = E'.μ ⟨(α (P w), Φ.obj w), hΦw⟩ := by
      rw [← hμw w rfl]
      exact EpStrongBundle.lrAct_eq hΦw
    have hv : P' (Ψ.obj w) = X'.src (X'.inv (α (P w))) := by
      rw [X'.src_inv, htw]; exact hcov
    refine (E'.μ_congr
      (q := ⟨(morInvSec X' (α a) (P' (Ψ.obj w)), Ψ.obj w),
        (src_morInvSec (α a) hT).symm⟩) (q' := ⟨(X'.inv (α (P w)), Ψ.obj w), hv⟩)
      (Prod.ext hinv rfl)).trans ?_
    exact E'.μ_inv_eq_of_eq_μ (ψ := α (P w)) hv hΦw hΨw

variable {a : Obj} (σ : Mor') (hσs : X'.src σ = ϕ.obj a) (hσt : X'.tgt σ = ψ.obj a)

/-- The open set at `ϕ(a)` used to compare `Φ` and `Ψ` along `σ : ϕ(a) → ψ(a)`. -/
def germSet' (a : Obj) (σ : Mor') : Set Obj' :=
  hΦ.locSet' a ∩ ((X'.sheetAt σ).srcSet ∩ (E'.morIso σ).g ⁻¹' hΨ.locSet' a)

theorem isOpen_germSet' (a : Obj) (σ : Mor') : IsOpen (germSet' hΦ hΨ a σ) :=
  (hΦ.isOpen_locSet' a).inter
    ((E'.morIso σ).base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage
      (isOpen_srcSet _) (hΨ.isOpen_locSet' a))

include hσs hσt in
theorem mem_germSet' : ϕ.obj a ∈ germSet' hΦ hΨ a σ := by
  refine ⟨hΦ.obj_mem_locSet' a, mem_srcSet hσs, ?_⟩
  change (E'.morIso σ).g (ϕ.obj a) ∈ hΨ.locSet' a
  rw [← E'.morIso_ϕ_eq hσs hσt, (E'.morIso σ).base.left_inv _ (mem_tgtSet hσt)]
  exact hΨ.obj_mem_locSet' a

variable (hG : ∃ N : Set Obj, IsOpen N ∧ a ∈ N ∧
    (∀ y ∈ N, (E'.morIso σ).ϕ ((hΨ.locIso a).ϕ y) = (hΦ.locIso a).ϕ y) ∧
    ∀ w, P w ∈ N → (E'.morIso σ).Φ ((hΨ.locIso a).Φ w) = (hΦ.locIso a).Φ w)

include hG in
/-- **`eT` of `Ψ` after `Tσ` is `eT` of `Φ`**, for `σ : ϕ(a) → ψ(a)` with `Φ̂'_σ ∘ Ψ = Φ`
near `a`. -/
theorem eT_of_germ (hs : a ∈ X.PObj.smoothSet)
    (v : ↥(orPt B' (ϕ.obj a) (hΦ.smooth_obj hs)).T) :
    hΨ.eT a hs (E'.morTx σ hσs hσt (hΦ.smooth_obj hs) (hΨ.smooth_obj hs) v) =
      hΦ.eT a hs v := by
  have ha' := hσs
  have hb' := hσt
  set p := restrPt B' (ϕ.obj a) (isOpen_germSet' hΦ hΨ a σ) (mem_germSet' hΦ hΨ σ hσs hσt)
    (hΦ.smooth_obj hs) with hp
  have hpV : p.c.φ.source ⊆ germSet' hΦ hΨ a σ := restrPt_sub _ _ _ _
  have hpa : p.c.φ.source ⊆ hΦ.locSet' a := fun y hy => (hpV hy).1
  have hpm : p.c.φ.source ⊆ (X'.sheetAt σ).srcSet := fun y hy => (hpV hy).2.1
  set q := (E'.morIso σ).pullPt p hpm (mem_tgtSet hb') (E'.morIso_ϕ_eq ha' hb') with hq
  have hqs : q.c.φ.source ⊆ hΨ.locSet' a := by
    rintro y ⟨hyU, hyp⟩
    have := (hpV hyp).2.2
    change (E'.morIso σ).g ((E'.morIso σ).ϕ y) ∈ hΨ.locSet' a at this
    rwa [(E'.morIso σ).base.left_inv y hyU] at this
  set A := (hΦ.locIso a).mpullPt p hpa (hΦ.mem_locSet a) rfl with hA
  set Bq := (hΨ.locIso a).mpullPt q hqs (hΨ.mem_locSet a) rfl with hBq
  set t := (orPt B' (ϕ.obj a) (hΦ.smooth_obj hs)).transferT p v
  have e1 : hΦ.eT a hs v = A.transferT (orPt B a hs) t := (hΦ.eT_eq hs p hpa v).trans rfl
  have e2 : hΨ.eT a hs (E'.morTx σ ha' hb' (hΦ.smooth_obj hs) (hΨ.smooth_obj hs) v) =
      Bq.transferT (orPt B a hs) t := by
    rw [E'.morTx_eq σ ha' hb' (hΦ.smooth_obj hs) (hΨ.smooth_obj hs) p hpm,
      hΨ.eT_eq hs q hqs]
    exact congrArg (Bq.transferT (orPt B a hs))
      ((q.transferT_trans_apply (orPt B' (ψ.obj a) (hΨ.smooth_obj hs)) q t).trans
        (q.transferT_self_apply t))
  have h4 := StrongBundle.LocalIso.transferT_mpullPt₃ (L := E'.morIso σ)
    (L₂ := hΨ.locIso a) (M := hΦ.locIso a) p hpm (mem_tgtSet hb') (E'.morIso_ϕ_eq ha' hb') hqs
    (hΨ.mem_locSet a) rfl hpa (hΦ.mem_locSet a) rfl hG t
  have e3 : Bq.transferT (orPt B a hs) t = A.transferT (orPt B a hs) t :=
    (congrArg (Bq.transferT (orPt B a hs)) (Subtype.ext h4).symm).trans
      (ChartPoint.transferT_trans_apply A Bq (orPt B a hs) t)
  exact e2.trans (e3.trans e1.symm)

include hG in
/-- **`eK` of `Ψ` after `μ'(σ, ·)` is `eK` of `Φ`**, for `σ : ϕ(a) → ψ(a)` with
`Φ̂'_σ ∘ Ψ = Φ` near `a`. -/
theorem eK_of_germ (hs : a ∈ X.PObj.smoothSet)
    (κ : ↥(orPt B' (ϕ.obj a) (hΦ.smooth_obj hs)).K) :
    hΨ.eK a hs (E'.morKx σ hσs hσt (hΦ.smooth_obj hs) (hΨ.smooth_obj hs) κ) =
      hΦ.eK a hs κ := by
  have ha' := hσs
  have hb' := hσt
  set p := restrPt B' (ϕ.obj a) (isOpen_germSet' hΦ hΨ a σ) (mem_germSet' hΦ hΨ σ hσs hσt)
    (hΦ.smooth_obj hs) with hp
  have hpV : p.c.φ.source ⊆ germSet' hΦ hΨ a σ := restrPt_sub _ _ _ _
  have hpa : p.c.φ.source ⊆ hΦ.locSet' a := fun y hy => (hpV hy).1
  have hpm : p.c.φ.source ⊆ (X'.sheetAt σ).srcSet := fun y hy => (hpV hy).2.1
  set q := (E'.morIso σ).pullPt p hpm (mem_tgtSet hb') (E'.morIso_ϕ_eq ha' hb') with hq
  have hqs : q.c.φ.source ⊆ hΨ.locSet' a := by
    rintro y ⟨hyU, hyp⟩
    have := (hpV hyp).2.2
    change (E'.morIso σ).g ((E'.morIso σ).ϕ y) ∈ hΨ.locSet' a at this
    rwa [(E'.morIso σ).base.left_inv y hyU] at this
  set A := (hΦ.locIso a).mpullPt p hpa (hΦ.mem_locSet a) rfl with hA
  set Bq := (hΨ.locIso a).mpullPt q hqs (hΨ.mem_locSet a) rfl with hBq
  set t := (orPt B' (ϕ.obj a) (hΦ.smooth_obj hs)).transferK p κ
  have e1 : hΦ.eK a hs κ = A.transferK (orPt B a hs) t := (hΦ.eK_eq hs p hpa κ).trans rfl
  have e2 : hΨ.eK a hs (E'.morKx σ ha' hb' (hΦ.smooth_obj hs) (hΨ.smooth_obj hs) κ) =
      Bq.transferK (orPt B a hs) t := by
    rw [E'.morKx_eq σ ha' hb' (hΦ.smooth_obj hs) (hΨ.smooth_obj hs) p hpm,
      hΨ.eK_eq hs q hqs]
    exact congrArg (Bq.transferK (orPt B a hs))
      ((q.transferK_trans_apply (orPt B' (ψ.obj a) (hΨ.smooth_obj hs)) q t).trans
        (q.transferK_self_apply t))
  have h4 := StrongBundle.LocalIso.transferK_mpullPt₃ (L := E'.morIso σ)
    (L₂ := hΨ.locIso a) (M := hΦ.locIso a) p hpm (mem_tgtSet hb') (E'.morIso_ϕ_eq ha' hb') hqs
    (hΨ.mem_locSet a) rfl hpa (hΦ.mem_locSet a) rfl hG t
  have e3 : Bq.transferK (orPt B a hs) t = A.transferK (orPt B a hs) t :=
    (congrArg (Bq.transferK (orPt B a hs)) (Subtype.ext h4).symm).trans
      (ChartPoint.transferK_trans_apply A Bq (orPt B a hs) t)
  exact e2.trans (e3.trans e1.symm)

section Or

variable {f : Obj → W} {f' : Obj' → W'} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hpbΦ : f = hΦ.pullback f')
  (hpbΨ : f = hΨ.pullback f') (hsec : B.HasScPlusSectionsThrough)
  (hsec' : B'.HasScPlusSectionsThrough)

include hG in
/-- **The identifications of orientations of `Φ` and `Ψ` at `a` differ by `σ_*`**, for
`σ : ϕ(a) → ψ(a)` with `Φ̂'_σ ∘ Ψ = Φ` near `a`. -/
theorem orEqv_of_germ (hs : a ∈ X.PObj.smoothSet)
    (o : Orx f' hF'.2 (ϕ.obj a) (hΦ.smooth_obj hs)) :
    hΨ.orEqv hF hF' hpbΨ hsec hsec' a hs (E'.orMor hF' hsec' σ hσs hσt (hΦ.smooth_obj hs)
      (hΨ.smooth_obj hs) o) = hΦ.orEqv hF hF' hpbΦ hsec hsec' a hs o := by
  have m1 := E'.morTx_mem hF' hsec' σ hσs hσt (hΦ.smooth_obj hs) (hΨ.smooth_obj hs)
  have m2 := hΨ.eT_mem hF hF' hpbΨ hsec hsec' hs
  rw [hΨ.orEqv_apply, E'.orMor_apply, hΦ.orEqv_apply]
  refine (LineOrientation.conj_trans
    (hC' := (orPt B' (ψ.obj a) (hΨ.smooth_obj hs)).isFredholm_of_mem_linSet hF'.2)
    (hC'' := (orPt B a hs).isFredholm_of_mem_linSet hF.2) _ _ _ _ m1 m2
    (conj_mem_trans _ _ _ _ m1 m2) o).trans ?_
  exact LineOrientation.conj_congr (fun v => eT_of_germ hΦ hΨ σ hσs hσt hG hs v)
    (fun κ => eK_of_germ hΦ hΨ σ hσs hσt hG hs κ) _ _ o

/-- **`Φ_*` and `Ψ_*` agree on `|O_f|` when `|Φ| = |Ψ|`**, for a target with the local
regularity property (Definition 8.4.2 as `IsLRLocal`): the point `(a, o)` goes to
`(ϕ(a), …)` and `(ψ(a), …)`, related by the morphism `α_a` of Proposition 10.4.7. -/
theorem orRel_orSpaceMap_of_orbitMap_eq (hΦΨ : Φ.orbitMap = Ψ.orbitMap) (hE' : E'.IsLRLocal)
    (p : OrSpace f hF.2) :
    E'.OrRel hF' hsec' (hΦ.orSpaceMap hF hF' hpbΦ hsec hsec' p)
      (hΨ.orSpaceMap hF hF' hpbΨ hsec hsec' p) := by
  set a := X.PObj.smoothVal p.1 with ha
  have hs : a ∈ X.PObj.smoothSet := X.PObj.smoothVal_mem p.1
  obtain ⟨R, -, α, hα, hfam⟩ :=
    EpStrongBundle.proposition_10_4_7 hΦ hΨ hΦΨ hE' a isOpen_univ (mem_univ a)
  have hG := germ_of_family hΦ hΨ R.isOpen_U hα.continuousOn hfam R.mem_U
  obtain ⟨hσs, hσt, -⟩ := hfam a R.mem_U
  refine ⟨α a, hσs, hσt, ?_⟩
  change E'.orMor hF' hsec' (α a) hσs hσt (hΦ.smooth_obj hs) (hΨ.smooth_obj hs)
      ((hΦ.orEqv hF hF' hpbΦ hsec hsec' _ hs).symm p.2) =
    (hΨ.orEqv hF hF' hpbΨ hsec hsec' _ hs).symm p.2
  rw [Equiv.eq_symm_apply, orEqv_of_germ hΦ hΨ (α a) hσs hσt hG hF hF' hpbΦ hpbΨ hsec hsec',
    Equiv.apply_symm_apply]

/-- **Theorem 12.5.7 for strong bundle equivalences with the same orbit map**: if
`|Φ| = |Ψ| : |W| → |W'|` and `W'` has the local regularity property (Definition 8.4.2 as
`IsLRLocal`), then `|Φ|_* = |Ψ|_*` on `|O_f|`, for `f = Φ^* f' = Ψ^* f'`. -/
theorem orbitOrMap_eq_of_orbitMap_eq (hΦΨ : Φ.orbitMap = Ψ.orbitMap) (hE' : E'.IsLRLocal)
    (c : Quot (E.OrRel hF hsec)) :
    hΦ.orbitOrMap hF hF' hpbΦ hsec hsec' c = hΨ.orbitOrMap hF hF' hpbΨ hsec hsec' c := by
  induction c using Quot.ind with
  | mk p =>
    exact Quot.sound
      (orRel_orSpaceMap_of_orbitMap_eq hΦ hΨ hF hF' hpbΦ hpbΨ hsec hsec' hΦΨ hE' p)

end Or

include hΦ hΨ in
/-- `|ϕ| = |ψ|` on `|X_∞|` when `|Φ| = |Ψ|` on `|W|`. -/
theorem smoothOrbitMap_eq_of_orbitMap_eq (hΦΨ : Φ.orbitMap = Ψ.orbitMap)
    (c : Quot X.SmoothRel) : hΦ.smoothOrbitMap c = hΨ.smoothOrbitMap c := by
  induction c using Quot.ind with
  | mk x =>
    obtain ⟨σ, h1, h2⟩ := X'.π_eq_π_iff.1 (EpStrongBundle.π_base_eq_of_orbitMap_eq
      hΦ.isStrongBundleFunctor hΨ.isStrongBundleFunctor hΦΨ (X.PObj.smoothVal x))
    exact Quot.sound ⟨σ, h1, h2⟩

end EpStrongBundle.IsStrongBundleEquivalence

end Germ

/-! ### Two diagrams refined by one middle bundle -/

section Rep

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {B : StrongBundle X.PObj P} [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type u} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  {B' : StrongBundle X'.PObj P'} [ParacompactSpace (pullbackSpace P' X'.src)]
  {Obj₁ Mor₁ : Type u} [TopologicalSpace Obj₁] [T2Space Obj₁] [ParacompactSpace Obj₁]
  [TopologicalSpace Mor₁] [T2Space Mor₁] [ParacompactSpace Mor₁] {X₁ : EpGroupoid Obj₁ Mor₁}
  {V₁ : Type u} [TopologicalSpace V₁] [T2Space V₁] [ParacompactSpace V₁] {P₁ : V₁ → Obj₁}
  [∀ x, AddCommGroup (P₁ ⁻¹' {x})] [∀ x, Module ℝ (P₁ ⁻¹' {x})]
  {B₁ : StrongBundle X₁.PObj P₁} [ParacompactSpace (pullbackSpace P₁ X₁.src)]
  {Obj₂ Mor₂ : Type u} [TopologicalSpace Obj₂] [T2Space Obj₂] [ParacompactSpace Obj₂]
  [TopologicalSpace Mor₂] [T2Space Mor₂] [ParacompactSpace Mor₂] {X₂ : EpGroupoid Obj₂ Mor₂}
  {V₂ : Type u} [TopologicalSpace V₂] [T2Space V₂] [ParacompactSpace V₂] {P₂ : V₂ → Obj₂}
  [∀ x, AddCommGroup (P₂ ⁻¹' {x})] [∀ x, Module ℝ (P₂ ⁻¹' {x})]
  {B₂ : StrongBundle X₂.PObj P₂} [ParacompactSpace (pullbackSpace P₂ X₂.src)]
  {Obj₃ Mor₃ : Type u} [TopologicalSpace Obj₃] [T2Space Obj₃] [ParacompactSpace Obj₃]
  [TopologicalSpace Mor₃] [T2Space Mor₃] [ParacompactSpace Mor₃] {X₃ : EpGroupoid Obj₃ Mor₃}
  {V₃ : Type u} [TopologicalSpace V₃] [T2Space V₃] [ParacompactSpace V₃] {P₃ : V₃ → Obj₃}
  [∀ x, AddCommGroup (P₃ ⁻¹' {x})] [∀ x, Module ℝ (P₃ ⁻¹' {x})]
  {B₃ : StrongBundle X₃.PObj P₃} [ParacompactSpace (pullbackSpace P₃ X₃.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {E₁ : EpStrongBundle X₁ B₁}
  {E₂ : EpStrongBundle X₂ B₂} {E₃ : EpStrongBundle X₃ B₃}

namespace EpStrongBundle.IsStrongBundleEquivalence

variable {ϕ₁ : EpFunctor X₁ X} {Φ₁ : EpFunctor E₁.toEpGroupoid E.toEpGroupoid}
  {ϕ₂ : EpFunctor X₁ X'} {Φ₂ : EpFunctor E₁.toEpGroupoid E'.toEpGroupoid}
  {γ₁ : EpFunctor X₂ X} {Γ₁ : EpFunctor E₂.toEpGroupoid E.toEpGroupoid}
  {γ₂ : EpFunctor X₂ X'} {Γ₂ : EpFunctor E₂.toEpGroupoid E'.toEpGroupoid}
  {η₁ : EpFunctor X₃ X₁} {H₁ : EpFunctor E₃.toEpGroupoid E₁.toEpGroupoid}
  {η₂ : EpFunctor X₃ X₂} {H₂ : EpFunctor E₃.toEpGroupoid E₂.toEpGroupoid}
  (h₁ : E₁.IsStrongBundleEquivalence E ϕ₁ Φ₁) (h₂ : E₁.IsStrongBundleEquivalence E' ϕ₂ Φ₂)
  (g₁ : E₂.IsStrongBundleEquivalence E γ₁ Γ₁) (g₂ : E₂.IsStrongBundleEquivalence E' γ₂ Γ₂)
  (hH₁ : E₃.IsStrongBundleEquivalence E₁ η₁ H₁) (hH₂ : E₃.IsStrongBundleEquivalence E₂ η₂ H₂)
  (ζ₁ : E₃.StrongBundleNatTrans E (γ₁.comp η₂) (ϕ₁.comp η₁) (Γ₁.comp H₂) (Φ₁.comp H₁))
  {f : Obj → W} {f' : Obj' → W'} {f₁ : Obj₁ → V₁} {f₂ : Obj₂ → V₂} {f₃ : Obj₃ → V₃}
  (hF : E.IsScFredholmSectionFunctor f) (hF' : E'.IsScFredholmSectionFunctor f')
  (hF₁ : E₁.IsScFredholmSectionFunctor f₁) (hF₂ : E₂.IsScFredholmSectionFunctor f₂)
  (hF₃ : E₃.IsScFredholmSectionFunctor f₃)
  (hpb₁ : f₁ = h₁.pullback f) (hpb₂ : f₁ = h₂.pullback f')
  (hqb₁ : f₂ = g₁.pullback f) (hqb₂ : f₂ = g₂.pullback f')
  (hpbH₁ : f₃ = hH₁.pullback f₁) (hpbH₂ : f₃ = hH₂.pullback f₂)
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)
  (hsec₁ : B₁.HasScPlusSectionsThrough) (hsec₂ : B₂.HasScPlusSectionsThrough)
  (hsec₃ : B₃.HasScPlusSectionsThrough)

include ζ₁ hH₁ hH₂ hF₃ hpbH₁ hpbH₂ hsec₃ in
/-- **Theorem 12.5.7, two diagrams with the same map of orbit spaces**, p. 595 (2017:
Theorem 12.12): let `W ←Φ₁– V₁ –Φ₂→ W'` and `W ←Γ₁– V₂ –Γ₂→ W'` be diagrams of strong bundle
equivalences with `Φ₁^* f = Φ₂^* f'`, `Γ₁^* f = Γ₂^* f'`, and `H₁ : V₃ → V₁`, `H₂ : V₃ → V₂`
strong bundle equivalences with `Γ₁ ∘ H₂ ≃ Φ₁ ∘ H₁` (Definition 10.4.8) and
`|Φ₂ ∘ H₁| = |Γ₂ ∘ H₂|` on `|V₃|`.  If `W'` has the local regularity property (Definition 8.4.2
as `IsLRLocal`), the two diagrams induce the same map `|O_f| → |O_{f'}|`. -/
theorem theorem_12_5_7_rep_indep_of_orbitMap_eq
    (horb : (Φ₂.comp H₁).orbitMap = (Γ₂.comp H₂).orbitMap) (hE' : E'.IsLRLocal)
    (x : Quot (E.OrRel hF hsec)) :
    (Equiv.ofBijective _ (h₂.orbitOrMap_bijective hF₁ hF' hpb₂ hsec₁ hsec'))
      ((Equiv.ofBijective _ (h₁.orbitOrMap_bijective hF₁ hF hpb₁ hsec₁ hsec)).symm x) =
    (Equiv.ofBijective _ (g₂.orbitOrMap_bijective hF₂ hF' hqb₂ hsec₂ hsec'))
      ((Equiv.ofBijective _ (g₁.orbitOrMap_bijective hF₂ hF hqb₁ hsec₂ hsec)).symm x) := by
  have k₁ := h₁.comp hH₁
  have k₂ := h₂.comp hH₁
  have l₁ := g₁.comp hH₂
  have l₂ := g₂.comp hH₂
  have hk₁ : f₃ = k₁.pullback f := pullback_comp_of hH₁ h₁ hF hpbH₁ hpb₁
  have hk₂ : f₃ = k₂.pullback f' := pullback_comp_of hH₁ h₂ hF' hpbH₁ hpb₂
  have hl₁ : f₃ = l₁.pullback f := pullback_comp_of hH₂ g₁ hF hpbH₂ hqb₁
  have hl₂ : f₃ = l₂.pullback f' := pullback_comp_of hH₂ g₂ hF' hpbH₂ hqb₂
  -- both sides through the middle `V₃`
  have e₁ := theorem_12_5_7_refinement h₁ h₂ k₁ k₂ hH₁
    (StrongBundleNatTrans.refl k₁.isStrongBundleFunctor)
    (StrongBundleNatTrans.refl k₂.isStrongBundleFunctor) hF hF' hF₁ hF₃ hpb₁ hpb₂ hpbH₁ hk₁ hk₂
    hsec hsec' hsec₁ hsec₃ x
  have e₂ := theorem_12_5_7_refinement g₁ g₂ l₁ l₂ hH₂
    (StrongBundleNatTrans.refl l₁.isStrongBundleFunctor)
    (StrongBundleNatTrans.refl l₂.isStrongBundleFunctor) hF hF' hF₂ hF₃ hqb₁ hqb₂ hpbH₂ hl₁ hl₂
    hsec hsec' hsec₂ hsec₃ x
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  set d₁ := Equiv.ofBijective _ (k₁.orbitOrMap_bijective hF₃ hF hk₁ hsec₃ hsec)
  set d₂ := Equiv.ofBijective _ (l₁.orbitOrMap_bijective hF₃ hF hl₁ hsec₃ hsec)
  obtain ⟨c, rfl⟩ := d₂.surjective x
  have hc : d₁ c = d₂ c :=
    (orbitOrMap_nat l₁ k₁ ζ₁ hF₃ hF hl₁ hk₁ hsec₃ hsec c).symm
  rw [← hc, Equiv.symm_apply_apply, hc, Equiv.symm_apply_apply]
  exact orbitOrMap_eq_of_orbitMap_eq k₂ l₂ hF₃ hF' hk₂ hl₂ hsec₃ hsec' horb hE' c

end EpStrongBundle.IsStrongBundleEquivalence

end Rep

end Polyfold
