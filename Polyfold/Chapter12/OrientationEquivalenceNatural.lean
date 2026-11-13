import Polyfold.Chapter12.OrientationEquivalenceComp
import Polyfold.Chapter10.StrongBundleWeakFibredProduct

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, **Theorem 12.5.7** (2017: Theorem 12.12): the maps of orientations do not change
when a strong bundle equivalence is replaced by a naturally equivalent one (Definition 10.4.8;
left to the reader in the text, as part of the independence of the representative).

For strong bundle equivalences `Φ, Ψ : W → W'` over `ϕ, ψ` and `T : Φ ≃ Ψ` covering
`τ : ϕ → ψ`, with `f = Φ^* f' = Ψ^* f'`:

* `germ_nat`: near `a`, `Φ̂'_{τ(a)} ∘ Ψ = Φ` (base and bundle maps);
* `eT_nat`, `eK_nat`, `orEqv_nat`: the identification `Or^{f'}_{ψ(a)} ≃ Or^f_a` of `Ψ` after
  `τ(a)_*` is that of `Φ`;
* `orbitOrMap_nat`, `smoothOrbitMap_nat`: `|Φ|_* = |Ψ|_*` on `|O_f|` and `|ϕ| = |ψ|` on `|X_∞|`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

open StrongRetr

universe u

section Nat

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
  (θ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ)

theorem continuous_natApp : Continuous θ.τ.app :=
  continuousOn_univ.1 θ.τ.isScSmoothMap_app.continuousOn

include hΦ hΨ in
/-- **The local isomorphisms of `Φ` and `Ψ` correspond under `τ(a) : ϕ(a) → ψ(a)`**: near `a`,
`Φ̂'_{τ(a)} ∘ Ψ = Φ` (the inverse direction of `τ(a)`, `EpStrongBundle.morIso`), on the base
because `τ(y)` lies in the sheet of `τ(a)` and on the bundle because
`T(w) = (τ(P w), Φ(w)) : Φ(w) → Ψ(w)`. -/
theorem germ_nat (a : Obj) :
    ∃ N : Set Obj, IsOpen N ∧ a ∈ N ∧
      (∀ y ∈ N, (E'.morIso (θ.τ.app a)).ϕ ((hΨ.locIso a).ϕ y) = (hΦ.locIso a).ϕ y) ∧
      ∀ w, P w ∈ N →
        (E'.morIso (θ.τ.app a)).Φ ((hΨ.locIso a).Φ w) = (hΦ.locIso a).Φ w := by
  set S := X'.sheetAt (θ.τ.app a) with hS
  refine ⟨θ.τ.app ⁻¹' S.carrier,
    S.isScDiffeoOn_tgt.isOpen_source.preimage (continuous_natApp θ), X'.mem_sheetAt _, ?_, ?_⟩
  · intro y hy
    change X'.src (S.tgtInv (ψ.obj y)) = ϕ.obj y
    rw [← θ.τ.tgt_app y, S.isScDiffeoOn_tgt.left_inv _ hy, θ.τ.src_app]
  · intro w hw
    have hcov : P' (Ψ.obj w) = ψ.obj (P w) := hΨ.covers w
    have hτ : S.tgtInv (ψ.obj (P w)) = θ.τ.app (P w) := by
      rw [← θ.τ.tgt_app (P w)]; exact S.isScDiffeoOn_tgt.left_inv _ hw
    have hT : P' (Ψ.obj w) ∈ S.tgtSet := by
      rw [hcov, ← θ.τ.tgt_app (P w)]; exact S.isScDiffeoOn_tgt.mapsTo hw
    change E'.sectionAct (morInvSec X' (θ.τ.app a)) (Ψ.obj w) = Φ.obj w
    rw [E'.sectionAct_of_eq _ (src_morInvSec (θ.τ.app a) hT).symm]
    have hinv : morInvSec X' (θ.τ.app a) (P' (Ψ.obj w)) = X'.inv (θ.τ.app (P w)) := by
      change X'.inv (S.tgtInv (P' (Ψ.obj w))) = _
      rw [hcov, hτ]
    have hΦw : P' (Φ.obj w) = X'.src (θ.τ.app (P w)) := by
      rw [θ.τ.src_app]; exact hΦ.covers w
    have hΨw : Ψ.obj w = E'.μ ⟨(θ.τ.app (P w), Φ.obj w), hΦw⟩ := by
      rw [← θ.tgt_T w]
      exact E'.μ_congr (θ.T_val w)
    have hv : P' (Ψ.obj w) = X'.src (X'.inv (θ.τ.app (P w))) := by
      rw [X'.src_inv, θ.τ.tgt_app]; exact hcov
    refine (E'.μ_congr
      (q := ⟨(morInvSec X' (θ.τ.app a) (P' (Ψ.obj w)), Ψ.obj w),
        (src_morInvSec (θ.τ.app a) hT).symm⟩) (q' := ⟨(X'.inv (θ.τ.app (P w)), Ψ.obj w), hv⟩)
      (Prod.ext hinv rfl)).trans ?_
    exact E'.μ_inv_eq_of_eq_μ (ψ := θ.τ.app (P w)) hv hΦw hΨw

/-- The open set at `ϕ(a)` used to compare `Φ` and `Ψ` along `τ(a)`. -/
def natSet' (a : Obj) : Set Obj' :=
  hΦ.locSet' a ∩
    ((X'.sheetAt (θ.τ.app a)).srcSet ∩ (E'.morIso (θ.τ.app a)).g ⁻¹' hΨ.locSet' a)

theorem isOpen_natSet' (a : Obj) : IsOpen (natSet' hΦ hΨ θ a) :=
  (hΦ.isOpen_locSet' a).inter
    ((E'.morIso (θ.τ.app a)).base.isScSmoothOn_inv.continuousOn.isOpen_inter_preimage
      (isOpen_srcSet _) (hΨ.isOpen_locSet' a))

theorem mem_natSet' (a : Obj) : ϕ.obj a ∈ natSet' hΦ hΨ θ a := by
  have ha' := θ.τ.src_app a
  have hb' := θ.τ.tgt_app a
  refine ⟨hΦ.obj_mem_locSet' a, mem_srcSet ha', ?_⟩
  change (E'.morIso (θ.τ.app a)).g (ϕ.obj a) ∈ hΨ.locSet' a
  rw [← E'.morIso_ϕ_eq ha' hb', (E'.morIso (θ.τ.app a)).base.left_inv _ (mem_tgtSet hb')]
  exact hΨ.obj_mem_locSet' a

/-- **`eT` of `Ψ` after `T τ(a)` is `eT` of `Φ`**: `T_{ϕ(a)}X' → T_{ψ(a)}X' → T_aX`. -/
theorem eT_nat {a : Obj} (hs : a ∈ X.PObj.smoothSet)
    (v : ↥(orPt B' (ϕ.obj a) (hΦ.smooth_obj hs)).T) :
    hΨ.eT a hs (E'.morTx (θ.τ.app a) (θ.τ.src_app a) (θ.τ.tgt_app a) (hΦ.smooth_obj hs)
      (hΨ.smooth_obj hs) v) = hΦ.eT a hs v := by
  have ha' := θ.τ.src_app a
  have hb' := θ.τ.tgt_app a
  set p := restrPt B' (ϕ.obj a) (isOpen_natSet' hΦ hΨ θ a) (mem_natSet' hΦ hΨ θ a)
    (hΦ.smooth_obj hs) with hp
  have hpV : p.c.φ.source ⊆ natSet' hΦ hΨ θ a := restrPt_sub _ _ _ _
  have hpa : p.c.φ.source ⊆ hΦ.locSet' a := fun y hy => (hpV hy).1
  have hpm : p.c.φ.source ⊆ (X'.sheetAt (θ.τ.app a)).srcSet := fun y hy => (hpV hy).2.1
  set q := (E'.morIso (θ.τ.app a)).pullPt p hpm (mem_tgtSet hb') (E'.morIso_ϕ_eq ha' hb')
    with hq
  have hqs : q.c.φ.source ⊆ hΨ.locSet' a := by
    rintro y ⟨hyU, hyp⟩
    have := (hpV hyp).2.2
    change (E'.morIso (θ.τ.app a)).g ((E'.morIso (θ.τ.app a)).ϕ y) ∈ hΨ.locSet' a at this
    rwa [(E'.morIso (θ.τ.app a)).base.left_inv y hyU] at this
  set A := (hΦ.locIso a).mpullPt p hpa (hΦ.mem_locSet a) rfl with hA
  set Bq := (hΨ.locIso a).mpullPt q hqs (hΨ.mem_locSet a) rfl with hBq
  set t := (orPt B' (ϕ.obj a) (hΦ.smooth_obj hs)).transferT p v
  have e1 : hΦ.eT a hs v = A.transferT (orPt B a hs) t := (hΦ.eT_eq hs p hpa v).trans rfl
  have e2 : hΨ.eT a hs (E'.morTx (θ.τ.app a) ha' hb' (hΦ.smooth_obj hs) (hΨ.smooth_obj hs) v) =
      Bq.transferT (orPt B a hs) t := by
    rw [E'.morTx_eq (θ.τ.app a) ha' hb' (hΦ.smooth_obj hs) (hΨ.smooth_obj hs) p hpm,
      hΨ.eT_eq hs q hqs]
    exact congrArg (Bq.transferT (orPt B a hs))
      ((q.transferT_trans_apply (orPt B' (ψ.obj a) (hΨ.smooth_obj hs)) q t).trans
        (q.transferT_self_apply t))
  have h4 := StrongBundle.LocalIso.transferT_mpullPt₃ (L := E'.morIso (θ.τ.app a))
    (L₂ := hΨ.locIso a) (M := hΦ.locIso a) p hpm (mem_tgtSet hb') (E'.morIso_ϕ_eq ha' hb') hqs
    (hΨ.mem_locSet a) rfl hpa (hΦ.mem_locSet a) rfl (germ_nat hΦ hΨ θ a) t
  have e3 : Bq.transferT (orPt B a hs) t = A.transferT (orPt B a hs) t :=
    (congrArg (Bq.transferT (orPt B a hs)) (Subtype.ext h4).symm).trans
      (ChartPoint.transferT_trans_apply A Bq (orPt B a hs) t)
  exact e2.trans (e3.trans e1.symm)

/-- **`eK` of `Ψ` after `μ(τ(a), ·)` is `eK` of `Φ`.** -/
theorem eK_nat {a : Obj} (hs : a ∈ X.PObj.smoothSet)
    (κ : ↥(orPt B' (ϕ.obj a) (hΦ.smooth_obj hs)).K) :
    hΨ.eK a hs (E'.morKx (θ.τ.app a) (θ.τ.src_app a) (θ.τ.tgt_app a) (hΦ.smooth_obj hs)
      (hΨ.smooth_obj hs) κ) = hΦ.eK a hs κ := by
  have ha' := θ.τ.src_app a
  have hb' := θ.τ.tgt_app a
  set p := restrPt B' (ϕ.obj a) (isOpen_natSet' hΦ hΨ θ a) (mem_natSet' hΦ hΨ θ a)
    (hΦ.smooth_obj hs) with hp
  have hpV : p.c.φ.source ⊆ natSet' hΦ hΨ θ a := restrPt_sub _ _ _ _
  have hpa : p.c.φ.source ⊆ hΦ.locSet' a := fun y hy => (hpV hy).1
  have hpm : p.c.φ.source ⊆ (X'.sheetAt (θ.τ.app a)).srcSet := fun y hy => (hpV hy).2.1
  set q := (E'.morIso (θ.τ.app a)).pullPt p hpm (mem_tgtSet hb') (E'.morIso_ϕ_eq ha' hb')
    with hq
  have hqs : q.c.φ.source ⊆ hΨ.locSet' a := by
    rintro y ⟨hyU, hyp⟩
    have := (hpV hyp).2.2
    change (E'.morIso (θ.τ.app a)).g ((E'.morIso (θ.τ.app a)).ϕ y) ∈ hΨ.locSet' a at this
    rwa [(E'.morIso (θ.τ.app a)).base.left_inv y hyU] at this
  set A := (hΦ.locIso a).mpullPt p hpa (hΦ.mem_locSet a) rfl with hA
  set Bq := (hΨ.locIso a).mpullPt q hqs (hΨ.mem_locSet a) rfl with hBq
  set t := (orPt B' (ϕ.obj a) (hΦ.smooth_obj hs)).transferK p κ
  have e1 : hΦ.eK a hs κ = A.transferK (orPt B a hs) t := (hΦ.eK_eq hs p hpa κ).trans rfl
  have e2 : hΨ.eK a hs (E'.morKx (θ.τ.app a) ha' hb' (hΦ.smooth_obj hs) (hΨ.smooth_obj hs) κ) =
      Bq.transferK (orPt B a hs) t := by
    rw [E'.morKx_eq (θ.τ.app a) ha' hb' (hΦ.smooth_obj hs) (hΨ.smooth_obj hs) p hpm,
      hΨ.eK_eq hs q hqs]
    exact congrArg (Bq.transferK (orPt B a hs))
      ((q.transferK_trans_apply (orPt B' (ψ.obj a) (hΨ.smooth_obj hs)) q t).trans
        (q.transferK_self_apply t))
  have h4 := StrongBundle.LocalIso.transferK_mpullPt₃ (L := E'.morIso (θ.τ.app a))
    (L₂ := hΨ.locIso a) (M := hΦ.locIso a) p hpm (mem_tgtSet hb') (E'.morIso_ϕ_eq ha' hb') hqs
    (hΨ.mem_locSet a) rfl hpa (hΦ.mem_locSet a) rfl (germ_nat hΦ hΨ θ a) t
  have e3 : Bq.transferK (orPt B a hs) t = A.transferK (orPt B a hs) t :=
    (congrArg (Bq.transferK (orPt B a hs)) (Subtype.ext h4).symm).trans
      (ChartPoint.transferK_trans_apply A Bq (orPt B a hs) t)
  exact e2.trans (e3.trans e1.symm)

section Or

variable {f : Obj → W} {f' : Obj' → W'} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hpbΦ : f = hΦ.pullback f')
  (hpbΨ : f = hΨ.pullback f') (hsec : B.HasScPlusSectionsThrough)
  (hsec' : B'.HasScPlusSectionsThrough)

/-- **Theorem 12.5.7, invariance under natural equivalence at a point**: for `T : Φ ≃ Ψ`
(Definition 10.4.8) covering `τ`, the identification of `Ψ` after `τ(a)_*` is that of `Φ`. -/
theorem orEqv_nat {a : Obj} (hs : a ∈ X.PObj.smoothSet)
    (o : Orx f' hF'.2 (ϕ.obj a) (hΦ.smooth_obj hs)) :
    hΨ.orEqv hF hF' hpbΨ hsec hsec' a hs (E'.orMor hF' hsec' (θ.τ.app a) (θ.τ.src_app a)
      (θ.τ.tgt_app a) (hΦ.smooth_obj hs) (hΨ.smooth_obj hs) o) =
        hΦ.orEqv hF hF' hpbΦ hsec hsec' a hs o := by
  have m1 := E'.morTx_mem hF' hsec' (θ.τ.app a) (θ.τ.src_app a) (θ.τ.tgt_app a)
    (hΦ.smooth_obj hs) (hΨ.smooth_obj hs)
  have m2 := hΨ.eT_mem hF hF' hpbΨ hsec hsec' hs
  rw [hΨ.orEqv_apply, E'.orMor_apply, hΦ.orEqv_apply]
  refine (LineOrientation.conj_trans
    (hC' := (orPt B' (ψ.obj a) (hΨ.smooth_obj hs)).isFredholm_of_mem_linSet hF'.2)
    (hC'' := (orPt B a hs).isFredholm_of_mem_linSet hF.2) _ _ _ _ m1 m2
    (conj_mem_trans _ _ _ _ m1 m2) o).trans ?_
  exact LineOrientation.conj_congr (fun v => eT_nat hΦ hΨ θ hs v) (fun κ => eK_nat hΦ hΨ θ hs κ)
    _ _ o

include θ in
/-- **`Φ_*` and `Ψ_*` agree on `|O_f|`** for naturally equivalent `Φ ≃ Ψ`: `(a, o)` goes to
`(ϕ(a), …)` and `(ψ(a), …)`, related by `τ(a)`. -/
theorem orRel_orSpaceMap_nat (p : OrSpace f hF.2) :
    E'.OrRel hF' hsec' (hΦ.orSpaceMap hF hF' hpbΦ hsec hsec' p)
      (hΨ.orSpaceMap hF hF' hpbΨ hsec hsec' p) := by
  refine ⟨θ.τ.app (X.PObj.smoothVal p.1), θ.τ.src_app _, θ.τ.tgt_app _, ?_⟩
  change E'.orMor hF' hsec' (θ.τ.app _) (θ.τ.src_app _) (θ.τ.tgt_app _)
      (hΦ.smooth_obj (X.PObj.smoothVal_mem p.1)) (hΨ.smooth_obj (X.PObj.smoothVal_mem p.1))
      ((hΦ.orEqv hF hF' hpbΦ hsec hsec' _ (X.PObj.smoothVal_mem p.1)).symm p.2) =
    (hΨ.orEqv hF hF' hpbΨ hsec hsec' _ (X.PObj.smoothVal_mem p.1)).symm p.2
  rw [Equiv.eq_symm_apply, orEqv_nat hΦ hΨ θ hF hF' hpbΦ hpbΨ hsec hsec',
    Equiv.apply_symm_apply]

include θ in
/-- **Invariance of `|f̄|_*` under natural equivalence**: `|Φ|_* = |Ψ|_*` on `|O_f|`. -/
theorem orbitOrMap_nat (c : Quot (E.OrRel hF hsec)) :
    hΦ.orbitOrMap hF hF' hpbΦ hsec hsec' c = hΨ.orbitOrMap hF hF' hpbΨ hsec hsec' c := by
  induction c using Quot.ind with
  | mk p => exact Quot.sound (orRel_orSpaceMap_nat hΦ hΨ θ hF hF' hpbΦ hpbΨ hsec hsec' p)

end Or

include θ in
/-- `|ϕ| = |ψ|` on `|X_∞|` for naturally equivalent `ϕ ≃ ψ`. -/
theorem smoothOrbitMap_nat (c : Quot X.SmoothRel) :
    hΦ.smoothOrbitMap c = hΨ.smoothOrbitMap c := by
  induction c using Quot.ind with
  | mk x => exact Quot.sound ⟨θ.τ.app (X.PObj.smoothVal x), θ.τ.src_app _, θ.τ.tgt_app _⟩

end EpStrongBundle.IsStrongBundleEquivalence

end Nat

end Polyfold
