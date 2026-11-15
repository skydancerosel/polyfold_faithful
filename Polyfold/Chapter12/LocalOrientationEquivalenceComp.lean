import Polyfold.Chapter12.LocalOrientationEquivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, **Theorem 12.5.7**: functoriality of the maps of orientations under composition of
strong bundle equivalences and their invariance under natural equivalence (left to the reader
in the text), for the linearizations made with local sc⁺-sections.

## The text, paraphrased

A generalized strong bundle isomorphism is an equivalence class of diagrams of strong bundle
equivalences; two diagrams are equivalent if they have a common refinement up to natural
equivalence (Definition 10.4.8).  The maps of Theorem 12.5.7 are those of a representative.

## What is formalized

For the local orientation sets (tame object M-polyfolds and tame germ data only):

* `orEqvLoc_comp`, `orSpaceMapLoc_comp`, `orbitOrMapLoc_comp`: for strong bundle equivalences
  `Φ : W → W'`, `Ψ : W' → W''` with `f = Φ^* f'`, `f' = Ψ^* f''`, the identification
  `Or^{f''}_{ψϕ(a)} ≃ Or^f_a` of `Ψ ∘ Φ` is the composite of those of `Ψ` and `Φ`; hence
  `|Ψ ∘ Φ|_* = |Ψ|_* ∘ |Φ|_*` on `|O_f|`.
* `orEqvLoc_nat`, `orRelLoc_orSpaceMapLoc_nat`, `orbitOrMapLoc_nat`: for `T : Φ ≃ Ψ` covering
  `τ : ϕ → ψ` with `f = Φ^* f' = Ψ^* f'`, the identification of `Ψ` after `τ(a)_*` is that of
  `Φ`; hence `|Φ|_* = |Ψ|_*` on `|O_f|`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

open StrongRetr StrongBundle.LocalIso

universe u

section EquivComp

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

section Or

variable {f : Obj → W} {f' : Obj' → W'} {f'' : Obj'' → W''}
  (hF : E.IsScFredholmSectionFunctor f) (hF' : E'.IsScFredholmSectionFunctor f')
  (hF'' : E''.IsScFredholmSectionFunctor f'') (hpb : f = h.pullback f')
  (hpb' : f' = h'.pullback f'') (hX : X.PObj.IsTame) (hX' : X'.PObj.IsTame)
  (hX'' : X''.PObj.IsTame) (hfT : B.IsScFredholmSectionTame f)
  (hfT' : B'.IsScFredholmSectionTame f') (hfT'' : B''.IsScFredholmSectionTame f'')

/-- **Theorem 12.5.7, functoriality at a point**, for the local orientation sets: the
identification `Or^{f''}_{ψϕ(a)} ≃ Or^f_a` of `Ψ ∘ Φ` is that of `Φ` after that of `Ψ`. -/
theorem orEqvLoc_comp (a : Obj) (hs : a ∈ X.PObj.smoothSet)
    (o : OrxLoc hfT'' (ψ.obj (ϕ.obj a)) (h'.smooth_obj (h.smooth_obj hs))) :
    (h'.comp h).orEqvLoc (pullback_comp_of h h' hF'' hpb hpb') hfT hfT'' a hs o =
      h.orEqvLoc hpb hfT hfT' a hs
        (h'.orEqvLoc hpb' hfT' hfT'' (ϕ.obj a) (h.smooth_obj hs) o) :=
  (DFunLike.congr_fun (orLoc_triangle (L := h'.locIso (ϕ.obj a)) (L₂ := h.locIso a)
    (N := (h'.comp h).locIso a) hfT hfT' hfT'' (h'.eqOn_loc hpb' hfT''.isScSmooth.1 (ϕ.obj a))
    (h.eqOn_loc hpb hfT'.isScSmooth.1 a)
    ((h'.comp h).eqOn_loc (pullback_comp_of h h' hF'' hpb hpb') hfT''.isScSmooth.1 a)
    (h.mem_locSet a) ((h'.comp h).mem_locSet a) rfl (h'.mem_locSet (ϕ.obj a)) rfl rfl hs
    (h.smooth_obj hs) (h'.smooth_obj (h.smooth_obj hs)) (germ_comp h h' a)) o).symm

/-- **Functoriality on `O_f`**: `(Ψ ∘ Φ)_* = Ψ_* ∘ Φ_*`, `(a, o) ↦ (ψϕ(a), …)`. -/
theorem orSpaceMapLoc_comp (p : OrSpaceLoc hX hfT) :
    (h'.comp h).orSpaceMapLoc (pullback_comp_of h h' hF'' hpb hpb') hX hX'' hfT hfT'' p =
      h'.orSpaceMapLoc hpb' hX' hX'' hfT' hfT'' (h.orSpaceMapLoc hpb hX hX' hfT hfT' p) := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  change ((h'.comp h).orEqvLoc (pullback_comp_of h h' hF'' hpb hpb') hfT hfT'' _
      (X.PObj.smoothVal_mem p.1)).symm p.2 =
    (h'.orEqvLoc hpb' hfT' hfT'' _ (h.smooth_obj (X.PObj.smoothVal_mem p.1))).symm
      ((h.orEqvLoc hpb hfT hfT' _ (X.PObj.smoothVal_mem p.1)).symm p.2)
  refine (Equiv.symm_apply_eq _).2 ?_
  refine Eq.trans ?_ (orEqvLoc_comp h h' hF'' hpb hpb' hfT hfT' hfT'' _ _ _).symm
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- **Functoriality of `|f̄|_*` on `|O_f|`**: `|Ψ ∘ Φ|_* = |Ψ|_* ∘ |Φ|_*`. -/
theorem orbitOrMapLoc_comp (c : Quot (E.OrRelLoc hX hF hfT)) :
    (h'.comp h).orbitOrMapLoc hF hF'' (pullback_comp_of h h' hF'' hpb hpb')
        hX hX'' hfT hfT'' c =
      h'.orbitOrMapLoc hF' hF'' hpb' hX' hX'' hfT' hfT''
        (h.orbitOrMapLoc hF hF' hpb hX hX' hfT hfT' c) := by
  induction c using Quot.ind with
  | mk p => exact congrArg (Quot.mk _) (orSpaceMapLoc_comp h h' hF'' hpb hpb' hX hX' hX'' hfT
      hfT' hfT'' p)


end Or

end EpStrongBundle.IsStrongBundleEquivalence

end EquivComp

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

section Or

variable {f : Obj → W} {f' : Obj' → W'} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hpbΦ : f = hΦ.pullback f')
  (hpbΨ : f = hΨ.pullback f') (hX : X.PObj.IsTame) (hX' : X'.PObj.IsTame)
  (hfT : B.IsScFredholmSectionTame f) (hfT' : B'.IsScFredholmSectionTame f')

/-- **Theorem 12.5.7, invariance under natural equivalence at a point**, for the local
orientation sets: for `T : Φ ≃ Ψ` (Definition 10.4.8) covering `τ`, the identification of `Ψ`
after `τ(a)_*` is that of `Φ`. -/
theorem orEqvLoc_nat {a : Obj} (hs : a ∈ X.PObj.smoothSet)
    (o : OrxLoc hfT' (ϕ.obj a) (hΦ.smooth_obj hs)) :
    hΨ.orEqvLoc hpbΨ hfT hfT' a hs (E'.orMorLoc hF' hfT' (θ.τ.app a) (θ.τ.src_app a)
      (θ.τ.tgt_app a) (hΦ.smooth_obj hs) (hΨ.smooth_obj hs) o) =
        hΦ.orEqvLoc hpbΦ hfT hfT' a hs o :=
  DFunLike.congr_fun (orLoc_triangle (L := E'.morIso (θ.τ.app a)) (L₂ := hΨ.locIso a)
    (N := hΦ.locIso a) hfT hfT' hfT' (E'.eqOn_morIso_of_functor hF' (θ.τ.app a))
    (hΨ.eqOn_loc hpbΨ hfT'.isScSmooth.1 a) (hΦ.eqOn_loc hpbΦ hfT'.isScSmooth.1 a)
    (hΨ.mem_locSet a) (hΦ.mem_locSet a) rfl (mem_tgtSet (θ.τ.tgt_app a))
    (E'.morIso_ϕ_eq (θ.τ.src_app a) (θ.τ.tgt_app a)) rfl hs (hΨ.smooth_obj hs)
    (hΦ.smooth_obj hs) (germ_nat hΦ hΨ θ a)) o

include θ in
/-- **`Φ_*` and `Ψ_*` agree on `|O_f|`** for naturally equivalent `Φ ≃ Ψ`: `(a, o)` goes to
`(ϕ(a), …)` and `(ψ(a), …)`, related by `τ(a)`. -/
theorem orRelLoc_orSpaceMapLoc_nat (p : OrSpaceLoc hX hfT) :
    E'.OrRelLoc hX' hF' hfT' (hΦ.orSpaceMapLoc hpbΦ hX hX' hfT hfT' p)
      (hΨ.orSpaceMapLoc hpbΨ hX hX' hfT hfT' p) := by
  refine ⟨θ.τ.app (X.PObj.smoothVal p.1), θ.τ.src_app _, θ.τ.tgt_app _, ?_⟩
  change E'.orMorLoc hF' hfT' (θ.τ.app _) (θ.τ.src_app _) (θ.τ.tgt_app _)
      (hΦ.smooth_obj (X.PObj.smoothVal_mem p.1)) (hΨ.smooth_obj (X.PObj.smoothVal_mem p.1))
      ((hΦ.orEqvLoc hpbΦ hfT hfT' _ (X.PObj.smoothVal_mem p.1)).symm p.2) =
    (hΨ.orEqvLoc hpbΨ hfT hfT' _ (X.PObj.smoothVal_mem p.1)).symm p.2
  rw [Equiv.eq_symm_apply, orEqvLoc_nat hΦ hΨ θ hF' hpbΦ hpbΨ hfT hfT',
    Equiv.apply_symm_apply]

include θ in
/-- **Invariance of `|f̄|_*` under natural equivalence**: `|Φ|_* = |Ψ|_*` on `|O_f|`. -/
theorem orbitOrMapLoc_nat (c : Quot (E.OrRelLoc hX hF hfT)) :
    hΦ.orbitOrMapLoc hF hF' hpbΦ hX hX' hfT hfT' c =
      hΨ.orbitOrMapLoc hF hF' hpbΨ hX hX' hfT hfT' c := by
  induction c using Quot.ind with
  | mk p => exact Quot.sound (orRelLoc_orSpaceMapLoc_nat hΦ hΨ θ hF' hpbΦ hpbΨ hX hX' hfT
      hfT' p)


end Or

end EpStrongBundle.IsStrongBundleEquivalence

end Nat

end Polyfold
