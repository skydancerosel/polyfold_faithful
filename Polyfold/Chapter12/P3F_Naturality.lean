import Polyfold.Chapter12.P3F_EquivalenceOr

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, **Theorem 12.5.7** (2017: Theorem 12.12): naturality of the orientation bundle
`O_f` under generalized strong bundle isomorphisms.

## The text, paraphrased

For strong bundles over tame ep-groupoids, a generalized strong bundle isomorphism `f̄ : W → W'`
over `f : X → X'`, an sc-Fredholm section functor `f` and its push-forward `f'`: (1) `f̄` induces
a fibre-preserving homeomorphism `|f̄|_* : |O_f| → |O_{f'}|` over `|f| : |X_∞| → |X'_∞|`, and the
construction is functorial; (2) a continuous section functor `o` of `σ` (an orientation) has a
push-forward `o' = f̄_* o`, a continuous section functor of `O_{f'} → X'_∞`.  The proof works with
a representative `W ← V → W'` of strong bundle equivalences; the pull-back of `f` to `V` is `f''`
and `f'` is the push-forward of `f''`.

## What is formalized

For one strong bundle equivalence `h : Φ : W → W'` over `ϕ : X → X'` and `f = Φ^* f'`
(`P3F_EquivalenceOr`: `orEqv`, naturality `orMor_orEqv`):

* `smoothOrbitMap h : |X_∞| → |X'_∞|`, a bijection (`smoothOrbitMap_bijective`).
* `orbitOrMap h : |O_f| → |O_{f'}|`, `|(a, o)| ↦ |(ϕ(a), orEqv⁻¹ o)|`: well defined by
  naturality, a bijection over `smoothOrbitMap` (`orbitOrMap_bijective`,
  `orbitProj_orbitOrMap`).
* `pullOr h o'`, `pushOr h o`: an invariant section of `σ'` (the second clause of Definition
  12.5.4, `IsOrInvariant`) gives one of `σ` and conversely (`isOrInvariant_pullOr`,
  `isOrInvariant_pushOr`); `pushOr` is characterized by `pushOr_obj` and `pushOr_unique`.

For a representative `W ← V → W'` (two strong bundle equivalences `h₁ : V → W`, `h₂ : V → W'`),
`f'' = Φ₁^* f` and `f''= Φ₂^* f'` (true for `f' = Φ₂_* f''`, `pullback_pushforward`):

* `theorem_12_5_7_one_hyp`: **(1) without continuity**: a bijection `|O_f| ≃ |O_{f'}|` over the
  bijection `|X_∞| ≃ |X'_∞|` of the diagram (`|ϕ₂| ∘ |ϕ₁|⁻¹`).
* `theorem_12_5_7_two_invariant`: **(2) without continuity**: an invariant section `o` of `σ`
  has a unique invariant push-forward `o'` with `o'` and `o` corresponding at every `a ∈ V`.

Not formalized: the continuity statements (`|f̄|_*` a homeomorphism, `o'` continuous), which need
the continuity of Part I's orientation transport under local strong bundle isomorphisms (the
same missing step as the last sentence of Theorem 12.5.3); the independence of the
representative and the functoriality of `|f̄|_*` (left to the reader in the text).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

open StrongRetr

universe u

section Single

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

/-- **The invariance clause of Definition 12.5.4**, p. 594: `φ_* o_{s(φ)} = o_{t(φ)}` for every
morphism between smooth objects. -/
def IsOrInvariant (E : EpStrongBundle X B) {f : Obj → W} (hF : E.IsScFredholmSectionFunctor f)
    (hsec : B.HasScPlusSectionsThrough) (o : ∀ x (hs : x ∈ X.PObj.smoothSet), Orx f hF.2 x hs) :
    Prop :=
  ∀ (φ : Mor) {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x') (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet), E.orMor hF hsec φ hx hx' hs hs' (o x hs) = o x' hs'

/-- Definition 12.5.4 is continuity plus `IsOrInvariant`. -/
theorem definition_12_5_4_iff (E : EpStrongBundle X B) {f : Obj → W}
    (hF : E.IsScFredholmSectionFunctor f) (hsec : B.HasScPlusSectionsThrough)
    (t : TopologicalSpace (OrSpace f hF.2)) (o : ∀ x (hs : x ∈ X.PObj.smoothSet), Orx f hF.2 x hs) :
    E.definition_12_5_4 hF hsec t o ↔ @Continuous _ _ _ t (orSec o) ∧ E.IsOrInvariant hF hsec o :=
  Iff.rfl

namespace IsStrongBundleEquivalence

variable {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (h : E.IsStrongBundleEquivalence E' ϕ Φ)

/-! ### `|X_∞| → |X'_∞|` -/

/-- `ϕ` on smooth objects. -/
def smoothMap (x : X.PObj.SmoothLevel) : X'.PObj.SmoothLevel :=
  X'.PObj.smoothMk (ϕ.obj (X.PObj.smoothVal x)) (h.smooth_obj (X.PObj.smoothVal_mem x))

/-- **`|ϕ| : |X_∞| → |X'_∞|`**. -/
def smoothOrbitMap : Quot X.SmoothRel → Quot X'.SmoothRel :=
  Quot.map h.smoothMap fun _ _ ⟨φ, h1, h2⟩ => ⟨ϕ.mor φ, src_mor_eq h1, tgt_mor_eq h2⟩

include h in
/-- Every smooth `x' ∈ X'` is isomorphic to `ϕ(a)` for a smooth `a`. -/
theorem exists_smooth_iso {x' : Obj'} (hs : x' ∈ X'.PObj.smoothSet) :
    ∃ (a : Obj) (_ : a ∈ X.PObj.smoothSet) (ψ : Mor'), X'.src ψ = ϕ.obj a ∧ X'.tgt ψ = x' := by
  obtain ⟨a, ψ, h1, h2⟩ := h.isEquivalence_base.exists_iso x'
  have hψs : ψ ∈ X'.PMor.smoothSet := (X'.mem_smoothSet_tgt_iff ψ).1 (h2 ▸ hs)
  have hϕa : ϕ.obj a ∈ X'.PObj.smoothSet := h1 ▸ (X'.mem_smoothSet_src_iff ψ).2 hψs
  exact ⟨a, h.smooth_of_obj hϕa, ψ, h1, h2⟩

/-- `|ϕ| : |X_∞| → |X'_∞|` is a bijection (`ϕ` is full and essentially surjective). -/
theorem smoothOrbitMap_bijective : Function.Bijective h.smoothOrbitMap := by
  refine ⟨fun c d hcd => ?_, fun d => ?_⟩
  · induction c using Quot.ind with
    | mk x =>
      induction d using Quot.ind with
      | mk y =>
        obtain ⟨ψ, h1, h2⟩ := EpGroupoid.smoothRel_of_quot_eq hcd
        obtain ⟨α, ha, hb, -⟩ := h.exists_mor_eq h1 h2
        exact Quot.sound ⟨α, ha, hb⟩
  · induction d using Quot.ind with
    | mk y =>
      obtain ⟨a, ha, ψ, h1, h2⟩ := h.exists_smooth_iso (X'.PObj.smoothVal_mem y)
      exact ⟨Quot.mk _ (X.PObj.smoothMk a ha), Quot.sound ⟨ψ, h1, h2⟩⟩

/-! ### `|O_f| → |O_{f'}|` -/

include h in
/-- **Witness for the hypothesis `f = Φ^* f'`**: for every sc-Fredholm section functor `f` of
`W`, the push-forward `f' = Φ_* f` is one of `W'` (Theorem 10.4.5) with `Φ^* f' = f`. -/
theorem pullback_pushforward_witness {f : Obj → W} (hF : E.IsScFredholmSectionFunctor f) :
    E'.IsScFredholmSectionFunctor (h.pushforward f) ∧ f = h.pullback (h.pushforward f) :=
  ⟨(theorem_10_4_5_fred h).1 hF, (h.pullback_pushforward hF.1.choose.1 hF.1.choose_spec).symm⟩

section Orbit

variable {f : Obj → W} {f' : Obj' → W'} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hpb : f = h.pullback f')
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)

/-- `(a, o) ↦ (ϕ(a), orEqv⁻¹ o)`, `O_f → O_{f'}`. -/
def orSpaceMap (p : OrSpace f hF.2) : OrSpace f' hF'.2 :=
  ⟨h.smoothMap p.1, (h.orEqv hF hF' hpb hsec hsec' _ (X.PObj.smoothVal_mem p.1)).symm p.2⟩

theorem orRel_orSpaceMap {p q : OrSpace f hF.2} (hpq : E.OrRel hF hsec p q) :
    E'.OrRel hF' hsec' (h.orSpaceMap hF hF' hpb hsec hsec' p)
      (h.orSpaceMap hF hF' hpb hsec hsec' q) := by
  obtain ⟨α, hx, hx', hα⟩ := hpq
  refine ⟨ϕ.mor α, src_mor_eq hx, tgt_mor_eq hx', ?_⟩
  change E'.orMor hF' hsec' (ϕ.mor α) (src_mor_eq hx) (tgt_mor_eq hx')
      (h.smooth_obj (X.PObj.smoothVal_mem p.1)) (h.smooth_obj (X.PObj.smoothVal_mem q.1))
      ((h.orEqv hF hF' hpb hsec hsec' _ (X.PObj.smoothVal_mem p.1)).symm p.2) =
    (h.orEqv hF hF' hpb hsec hsec' _ (X.PObj.smoothVal_mem q.1)).symm q.2
  rw [Equiv.eq_symm_apply, ← h.orMor_orEqv hF hF' hpb hsec hsec' hx hx', Equiv.apply_symm_apply]
  exact hα

/-- **`|O_f| → |O_{f'}|`**, `|(a, o)| ↦ |(ϕ(a), orEqv⁻¹ o)|` (proof of Theorem 12.5.7). -/
def orbitOrMap : Quot (E.OrRel hF hsec) → Quot (E'.OrRel hF' hsec') :=
  Quot.map (h.orSpaceMap hF hF' hpb hsec hsec') fun _ _ => h.orRel_orSpaceMap hF hF' hpb hsec hsec'

/-- `|σ'| ∘ |Φ|_* = |ϕ| ∘ |σ|`. -/
theorem orbitProj_orbitOrMap (c : Quot (E.OrRel hF hsec)) :
    E'.orbitProj hF' hsec' (h.orbitOrMap hF hF' hpb hsec hsec' c) =
      h.smoothOrbitMap (E.orbitProj hF hsec c) := by
  induction c using Quot.ind with
  | mk p => rfl

/-- **`|O_f| → |O_{f'}|` is a bijection.** -/
theorem orbitOrMap_bijective : Function.Bijective (h.orbitOrMap hF hF' hpb hsec hsec') := by
  refine ⟨fun c d hcd => ?_, fun d => ?_⟩
  · induction c using Quot.ind with
    | mk p =>
      induction d using Quot.ind with
      | mk q =>
        obtain ⟨ψ, hx, hx', hψ⟩ := E'.orRel_of_quot_eq hF' hsec' hcd
        obtain ⟨α, ha, hb, hαψ⟩ := h.exists_mor_eq hx hx'
        refine Quot.sound ⟨α, ha, hb, ?_⟩
        have key := h.orMor_orEqv hF hF' hpb hsec hsec' ha hb (X.PObj.smoothVal_mem p.1)
          (X.PObj.smoothVal_mem q.1)
          ((h.orEqv hF hF' hpb hsec hsec' _ (X.PObj.smoothVal_mem p.1)).symm p.2)
        rw [Equiv.apply_symm_apply] at key
        have e : E'.orMor hF' hsec' (ϕ.mor α) (src_mor_eq ha) (tgt_mor_eq hb)
            (h.smooth_obj (X.PObj.smoothVal_mem p.1)) (h.smooth_obj (X.PObj.smoothVal_mem q.1))
            ((h.orEqv hF hF' hpb hsec hsec' _ (X.PObj.smoothVal_mem p.1)).symm p.2) =
            (h.orEqv hF hF' hpb hsec hsec' _ (X.PObj.smoothVal_mem q.1)).symm q.2 := by
          rw [E'.orMor_congr hF' hsec' hαψ]
          exact hψ
        rw [e, Equiv.apply_symm_apply] at key
        exact key
  · induction d using Quot.ind with
    | mk p' =>
      obtain ⟨a, ha, ψ, h1, h2⟩ := h.exists_smooth_iso (X'.PObj.smoothVal_mem p'.1)
      set ω := E'.orMor hF' hsec' (X'.inv ψ) ((X'.src_inv ψ).trans h2) ((X'.tgt_inv ψ).trans h1)
        (X'.PObj.smoothVal_mem p'.1) (h.smooth_obj ha) p'.2 with hω
      refine ⟨Quot.mk _ ⟨X.PObj.smoothMk a ha, h.orEqv hF hF' hpb hsec hsec' a ha ω⟩,
        Quot.sound ⟨ψ, h1, h2, ?_⟩⟩
      change E'.orMor hF' hsec' ψ h1 h2 (h.smooth_obj ha) (X'.PObj.smoothVal_mem p'.1)
        ((h.orEqv hF hF' hpb hsec hsec' a ha).symm (h.orEqv hF hF' hpb hsec hsec' a ha ω)) = p'.2
      rw [Equiv.symm_apply_apply, hω, E'.orMor_inv hF' hsec' h1 h2]
      exact Equiv.apply_symm_apply _ _

/-! ### Invariant sections: pull-back and push-forward -/

/-- **The pull-back of an invariant section of `σ'`**: `a ↦ orEqv (o'_{ϕ(a)})`. -/
def pullOr (o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), Orx f' hF'.2 x hs) :
    ∀ a (hs : a ∈ X.PObj.smoothSet), Orx f hF.2 a hs :=
  fun a hs => h.orEqv hF hF' hpb hsec hsec' a hs (o' (ϕ.obj a) (h.smooth_obj hs))

theorem isOrInvariant_pullOr {o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), Orx f' hF'.2 x hs}
    (ho' : E'.IsOrInvariant hF' hsec' o') :
    E.IsOrInvariant hF hsec (h.pullOr hF hF' hpb hsec hsec' o') := by
  intro α a b ha hb hs hsb
  change E.orMor hF hsec α ha hb hs hsb (h.orEqv hF hF' hpb hsec hsec' a hs
    (o' (ϕ.obj a) (h.smooth_obj hs))) = h.orEqv hF hF' hpb hsec hsec' b hsb
      (o' (ϕ.obj b) (h.smooth_obj hsb))
  rw [h.orMor_orEqv hF hF' hpb hsec hsec' ha hb hs hsb, ho']

/-- For an invariant `o`, every morphism `β : ϕ(a) → ϕ(b)` maps `orEqv⁻¹ o_a` to `orEqv⁻¹ o_b`
(`ϕ` is full; naturality). -/
theorem orMor_orEqv_symm {o : ∀ a (hs : a ∈ X.PObj.smoothSet), Orx f hF.2 a hs}
    (ho : E.IsOrInvariant hF hsec o) {β : Mor'} {a b : Obj} (ha : X'.src β = ϕ.obj a)
    (hb : X'.tgt β = ϕ.obj b) (hs : a ∈ X.PObj.smoothSet) (hsb : b ∈ X.PObj.smoothSet) :
    E'.orMor hF' hsec' β ha hb (h.smooth_obj hs) (h.smooth_obj hsb)
      ((h.orEqv hF hF' hpb hsec hsec' a hs).symm (o a hs)) =
      (h.orEqv hF hF' hpb hsec hsec' b hsb).symm (o b hsb) := by
  obtain ⟨α, hα, hα', hαβ⟩ := h.exists_mor_eq ha hb
  have key := h.orMor_orEqv hF hF' hpb hsec hsec' hα hα' hs hsb
    ((h.orEqv hF hF' hpb hsec hsec' a hs).symm (o a hs))
  rw [Equiv.apply_symm_apply, ho, E'.orMor_congr hF' hsec' hαβ] at key
  rw [Equiv.eq_symm_apply]
  exact key.symm

/-- **The push-forward of an invariant section of `σ`**: at a smooth `x'`, with the chosen
`ψ : ϕ(a) → x'`, `ψ_* (orEqv⁻¹ o_a)`. -/
def pushOr (o : ∀ a (hs : a ∈ X.PObj.smoothSet), Orx f hF.2 a hs) :
    ∀ x (hs : x ∈ X'.PObj.smoothSet), Orx f' hF'.2 x hs :=
  fun _ hs => E'.orMor hF' hsec' (h.exists_smooth_iso hs).choose_spec.choose_spec.choose
    (h.exists_smooth_iso hs).choose_spec.choose_spec.choose_spec.1
    (h.exists_smooth_iso hs).choose_spec.choose_spec.choose_spec.2
    (h.smooth_obj (h.exists_smooth_iso hs).choose_spec.choose) hs
    ((h.orEqv hF hF' hpb hsec hsec' _ (h.exists_smooth_iso hs).choose_spec.choose).symm
      (o _ (h.exists_smooth_iso hs).choose_spec.choose))

/-- **`pushOr` through any `ψ : ϕ(a) → x'`**: `(pushOr o)_{x'} = ψ_* (orEqv⁻¹ o_a)`. -/
theorem pushOr_eq {o : ∀ a (hs : a ∈ X.PObj.smoothSet), Orx f hF.2 a hs}
    (ho : E.IsOrInvariant hF hsec o) {x : Obj'} (hs : x ∈ X'.PObj.smoothSet) {a : Obj}
    (ha : a ∈ X.PObj.smoothSet) {ψ : Mor'} (h1 : X'.src ψ = ϕ.obj a) (h2 : X'.tgt ψ = x) :
    h.pushOr hF hF' hpb hsec hsec' o x hs =
      E'.orMor hF' hsec' ψ h1 h2 (h.smooth_obj ha) hs
        ((h.orEqv hF hF' hpb hsec hsec' a ha).symm (o a ha)) := by
  set a₀ := (h.exists_smooth_iso hs).choose
  have ha₀ := (h.exists_smooth_iso hs).choose_spec.choose
  set ψ₀ := (h.exists_smooth_iso hs).choose_spec.choose_spec.choose
  have h01 := (h.exists_smooth_iso hs).choose_spec.choose_spec.choose_spec.1
  have h02 := (h.exists_smooth_iso hs).choose_spec.choose_spec.choose_spec.2
  change E'.orMor hF' hsec' ψ₀ h01 h02 (h.smooth_obj ha₀) hs
    ((h.orEqv hF hF' hpb hsec hsec' a₀ ha₀).symm (o a₀ ha₀)) = _
  -- `β = ψ⁻¹ ∘ ψ₀ : ϕ(a₀) → ϕ(a)`
  have hi1 : X'.src (X'.inv ψ) = x := (X'.src_inv ψ).trans h2
  have hi2 : X'.tgt (X'.inv ψ) = ϕ.obj a := (X'.tgt_inv ψ).trans h1
  have hc := E'.orMor_comp hF' hsec' h01 h02 hi1 hi2 (h.smooth_obj ha₀) hs (h.smooth_obj ha)
  have hβ := h.orMor_orEqv_symm hF hF' hpb hsec hsec' ho (src_comp_eq h01 h02 hi1)
    (tgt_comp_eq h02 hi1 hi2) ha₀ ha
  rw [← hc, Equiv.trans_apply, E'.orMor_inv hF' hsec' h1 h2, Equiv.symm_apply_eq] at hβ
  exact hβ

/-- `pushOr o` at `ϕ(a)` is `orEqv⁻¹ o_a`: `o` and `pushOr o` correspond under `orEqv`. -/
theorem pushOr_obj {o : ∀ a (hs : a ∈ X.PObj.smoothSet), Orx f hF.2 a hs}
    (ho : E.IsOrInvariant hF hsec o) {a : Obj} (ha : a ∈ X.PObj.smoothSet) :
    h.orEqv hF hF' hpb hsec hsec' a ha
      (h.pushOr hF hF' hpb hsec hsec' o (ϕ.obj a) (h.smooth_obj ha)) = o a ha := by
  rw [h.pushOr_eq hF hF' hpb hsec hsec' ho (h.smooth_obj ha) ha (X'.src_unit _)
    (X'.tgt_unit _), E'.orMor_unit hF' hsec' rfl]
  exact Equiv.apply_symm_apply _ _

/-- **`pushOr o` is invariant.** -/
theorem isOrInvariant_pushOr {o : ∀ a (hs : a ∈ X.PObj.smoothSet), Orx f hF.2 a hs}
    (ho : E.IsOrInvariant hF hsec o) :
    E'.IsOrInvariant hF' hsec' (h.pushOr hF hF' hpb hsec hsec' o) := by
  intro χ x x' hx hx' hs hs'
  obtain ⟨a, ha, ψ, h1, h2⟩ := h.exists_smooth_iso hs
  rw [h.pushOr_eq hF hF' hpb hsec hsec' ho hs ha h1 h2,
    h.pushOr_eq hF hF' hpb hsec hsec' ho hs' ha (src_comp_eq h1 h2 hx) (tgt_comp_eq h2 hx hx'),
    ← E'.orMor_comp hF' hsec' h1 h2 hx hx' (h.smooth_obj ha) hs hs']
  rfl

/-- **Uniqueness of the push-forward**: an invariant section of `σ'` corresponding to `o` at
every `ϕ(a)` is `pushOr o`. -/
theorem pushOr_unique {o : ∀ a (hs : a ∈ X.PObj.smoothSet), Orx f hF.2 a hs}
    (ho : E.IsOrInvariant hF hsec o) {o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), Orx f' hF'.2 x hs}
    (ho' : E'.IsOrInvariant hF' hsec' o')
    (hoo : ∀ a (ha : a ∈ X.PObj.smoothSet),
      h.orEqv hF hF' hpb hsec hsec' a ha (o' (ϕ.obj a) (h.smooth_obj ha)) = o a ha) :
    o' = h.pushOr hF hF' hpb hsec hsec' o := by
  funext x hs
  obtain ⟨a, ha, ψ, h1, h2⟩ := h.exists_smooth_iso hs
  rw [h.pushOr_eq hF hF' hpb hsec hsec' ho hs ha h1 h2, ← hoo a ha, Equiv.symm_apply_apply,
    ho' ψ h1 h2]

/-- `pullOr` undoes `pushOr`. -/
theorem pullOr_pushOr {o : ∀ a (hs : a ∈ X.PObj.smoothSet), Orx f hF.2 a hs}
    (ho : E.IsOrInvariant hF hsec o) :
    h.pullOr hF hF' hpb hsec hsec' (h.pushOr hF hF' hpb hsec hsec' o) = o := by
  funext a ha
  exact h.pushOr_obj hF hF' hpb hsec hsec' ho ha

end Orbit

end IsStrongBundleEquivalence

end EpStrongBundle

end Single

section Diagram

/-! ### Theorem 12.5.7 for a representative `W ← V → W'` -/

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
  {ϕ₁ : EpFunctor X'' X} {Φ₁ : EpFunctor E''.toEpGroupoid E.toEpGroupoid}
  {ϕ₂ : EpFunctor X'' X'} {Φ₂ : EpFunctor E''.toEpGroupoid E'.toEpGroupoid}
  (h₁ : E''.IsStrongBundleEquivalence E ϕ₁ Φ₁) (h₂ : E''.IsStrongBundleEquivalence E' ϕ₂ Φ₂)
  {f : Obj → W} {f' : Obj' → W'} {f'' : Obj'' → W''} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hF'' : E''.IsScFredholmSectionFunctor f'')
  (hpb₁ : f'' = h₁.pullback f) (hpb₂ : f'' = h₂.pullback f')
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)
  (hsec'' : B''.HasScPlusSectionsThrough)

/-- **Theorem 12.5.7 (1)**, p. 595 (2017: Theorem 12.12 (1)), without the topology: for a
representative `W ←Φ₁– V –Φ₂→ W'` of a generalized strong bundle isomorphism, an sc-Fredholm
section functor `f` of `W` and `f'` of `W'` with the same pull-back `f''` to `V`, there are
bijections `|O_f| ≃ |O_{f'}|` and `|X_∞| ≃ |X'_∞|` commuting with `|σ|`, `|σ'|`; they are the
ones of the diagram: `F ∘ |Φ₁|_* = |Φ₂|_*` and `G ∘ |ϕ₁| = |ϕ₂|`.  Hypotheses as in Part I's
orientation transport: `sc⁺`-sections through every point of `W`, `W'`, `V` (`_hyp`). -/
theorem theorem_12_5_7_one_hyp :
    ∃ (F : Quot (E.OrRel hF hsec) ≃ Quot (E'.OrRel hF' hsec'))
      (G : Quot X.SmoothRel ≃ Quot X'.SmoothRel),
      (∀ c, E'.orbitProj hF' hsec' (F c) = G (E.orbitProj hF hsec c)) ∧
      (∀ c, F (h₁.orbitOrMap hF'' hF hpb₁ hsec'' hsec c) =
        h₂.orbitOrMap hF'' hF' hpb₂ hsec'' hsec' c) ∧
      ∀ v, G (h₁.smoothOrbitMap v) = h₂.smoothOrbitMap v := by
  set F₁ := Equiv.ofBijective _ (h₁.orbitOrMap_bijective hF'' hF hpb₁ hsec'' hsec)
  set F₂ := Equiv.ofBijective _ (h₂.orbitOrMap_bijective hF'' hF' hpb₂ hsec'' hsec')
  set G₁ := Equiv.ofBijective _ h₁.smoothOrbitMap_bijective
  set G₂ := Equiv.ofBijective _ h₂.smoothOrbitMap_bijective
  refine ⟨F₁.symm.trans F₂, G₁.symm.trans G₂, fun c => ?_, fun c => ?_, fun v => ?_⟩
  · obtain ⟨d, rfl⟩ := F₁.surjective c
    rw [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.trans_apply]
    change E'.orbitProj hF' hsec' (h₂.orbitOrMap hF'' hF' hpb₂ hsec'' hsec' d) =
      G₂ (G₁.symm (E.orbitProj hF hsec (h₁.orbitOrMap hF'' hF hpb₁ hsec'' hsec d)))
    rw [h₂.orbitProj_orbitOrMap, h₁.orbitProj_orbitOrMap]
    change _ = G₂ (G₁.symm (G₁ _))
    rw [Equiv.symm_apply_apply]
    rfl
  · change F₂ (F₁.symm (F₁ c)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  · change G₂ (G₁.symm (G₁ v)) = _
    rw [Equiv.symm_apply_apply]
    rfl

/-- **Theorem 12.5.7 (2)**, p. 595 (2017: Theorem 12.12 (2)), without the topology: an
orientation section `o` of `σ` with the invariance of Definition 12.5.4 has exactly one
invariant section `o'` of `σ'` that corresponds to `o` over the representative, i.e.
`orEqv₂ o'_{ϕ₂ v} = orEqv₁ o_{ϕ₁ v}` for every smooth `v ∈ V`. -/
theorem theorem_12_5_7_two_invariant {o : ∀ a (hs : a ∈ X.PObj.smoothSet), Orx f hF.2 a hs}
    (ho : E.IsOrInvariant hF hsec o) :
    ∃! o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), Orx f' hF'.2 x hs,
      E'.IsOrInvariant hF' hsec' o' ∧ ∀ v (hv : v ∈ X''.PObj.smoothSet),
        h₂.orEqv hF'' hF' hpb₂ hsec'' hsec' v hv (o' (ϕ₂.obj v) (h₂.smooth_obj hv)) =
          h₁.orEqv hF'' hF hpb₁ hsec'' hsec v hv (o (ϕ₁.obj v) (h₁.smooth_obj hv)) := by
  have ho'' := h₁.isOrInvariant_pullOr hF'' hF hpb₁ hsec'' hsec ho
  refine ⟨h₂.pushOr hF'' hF' hpb₂ hsec'' hsec' (h₁.pullOr hF'' hF hpb₁ hsec'' hsec o),
    ⟨h₂.isOrInvariant_pushOr hF'' hF' hpb₂ hsec'' hsec' ho'', fun v hv =>
      h₂.pushOr_obj hF'' hF' hpb₂ hsec'' hsec' ho'' hv⟩, fun o' ⟨ho', hoo⟩ => ?_⟩
  exact h₂.pushOr_unique hF'' hF' hpb₂ hsec'' hsec' ho'' ho' hoo

end Diagram


end Polyfold
