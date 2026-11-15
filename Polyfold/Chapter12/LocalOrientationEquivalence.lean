import Polyfold.Chapter12.LocalOrientationIsoTransport
import Polyfold.Chapter12.LocalOrientationOrbit
import Polyfold.Chapter12.OrientationEquivalenceNatural

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597, **Theorem 12.5.7** for a representative `W ← V → W'`, without the topology, for
the linearizations made with local sc⁺-sections.

# Strong bundle equivalences and the local orientation sets

## The text, paraphrased

(Theorem 12.5.7) A generalized strong bundle isomorphism `𝔣 : W → W'` between strong bundles
over tame ep-groupoids and sc-Fredholm section functors `f`, `f'` with `𝔣_* f = f'` induce (1) a
homeomorphism `|O_f| → |O_{f'}|` covering `|X_∞| → |X'_∞|`, and (2) for an orientation `o` of
`f` a unique push-forward orientation `o'` of `f'`.  In the proof `𝔣` is represented by a
diagram `W ←Φ– V –Φ'→ W'` of strong bundle equivalences; the pull-back of `f` to `V` and the
push-forward to `W'` give bijections of the fibres of the orientation bundles, natural with
respect to the morphisms.

## What is formalized

The orientation sets are the local ones (`OrxLoc`); the hypotheses are tame object M-polyfolds
and tame germ data only.  For a strong bundle equivalence `Φ : W → W'` over `ϕ` with
`f = Φ^* f'`:

* `EpStrongBundle.orMorLoc_eq_orLoc`: `φ_*` is the map of orientations of the local strong
  bundle isomorphism of `φ`.
* `orEqvLoc a : Or_{ϕ(a)}^{f'} ≃ Or_a^f`, the map of orientations of `Φ` near `a`;
  `orEqvLoc_eq_orLoc` (any point of `U(a)`), `orMorLoc_orEqvLoc` (**naturality** under
  morphisms), `orEqvLoc_comp` (composites of equivalences), `orEqvLoc_nat` (naturally
  equivalent equivalences).
* `IsOrInvariantLoc`, `orSpaceMapLoc`, `orbitOrMapLoc` (`|O_f| → |O_{f'}|`),
  `orbitProjLoc_orbitOrMapLoc`, `orbitOrMapLoc_bijective`, `pullOrLoc`, `pushOrLoc` with
  `pushOrLoc_eq`, `pushOrLoc_obj`, `isOrInvariantLoc_pushOrLoc`, `pushOrLoc_unique`,
  `pullOrLoc_pushOrLoc`.
* `theorem_12_5_7_one_loc_bijection`: **Theorem 12.5.7 (1)** without the topology: bijections
  `|O_f| ≃ |O_{f'}|` and `|X_∞| ≃ |X'_∞|` commuting with `|σ|`, `|σ'|` and the maps of the
  diagram.
* `theorem_12_5_7_two_invariant_loc`: **Theorem 12.5.7 (2)** without the continuity: an
  invariant family of orientations of `f` has exactly one invariant family of orientations of
  `f'` corresponding to it over `V`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

open StrongRetr StrongBundle.LocalIso

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

/-- **`φ_*` on the local orientation sets is the map of orientations of the local strong bundle
isomorphism of `φ`.** -/
theorem orMorLoc_eq_orLoc (E : EpStrongBundle X B) {f : Obj → W}
    (hF : E.IsScFredholmSectionFunctor f) (hfT : B.IsScFredholmSectionTame f) (σ : Mor)
    {x x' : Obj} (hx : X.src σ = x) (hx' : X.tgt σ = x') (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet) :
    E.orMorLoc hF hfT σ hx hx' hs hs' =
      (E.morIso σ).orLoc hfT hfT (E.eqOn_morIso_of_functor hF σ) (mem_tgtSet hx')
        (E.morIso_ϕ_eq hx hx') hs' hs :=
  rfl

/-- **The invariance clause of Definition 12.5.4**, p. 594, for the local orientation sets:
`φ_* o_{s(φ)} = o_{t(φ)}` for every morphism between smooth objects. -/
def IsOrInvariantLoc (E : EpStrongBundle X B) {f : Obj → W}
    (hF : E.IsScFredholmSectionFunctor f) (hfT : B.IsScFredholmSectionTame f)
    (o : ∀ x (hs : x ∈ X.PObj.smoothSet), OrxLoc hfT x hs) : Prop :=
  ∀ (φ : Mor) {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x') (hs : x ∈ X.PObj.smoothSet)
    (hs' : x' ∈ X.PObj.smoothSet), E.orMorLoc hF hfT φ hx hx' hs hs' (o x hs) = o x' hs'

/-- Definition 12.5.4 is continuity plus `IsOrInvariantLoc`. -/
theorem definition_12_5_4_loc_iff_isOrInvariantLoc (E : EpStrongBundle X B) {f : Obj → W}
    (hX : X.PObj.IsTame) (hF : E.IsScFredholmSectionFunctor f)
    (hfT : B.IsScFredholmSectionTame f)
    (o : ∀ x (hs : x ∈ X.PObj.smoothSet), OrxLoc hfT x hs) :
    E.definition_12_5_4_loc hX hF hfT o ↔
      @Continuous _ _ _ (orTopologyLoc hX hfT) ((orLocalTransportLoc hX hfT).sec o) ∧
        E.IsOrInvariantLoc hF hfT o :=
  Iff.rfl

namespace IsStrongBundleEquivalence

variable {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
  (h : E.IsStrongBundleEquivalence E' ϕ Φ)

section Or

variable {f : Obj → W} {f' : Obj' → W'} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hpb : f = h.pullback f')
  (hfT : B.IsScFredholmSectionTame f) (hfT' : B'.IsScFredholmSectionTame f')

/-- **`Or_{ϕ(a)}^{f'} ≃ Or_a^f`** on the local orientation sets: an orientation of
`DET(f', ϕ(a))` carried to one of `DET(f, a)` along `Φ⁻¹`, the map of orientations of the local
strong bundle isomorphism `W|U(a) → W'|U'(a)` of Definition 10.4.1 (2). -/
def orEqvLoc (a : Obj) (hs : a ∈ X.PObj.smoothSet) :
    OrxLoc hfT' (ϕ.obj a) (h.smooth_obj hs) ≃ OrxLoc hfT a hs :=
  (h.locIso a).orLoc hfT hfT' (h.eqOn_loc hpb hfT'.isScSmooth.1 a) (h.mem_locSet a) rfl hs
    (h.smooth_obj hs)

/-- **The map of orientations of `Φ` near `a` at any point `b ∈ U(a)`** is `orEqvLoc b`: the
local isomorphisms of Definition 10.4.1 (2) at `a` and at `b` are both restrictions of `Φ`. -/
theorem orEqvLoc_eq_orLoc (a : Obj) {b : Obj} (hb : b ∈ h.locSet a)
    (hs : b ∈ X.PObj.smoothSet) :
    h.orEqvLoc hpb hfT hfT' b hs =
      (h.locIso a).orLoc hfT hfT' (h.eqOn_loc hpb hfT'.isScSmooth.1 a) hb rfl hs
        (h.smooth_obj hs) :=
  orLoc_germ hfT hfT' _ _ (h.mem_locSet b) hb rfl rfl hs (h.smooth_obj hs)
    ⟨⟨h.locSet b ∩ h.locSet a, (h.isOpen_locSet b).inter (h.isOpen_locSet a),
      ⟨h.mem_locSet b, hb⟩, inter_subset_left, inter_subset_right, fun _ _ => rfl,
      fun _ _ => rfl⟩⟩

/-- **Naturality of `orEqvLoc`** (the "canonical lifts" in the proof of Theorem 12.5.7,
p. 597): for a morphism `α : a → b` between smooth objects,
`α_* ∘ orEqvLoc a = orEqvLoc b ∘ ϕ(α)_*`. -/
theorem orMorLoc_orEqvLoc {α : Mor} {a b : Obj} (ha : X.src α = a) (hb : X.tgt α = b)
    (hs : a ∈ X.PObj.smoothSet) (hsb : b ∈ X.PObj.smoothSet)
    (o : OrxLoc hfT' (ϕ.obj a) (h.smooth_obj hs)) :
    E.orMorLoc hF hfT α ha hb hs hsb (h.orEqvLoc hpb hfT hfT' a hs o) =
      h.orEqvLoc hpb hfT hfT' b hsb (E'.orMorLoc hF' hfT' (ϕ.mor α) (src_mor_eq ha)
        (tgt_mor_eq hb) (h.smooth_obj hs) (h.smooth_obj hsb) o) :=
  DFunLike.congr_fun (orLoc_square (L := h.locIso a) (L₂ := E.morIso α)
    (M := E'.morIso (ϕ.mor α)) (M₂ := h.locIso b) hfT hfT hfT' hfT'
    (h.eqOn_loc hpb hfT'.isScSmooth.1 a) (E.eqOn_morIso_of_functor hF α)
    (E'.eqOn_morIso_of_functor hF' (ϕ.mor α)) (h.eqOn_loc hpb hfT'.isScSmooth.1 b)
    (mem_tgtSet hb) (h.mem_locSet b) (E.morIso_ϕ_eq ha hb) rfl (h.mem_locSet a)
    (mem_tgtSet (tgt_mor_eq hb)) rfl (E'.morIso_ϕ_eq (src_mor_eq ha) (tgt_mor_eq hb)) hsb hs
    (h.smooth_obj hsb) (h.smooth_obj hs) (h.germAgree₄_mor (a := a) hb)) o

end Or

section Orbit

variable {f : Obj → W} {f' : Obj' → W'} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hpb : f = h.pullback f')
  (hX : X.PObj.IsTame) (hX' : X'.PObj.IsTame) (hfT : B.IsScFredholmSectionTame f)
  (hfT' : B'.IsScFredholmSectionTame f')

/-- `(a, o) ↦ (ϕ(a), orEqv⁻¹ o)`, `O_f → O_{f'}`. -/
def orSpaceMapLoc (p : OrSpaceLoc hX hfT) : OrSpaceLoc hX' hfT' :=
  ⟨h.smoothMap p.1, (h.orEqvLoc hpb hfT hfT' _ (X.PObj.smoothVal_mem p.1)).symm p.2⟩

theorem orRelLoc_orSpaceMapLoc {p q : OrSpaceLoc hX hfT} (hpq : E.OrRelLoc hX hF hfT p q) :
    E'.OrRelLoc hX' hF' hfT' (h.orSpaceMapLoc hpb hX hX' hfT hfT' p)
      (h.orSpaceMapLoc hpb hX hX' hfT hfT' q) := by
  obtain ⟨α, hx, hx', hα⟩ := hpq
  refine ⟨ϕ.mor α, src_mor_eq hx, tgt_mor_eq hx', ?_⟩
  change E'.orMorLoc hF' hfT' (ϕ.mor α) (src_mor_eq hx) (tgt_mor_eq hx')
      (h.smooth_obj (X.PObj.smoothVal_mem p.1)) (h.smooth_obj (X.PObj.smoothVal_mem q.1))
      ((h.orEqvLoc hpb hfT hfT' _ (X.PObj.smoothVal_mem p.1)).symm p.2) =
    (h.orEqvLoc hpb hfT hfT' _ (X.PObj.smoothVal_mem q.1)).symm q.2
  rw [Equiv.eq_symm_apply, ← h.orMorLoc_orEqvLoc hF hF' hpb hfT hfT' hx hx', Equiv.apply_symm_apply]
  exact hα

/-- **`|O_f| → |O_{f'}|`**, `|(a, o)| ↦ |(ϕ(a), orEqv⁻¹ o)|` (proof of Theorem 12.5.7). -/
def orbitOrMapLoc : Quot (E.OrRelLoc hX hF hfT) → Quot (E'.OrRelLoc hX' hF' hfT') :=
  Quot.map (h.orSpaceMapLoc hpb hX hX' hfT hfT') fun _ _ =>
    h.orRelLoc_orSpaceMapLoc hF hF' hpb hX hX' hfT hfT'

/-- `|σ'| ∘ |Φ|_* = |ϕ| ∘ |σ|`. -/
theorem orbitProjLoc_orbitOrMapLoc (c : Quot (E.OrRelLoc hX hF hfT)) :
    E'.orbitProjLoc hX' hF' hfT' (h.orbitOrMapLoc hF hF' hpb hX hX' hfT hfT' c) =
      h.smoothOrbitMap (E.orbitProjLoc hX hF hfT c) := by
  induction c using Quot.ind with
  | mk p => rfl

/-- **`|O_f| → |O_{f'}|` is a bijection.** -/
theorem orbitOrMapLoc_bijective :
    Function.Bijective (h.orbitOrMapLoc hF hF' hpb hX hX' hfT hfT') := by
  refine ⟨fun c d hcd => ?_, fun d => ?_⟩
  · induction c using Quot.ind with
    | mk p =>
      induction d using Quot.ind with
      | mk q =>
        obtain ⟨ψ, hx, hx', hψ⟩ := E'.orRelLoc_of_quot_eq hX' hF' hfT' hcd
        obtain ⟨α, ha, hb, hαψ⟩ := h.exists_mor_eq hx hx'
        refine Quot.sound ⟨α, ha, hb, ?_⟩
        have key := h.orMorLoc_orEqvLoc hF hF' hpb hfT hfT' ha hb (X.PObj.smoothVal_mem p.1)
          (X.PObj.smoothVal_mem q.1)
          ((h.orEqvLoc hpb hfT hfT' _ (X.PObj.smoothVal_mem p.1)).symm p.2)
        rw [Equiv.apply_symm_apply] at key
        have e : E'.orMorLoc hF' hfT' (ϕ.mor α) (src_mor_eq ha) (tgt_mor_eq hb)
            (h.smooth_obj (X.PObj.smoothVal_mem p.1)) (h.smooth_obj (X.PObj.smoothVal_mem q.1))
            ((h.orEqvLoc hpb hfT hfT' _ (X.PObj.smoothVal_mem p.1)).symm p.2) =
            (h.orEqvLoc hpb hfT hfT' _ (X.PObj.smoothVal_mem q.1)).symm q.2 := by
          rw [E'.orMorLoc_congr hF' hfT' hαψ]
          exact hψ
        rw [e, Equiv.apply_symm_apply] at key
        exact key
  · induction d using Quot.ind with
    | mk p' =>
      obtain ⟨a, ha, ψ, h1, h2⟩ := h.exists_smooth_iso (X'.PObj.smoothVal_mem p'.1)
      set ω := E'.orMorLoc hF' hfT' (X'.inv ψ) ((X'.src_inv ψ).trans h2) ((X'.tgt_inv ψ).trans h1)
        (X'.PObj.smoothVal_mem p'.1) (h.smooth_obj ha) p'.2 with hω
      refine ⟨Quot.mk _ ⟨X.PObj.smoothMk a ha, h.orEqvLoc hpb hfT hfT' a ha ω⟩,
        Quot.sound ⟨ψ, h1, h2, ?_⟩⟩
      change E'.orMorLoc hF' hfT' ψ h1 h2 (h.smooth_obj ha) (X'.PObj.smoothVal_mem p'.1)
        ((h.orEqvLoc hpb hfT hfT' a ha).symm (h.orEqvLoc hpb hfT hfT' a ha ω)) = p'.2
      rw [Equiv.symm_apply_apply, hω, E'.orMorLoc_inv hF' hfT' h1 h2]
      exact Equiv.apply_symm_apply _ _

/-! ### Invariant sections: pull-back and push-forward -/

/-- **The pull-back of an invariant section of `σ'`**: `a ↦ orEqv (o'_{ϕ(a)})`. -/
def pullOrLoc (o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), OrxLoc hfT' x hs) :
    ∀ a (hs : a ∈ X.PObj.smoothSet), OrxLoc hfT a hs :=
  fun a hs => h.orEqvLoc hpb hfT hfT' a hs (o' (ϕ.obj a) (h.smooth_obj hs))

theorem isOrInvariantLoc_pullOrLoc {o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), OrxLoc hfT' x hs}
    (ho' : E'.IsOrInvariantLoc hF' hfT' o') :
    E.IsOrInvariantLoc hF hfT (h.pullOrLoc hpb hfT hfT' o') := by
  intro α a b ha hb hs hsb
  change E.orMorLoc hF hfT α ha hb hs hsb (h.orEqvLoc hpb hfT hfT' a hs
    (o' (ϕ.obj a) (h.smooth_obj hs))) = h.orEqvLoc hpb hfT hfT' b hsb
      (o' (ϕ.obj b) (h.smooth_obj hsb))
  rw [h.orMorLoc_orEqvLoc hF hF' hpb hfT hfT' ha hb hs hsb, ho']

/-- For an invariant `o`, every morphism `β : ϕ(a) → ϕ(b)` maps `orEqv⁻¹ o_a` to `orEqv⁻¹ o_b`
(`ϕ` is full; naturality). -/
theorem orMorLoc_orEqvLoc_symm {o : ∀ a (hs : a ∈ X.PObj.smoothSet), OrxLoc hfT a hs}
    (ho : E.IsOrInvariantLoc hF hfT o) {β : Mor'} {a b : Obj} (ha : X'.src β = ϕ.obj a)
    (hb : X'.tgt β = ϕ.obj b) (hs : a ∈ X.PObj.smoothSet) (hsb : b ∈ X.PObj.smoothSet) :
    E'.orMorLoc hF' hfT' β ha hb (h.smooth_obj hs) (h.smooth_obj hsb)
      ((h.orEqvLoc hpb hfT hfT' a hs).symm (o a hs)) =
      (h.orEqvLoc hpb hfT hfT' b hsb).symm (o b hsb) := by
  obtain ⟨α, hα, hα', hαβ⟩ := h.exists_mor_eq ha hb
  have key := h.orMorLoc_orEqvLoc hF hF' hpb hfT hfT' hα hα' hs hsb
    ((h.orEqvLoc hpb hfT hfT' a hs).symm (o a hs))
  rw [Equiv.apply_symm_apply, ho, E'.orMorLoc_congr hF' hfT' hαβ] at key
  rw [Equiv.eq_symm_apply]
  exact key.symm

/-- **The push-forward of an invariant section of `σ`**: at a smooth `x'`, with the chosen
`ψ : ϕ(a) → x'`, `ψ_* (orEqv⁻¹ o_a)`. -/
def pushOrLoc (o : ∀ a (hs : a ∈ X.PObj.smoothSet), OrxLoc hfT a hs) :
    ∀ x (hs : x ∈ X'.PObj.smoothSet), OrxLoc hfT' x hs :=
  fun _ hs => E'.orMorLoc hF' hfT' (h.exists_smooth_iso hs).choose_spec.choose_spec.choose
    (h.exists_smooth_iso hs).choose_spec.choose_spec.choose_spec.1
    (h.exists_smooth_iso hs).choose_spec.choose_spec.choose_spec.2
    (h.smooth_obj (h.exists_smooth_iso hs).choose_spec.choose) hs
    ((h.orEqvLoc hpb hfT hfT' _ (h.exists_smooth_iso hs).choose_spec.choose).symm
      (o _ (h.exists_smooth_iso hs).choose_spec.choose))

/-- **`pushOrLoc` through any `ψ : ϕ(a) → x'`**: `(pushOrLoc o)_{x'} = ψ_* (orEqv⁻¹ o_a)`. -/
theorem pushOrLoc_eq {o : ∀ a (hs : a ∈ X.PObj.smoothSet), OrxLoc hfT a hs}
    (ho : E.IsOrInvariantLoc hF hfT o) {x : Obj'} (hs : x ∈ X'.PObj.smoothSet) {a : Obj}
    (ha : a ∈ X.PObj.smoothSet) {ψ : Mor'} (h1 : X'.src ψ = ϕ.obj a) (h2 : X'.tgt ψ = x) :
    h.pushOrLoc hF' hpb hfT hfT' o x hs =
      E'.orMorLoc hF' hfT' ψ h1 h2 (h.smooth_obj ha) hs
        ((h.orEqvLoc hpb hfT hfT' a ha).symm (o a ha)) := by
  set a₀ := (h.exists_smooth_iso hs).choose
  have ha₀ := (h.exists_smooth_iso hs).choose_spec.choose
  set ψ₀ := (h.exists_smooth_iso hs).choose_spec.choose_spec.choose
  have h01 := (h.exists_smooth_iso hs).choose_spec.choose_spec.choose_spec.1
  have h02 := (h.exists_smooth_iso hs).choose_spec.choose_spec.choose_spec.2
  change E'.orMorLoc hF' hfT' ψ₀ h01 h02 (h.smooth_obj ha₀) hs
    ((h.orEqvLoc hpb hfT hfT' a₀ ha₀).symm (o a₀ ha₀)) = _
  -- `β = ψ⁻¹ ∘ ψ₀ : ϕ(a₀) → ϕ(a)`
  have hi1 : X'.src (X'.inv ψ) = x := (X'.src_inv ψ).trans h2
  have hi2 : X'.tgt (X'.inv ψ) = ϕ.obj a := (X'.tgt_inv ψ).trans h1
  have hc := E'.orMorLoc_comp hF' hfT' h01 h02 hi1 hi2 (h.smooth_obj ha₀) hs (h.smooth_obj ha)
  have hβ := h.orMorLoc_orEqvLoc_symm hF hF' hpb hfT hfT' ho (src_comp_eq h01 h02 hi1)
    (tgt_comp_eq h02 hi1 hi2) ha₀ ha
  rw [← hc, Equiv.trans_apply, E'.orMorLoc_inv hF' hfT' h1 h2, Equiv.symm_apply_eq] at hβ
  exact hβ

/-- `pushOrLoc o` at `ϕ(a)` is `orEqv⁻¹ o_a`: `o` and `pushOrLoc o` correspond under `orEqv`. -/
theorem pushOrLoc_obj {o : ∀ a (hs : a ∈ X.PObj.smoothSet), OrxLoc hfT a hs}
    (ho : E.IsOrInvariantLoc hF hfT o) {a : Obj} (ha : a ∈ X.PObj.smoothSet) :
    h.orEqvLoc hpb hfT hfT' a ha
      (h.pushOrLoc hF' hpb hfT hfT' o (ϕ.obj a) (h.smooth_obj ha)) = o a ha := by
  rw [h.pushOrLoc_eq hF hF' hpb hfT hfT' ho (h.smooth_obj ha) ha (X'.src_unit _)
    (X'.tgt_unit _), E'.orMorLoc_unit hF' hfT' rfl]
  exact Equiv.apply_symm_apply _ _

/-- **`pushOrLoc o` is invariant.** -/
theorem isOrInvariantLoc_pushOrLoc {o : ∀ a (hs : a ∈ X.PObj.smoothSet), OrxLoc hfT a hs}
    (ho : E.IsOrInvariantLoc hF hfT o) :
    E'.IsOrInvariantLoc hF' hfT' (h.pushOrLoc hF' hpb hfT hfT' o) := by
  intro χ x x' hx hx' hs hs'
  obtain ⟨a, ha, ψ, h1, h2⟩ := h.exists_smooth_iso hs
  rw [h.pushOrLoc_eq hF hF' hpb hfT hfT' ho hs ha h1 h2,
    h.pushOrLoc_eq hF hF' hpb hfT hfT' ho hs' ha (src_comp_eq h1 h2 hx) (tgt_comp_eq h2 hx hx'),
    ← E'.orMorLoc_comp hF' hfT' h1 h2 hx hx' (h.smooth_obj ha) hs hs']
  rfl

/-- **Uniqueness of the push-forward**: an invariant section of `σ'` corresponding to `o` at
every `ϕ(a)` is `pushOrLoc o`. -/
theorem pushOrLoc_unique {o : ∀ a (hs : a ∈ X.PObj.smoothSet), OrxLoc hfT a hs}
    (ho : E.IsOrInvariantLoc hF hfT o) {o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), OrxLoc hfT' x hs}
    (ho' : E'.IsOrInvariantLoc hF' hfT' o')
    (hoo : ∀ a (ha : a ∈ X.PObj.smoothSet),
      h.orEqvLoc hpb hfT hfT' a ha (o' (ϕ.obj a) (h.smooth_obj ha)) = o a ha) :
    o' = h.pushOrLoc hF' hpb hfT hfT' o := by
  funext x hs
  obtain ⟨a, ha, ψ, h1, h2⟩ := h.exists_smooth_iso hs
  rw [h.pushOrLoc_eq hF hF' hpb hfT hfT' ho hs ha h1 h2, ← hoo a ha, Equiv.symm_apply_apply,
    ho' ψ h1 h2]

/-- `pullOrLoc` undoes `pushOrLoc`. -/
theorem pullOrLoc_pushOrLoc {o : ∀ a (hs : a ∈ X.PObj.smoothSet), OrxLoc hfT a hs}
    (ho : E.IsOrInvariantLoc hF hfT o) :
    h.pullOrLoc hpb hfT hfT' (h.pushOrLoc hF' hpb hfT hfT' o) = o := by
  funext a ha
  exact h.pushOrLoc_obj hF hF' hpb hfT hfT' ho ha

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
  (hX : X.PObj.IsTame) (hX' : X'.PObj.IsTame) (hX'' : X''.PObj.IsTame)
  (hfT : B.IsScFredholmSectionTame f) (hfT' : B'.IsScFredholmSectionTame f')
  (hfT'' : B''.IsScFredholmSectionTame f'')

/-- **Theorem 12.5.7 (1)**, p. 595 (2017: Theorem 12.12 (1)), without the topology: for a
representative `W ←Φ₁– V –Φ₂→ W'` of a generalized strong bundle isomorphism, an sc-Fredholm
section functor `f` of `W` and `f'` of `W'` with the same pull-back `f''` to `V`, there are
bijections `|O_f| ≃ |O_{f'}|` and `|X_∞| ≃ |X'_∞|` commuting with `|σ|`, `|σ'|`; they are the
ones of the diagram: `F ∘ |Φ₁|_* = |Φ₂|_*` and `G ∘ |ϕ₁| = |ϕ₂|`.  The orientation sets are
the local ones; the hypotheses are tame object M-polyfolds and tame germ data. -/
theorem theorem_12_5_7_one_loc_bijection :
    ∃ (F : Quot (E.OrRelLoc hX hF hfT) ≃ Quot (E'.OrRelLoc hX' hF' hfT'))
      (G : Quot X.SmoothRel ≃ Quot X'.SmoothRel),
      (∀ c, E'.orbitProjLoc hX' hF' hfT' (F c) = G (E.orbitProjLoc hX hF hfT c)) ∧
      (∀ c, F (h₁.orbitOrMapLoc hF'' hF hpb₁ hX'' hX hfT'' hfT c) =
        h₂.orbitOrMapLoc hF'' hF' hpb₂ hX'' hX' hfT'' hfT' c) ∧
      ∀ v, G (h₁.smoothOrbitMap v) = h₂.smoothOrbitMap v := by
  set F₁ := Equiv.ofBijective _ (h₁.orbitOrMapLoc_bijective hF'' hF hpb₁ hX'' hX hfT'' hfT)
  set F₂ := Equiv.ofBijective _ (h₂.orbitOrMapLoc_bijective hF'' hF' hpb₂ hX'' hX' hfT'' hfT')
  set G₁ := Equiv.ofBijective _ h₁.smoothOrbitMap_bijective
  set G₂ := Equiv.ofBijective _ h₂.smoothOrbitMap_bijective
  refine ⟨F₁.symm.trans F₂, G₁.symm.trans G₂, fun c => ?_, fun c => ?_, fun v => ?_⟩
  · obtain ⟨d, rfl⟩ := F₁.surjective c
    rw [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.trans_apply]
    change E'.orbitProjLoc hX' hF' hfT' (h₂.orbitOrMapLoc hF'' hF' hpb₂ hX'' hX' hfT'' hfT' d) =
      G₂ (G₁.symm (E.orbitProjLoc hX hF hfT (h₁.orbitOrMapLoc hF'' hF hpb₁ hX'' hX hfT'' hfT d)))
    rw [h₂.orbitProjLoc_orbitOrMapLoc, h₁.orbitProjLoc_orbitOrMapLoc]
    change _ = G₂ (G₁.symm (G₁ _))
    rw [Equiv.symm_apply_apply]
    rfl
  · change F₂ (F₁.symm (F₁ c)) = _
    rw [Equiv.symm_apply_apply]
    rfl
  · change G₂ (G₁.symm (G₁ v)) = _
    rw [Equiv.symm_apply_apply]
    rfl

include hF'' in
/-- **Theorem 12.5.7 (2)**, p. 595 (2017: Theorem 12.12 (2)), without the topology: an
orientation section `o` of `σ` with the invariance of Definition 12.5.4 has exactly one
invariant section `o'` of `σ'` that corresponds to `o` over the representative, i.e.
`orEqv₂ o'_{ϕ₂ v} = orEqv₁ o_{ϕ₁ v}` for every smooth `v ∈ V`. -/
theorem theorem_12_5_7_two_invariant_loc {o : ∀ a (hs : a ∈ X.PObj.smoothSet), OrxLoc hfT a hs}
    (ho : E.IsOrInvariantLoc hF hfT o) :
    ∃! o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), OrxLoc hfT' x hs,
      E'.IsOrInvariantLoc hF' hfT' o' ∧ ∀ v (hv : v ∈ X''.PObj.smoothSet),
        h₂.orEqvLoc hpb₂ hfT'' hfT' v hv (o' (ϕ₂.obj v) (h₂.smooth_obj hv)) =
          h₁.orEqvLoc hpb₁ hfT'' hfT v hv (o (ϕ₁.obj v) (h₁.smooth_obj hv)) := by
  have ho'' := h₁.isOrInvariantLoc_pullOrLoc hF'' hF hpb₁ hfT'' hfT ho
  refine ⟨h₂.pushOrLoc hF' hpb₂ hfT'' hfT' (h₁.pullOrLoc hpb₁ hfT'' hfT o),
    ⟨h₂.isOrInvariantLoc_pushOrLoc hF'' hF' hpb₂ hfT'' hfT' ho'', fun v hv =>
      h₂.pushOrLoc_obj hF'' hF' hpb₂ hfT'' hfT' ho'' hv⟩, fun o' ⟨ho', hoo⟩ => ?_⟩
  exact h₂.pushOrLoc_unique hF'' hF' hpb₂ hfT'' hfT' ho'' ho' hoo


end Diagram

end Polyfold
