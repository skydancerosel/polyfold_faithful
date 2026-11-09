import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_30

/-! Round trip for V10_30 (2021 Definition 10.4.10 = 2017 Definition 10.12, and its equivalence
with Definition 10.4.8).

The item lists the definitions `IsStrongBundleNatTransMap` (Definition 10.4.10) and
`IsStrongBundleNatTransMap.toNatTrans` (10.4.10 ⇒ 10.4.8, as a construction of a
`StrongBundleNatTrans`) and three theorems; `A` (universes at `0`) is the conjunction of their
types: `StrongBundleNatTrans.isStrongBundleNatTransMap` (10.4.8 ⇒ 10.4.10, for `Φ` a strong
bundle functor), `StrongBundleNatTrans.orbitMap_eq` and `StrongBundleNatEquiv.orbitMap_eq`
(`Φ ≃ Ψ ⇒ |Φ| = |Ψ|`, p. 503).

`B` (for strong bundle functors `Φ`, `Ψ` covering `ϕ`, `ψ`): (a) the project's
`IsStrongBundleNatTransMap` is the text's Definition 10.4.10 (`IsSBNatTransMapB`), (b) Definition
10.4.8 (`IsSBNatTransB`, the clauses of the project's `StrongBundleNatTrans`) holds iff
Definition 10.4.10 does.

* `A_to_B`: (a) is a definitional comparison, proved outright (`iff_map`: the fields agree;
  `μ'(T(w)) = μ'(τ(P(w)), Φ(w))` by `T_val`).  (b) ⇒: package `(T, τ)` as a `StrongBundleNatTrans`
  and apply `A`'s `isStrongBundleNatTransMap`.  (b) ⇐ is not a theorem of `A`: in the project it
  is the definition `IsStrongBundleNatTransMap.toNatTrans` (data), which is used here; its fields
  give the clauses of `IsSBNatTransB`.
* `B_to_A`: vacuous.  `A`'s `isStrongBundleNatTransMap` assumes only `Φ` to be a strong bundle
  functor (`B` needs `Ψ` too), and `B` says nothing about `|Φ| = |Ψ|`; the three conjuncts are
  re-proved outright from non-item project lemmas (`T_val`, `isStrongBundleMap_T` of V10_29,
  `orbitMap_eq_of_forall_exists`). -/

namespace RoundTrip.V10_30
open Polyfold Set Function

/-- The project's statement (universes at `0`). -/
def A1 : Prop :=
  type_of% @Polyfold.EpStrongBundle.StrongBundleNatTrans.isStrongBundleNatTransMap.{0}
def A2 : Prop := type_of% @Polyfold.EpStrongBundle.StrongBundleNatTrans.orbitMap_eq.{0}
def A3 : Prop := type_of% @Polyfold.EpStrongBundle.StrongBundleNatEquiv.orbitMap_eq.{0}

def A : Prop := A1 ∧ A2 ∧ A3

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.StrongBundleNatTrans.isStrongBundleNatTransMap.{0},
    @Polyfold.EpStrongBundle.StrongBundleNatTrans.orbitMap_eq.{0},
    @Polyfold.EpStrongBundle.StrongBundleNatEquiv.orbitMap_eq.{0}⟩

section

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'}

/-- **(a)**: the project's Definition 10.4.10 is the text's (no hypothesis on `Φ`, `Ψ`). -/
theorem iff_map (hs' : X'.PMor.IsScSmoothMap X'.PObj X'.src) {ϕ ψ : EpFunctor X X'}
    (Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid) (τ : EpNatTrans ϕ ψ)
    (T : W → pullbackSpace P' X'.src) :
    E.IsStrongBundleNatTransMap E' Φ Ψ τ T ↔ IsSBNatTransMapB hs' E E' Φ Ψ τ T := by
  constructor
  · intro hT
    refine ⟨hT.isStrongBundleMap, hT.T_val, fun w => ?_⟩
    have hm : P' (Φ.obj w) = X'.src (τ.app (P w)) := by
      have h2 := (T w).2
      rw [hT.T_val w] at h2
      exact h2
    exact ⟨hm, (hT.obj_eq w).trans (congrArg E'.μ (Subtype.ext (hT.T_val w)))⟩
  · rintro ⟨hm, hv, ho⟩
    refine ⟨hv, hm, fun w => ?_⟩
    obtain ⟨h, he⟩ := ho w
    rw [he]
    exact congrArg E'.μ (Subtype.ext (hv w)).symm

end

theorem A_to_B : A → B := by
  rintro ⟨hmap, -, -⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
    hs' E E' ϕ ψ Φ Ψ hΦ hΨ τ T
  have ha := iff_map hs' Φ Ψ τ T
  refine ⟨ha, fun hT => ?_, fun hT => ?_⟩
  · -- 10.4.8 ⇒ 10.4.10: `A`'s `isStrongBundleNatTransMap`
    let θ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ :=
      ⟨T, fun w => (hT.1 w).1, fun w => (hT.1 w).2, hT.2.1, τ, fun w => (hT.2.2 w).symm⟩
    exact ha.1 (hmap θ hΦ)
  · -- 10.4.10 ⇒ 10.4.8: the item's definition `toNatTrans` (data, not part of `A`)
    let N := EpStrongBundle.IsStrongBundleNatTransMap.toNatTrans (ha.2 hT) hΦ hΨ
    exact ⟨fun w => ⟨N.src_T w, N.tgt_T w⟩, N.naturality, fun w => (N.app_P w).symm⟩

/-- Vacuous for the audit: `A` is re-proved outright, `B` is not used. -/
theorem B_to_A : B → A := fun _ =>
  ⟨fun θ hΦ => ⟨θ.T_val, θ.isStrongBundleMap_T hΦ, fun w => (θ.tgt_T w).symm⟩,
    fun θ => EpStrongBundle.orbitMap_eq_of_forall_exists fun w => ⟨θ.T w, θ.src_T w, θ.tgt_T w⟩,
    fun h => EpStrongBundle.orbitMap_eq_of_forall_exists fun w =>
      ⟨h.some.T w, h.some.src_T w, h.some.tgt_T w⟩⟩

#rt_check RoundTrip.V10_30.A_to_B
  [Polyfold.EpStrongBundle.StrongBundleNatTrans.isStrongBundleNatTransMap,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.orbitMap_eq,
  Polyfold.EpStrongBundle.StrongBundleNatEquiv.orbitMap_eq]
#rt_check RoundTrip.V10_30.B_to_A
  [Polyfold.EpStrongBundle.StrongBundleNatTrans.isStrongBundleNatTransMap,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.orbitMap_eq,
  Polyfold.EpStrongBundle.StrongBundleNatEquiv.orbitMap_eq]
#rt_overlap RoundTrip.V10_30.B_to_A
  [Polyfold.EpStrongBundle.StrongBundleNatTrans.isStrongBundleNatTransMap,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.orbitMap_eq,
  Polyfold.EpStrongBundle.StrongBundleNatEquiv.orbitMap_eq]

end RoundTrip.V10_30
