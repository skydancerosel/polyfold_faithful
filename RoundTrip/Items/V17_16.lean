import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V17_16

set_option maxSynthPendingDepth 3

/-! Round trip for V17_16 (2021 Theorem 17.1.14, p. 753: `X_Ψ` is an ep-groupoid, tame if `(F, M)`
is tame).

The item lists the definitions `modelEpGroupoid`, `modelEP` (vocabulary) and four theorems; `A`
is the conjunction of their types, at universe `0` (`B` is stated for `GCT.{0}`; the topological
lemma `isProperMap_domRestrict_sigmaMap` at `.{0,0,0,0}`).  The conjuncts:
`exists_isProperMap_model` (the properness axiom of `X_Ψ`, any family `Ψ`),
`isProperMap_domRestrict_sigmaMap` (a map of disjoint unions proper on each piece is proper),
`isTame_modelEpGroupoid` (any family), and the main `theorem_17_1_14` (covering family `c`: an
`EpGroupoid` with groupoid `modelGroupoid`, M-polyfolds `modelObjPolyfold`, `modelMorPolyfold`,
tame if `S` is tame).

* `A_to_B`, `main_to_B`: from `theorem_17_1_14`; the pinned source and target of `B` hold by
  definition (`rfl`); `EpGroupoid.IsTame` is `PObj.IsTame`, rewritten along `X.PObj = ...`.
* `B_to_A`: `theorem_17_1_14` from `B`.  The three helper conjuncts are stated for an arbitrary
  family `Ψ : ι → S.Unif` (not only a covering family) or are pure topology, so `B` does not give
  them; they are re-proved outright, copying the project's proofs (from the non-item
  `proposition_17_1_11`, `continuous_trTgt`, `MPolyfold.isTame_sigma_iff`).

**Harness note.**  `A`'s statement mentions `modelEpGroupoid` (in `isTame_modelEpGroupoid`), whose
field `exists_isProperMap` is the banned `exists_isProperMap_model` itself (a plain constant, not
an abstracted `_proof_N`, so `#rt_check_soft` does not help), and through it the banned
`isProperMap_domRestrict_sigmaMap`.  Every term mentioning `A` reaches them, so `#rt_check` fails
on `A_to_B` and `B_to_A` (recorded with `#guard_msgs`).  The `A'` pattern: `modelEpGroupoid'` is a
copy with the same data and its properness field from the local copy `exists_isProperMap_model'`
(`= modelEpGroupoid` by `rfl`); `A'` is `A` with that constant replaced (`replace_modelEpGroupoid%`),
`A = A'` by `rfl`; `A'_to_B` and `B_to_A'` pass plain `#rt_check`, and `A_to_B`, `B_to_A` are
obtained by transport along `A_eq_A'`. -/

namespace RoundTrip.V17_16
open Polyfold Polyfold.GCT.PolyfoldConstruction
open Set Function Topology Filter

def A : Prop :=
  (type_of% @Polyfold.GCT.PolyfoldConstruction.exists_isProperMap_model.{0}) ∧
  (type_of% @Polyfold.isProperMap_domRestrict_sigmaMap.{0, 0, 0, 0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isTame_modelEpGroupoid.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_14.{0})

theorem A_holds : A :=
  ⟨@Polyfold.GCT.PolyfoldConstruction.exists_isProperMap_model.{0},
    @Polyfold.isProperMap_domRestrict_sigmaMap.{0, 0, 0, 0},
    @Polyfold.GCT.PolyfoldConstruction.isTame_modelEpGroupoid.{0},
    @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_14.{0}⟩

theorem main_to_B : type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_14.{0} → B := by
  intro h C S c
  obtain ⟨X, hX, hO, hM, hT⟩ := h S c
  refine ⟨fun _ _ => ⟨rfl, rfl⟩, ⟨X, hX, hO, hM⟩, fun hS => ?_⟩
  have := hT hS
  unfold EpGroupoid.IsTame at this
  rwa [hO] at this


theorem B_to_main : B → type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_14.{0} := by
  intro hB C S c
  obtain ⟨-, ⟨X, hX, hO, hM⟩, hT⟩ := hB C S c
  refine ⟨X, hX, hO, hM, fun hS => ?_⟩
  unfold EpGroupoid.IsTame
  rw [hO]
  exact hT hS

/-! ### The helper conjuncts, re-proved outright (the project's proofs) -/

section ProperSigma

variable {K J : Type} {A : K → Type} {B : J → Type} [∀ k, TopologicalSpace (A k)]
  [∀ j, TopologicalSpace (B j)]

theorem isProperMap_domRestrict_sigmaMap' (τ : K → J) (f : ∀ k, A k → B (τ k))
    (hfc : ∀ k, Continuous (f k)) (D : Set (Σ k, A k))
    (hτ : ∀ k k', (Sigma.mk k ⁻¹' D).Nonempty → (Sigma.mk k' ⁻¹' D).Nonempty → τ k = τ k' →
      k = k')
    (hf : ∀ k, IsProperMap ((Sigma.mk k ⁻¹' D).domRestrict (f k))) :
    IsProperMap (D.domRestrict (Sigma.map τ f)) := by
  -- the inclusion of the `k`-th piece of `D` into `D`
  let incl : ∀ k, (Sigma.mk k ⁻¹' D) → D := fun k a => ⟨⟨k, a.1⟩, a.2⟩
  have hincl : ∀ k, Continuous (incl k) := fun k =>
    (continuous_sigmaMk.comp continuous_subtype_val).subtype_mk _
  have hcomp : ∀ k (a : Sigma.mk k ⁻¹' D),
      D.domRestrict (Sigma.map τ f) (incl k a) = ⟨τ k, f k a.1⟩ := fun _ _ => rfl
  -- every element of `D` comes from a piece
  have hsurj : ∀ z : D, ∃ k a, z = incl k a := by
    rintro ⟨⟨k, a⟩, hz⟩
    exact ⟨k, ⟨a, hz⟩, rfl⟩
  -- the preimage of the `j`-th piece of the target
  have hpre : ∀ (Z : Set D) (j : J), Sigma.mk j ⁻¹' (D.domRestrict (Sigma.map τ f) '' Z) ⊆
      ⋃ (k) (hk : τ k = j), (fun y => hk ▸ y) '' ((Sigma.mk k ⁻¹' D).domRestrict (f k) ''
        (incl k ⁻¹' Z)) := by
    intro Z j y ⟨z, hz, hzy⟩
    obtain ⟨k, a, rfl⟩ := hsurj z
    rw [hcomp] at hzy
    obtain ⟨hk, hy⟩ := Sigma.mk.inj_iff.1 hzy
    refine mem_iUnion₂.2 ⟨k, hk, ?_⟩
    subst hk
    exact ⟨f k a.1, ⟨a, hz, rfl⟩, eq_of_heq hy⟩
  have hpre' : ∀ (Z : Set D) (j : J) (k : K) (hk : τ k = j) (a : Sigma.mk k ⁻¹' D),
      incl k a ∈ Z → (hk ▸ f k a.1 : B j) ∈
        Sigma.mk j ⁻¹' (D.domRestrict (Sigma.map τ f) '' Z) := by
    intro Z j k hk a ha
    subst hk
    exact ⟨incl k a, ha, rfl⟩
  -- at most one piece of `D` lies over `j`
  have hunique : ∀ j, ∀ k₁ k₂ (h₁ : τ k₁ = j) (h₂ : τ k₂ = j),
      (Sigma.mk k₁ ⁻¹' D).Nonempty → (Sigma.mk k₂ ⁻¹' D).Nonempty → k₁ = k₂ :=
    fun j k₁ k₂ h₁ h₂ hn₁ hn₂ => hτ k₁ k₂ hn₁ hn₂ (h₁.trans h₂.symm)
  have himage : ∀ (Z : Set D) (j : J), (Sigma.mk j ⁻¹' (D.domRestrict (Sigma.map τ f) '' Z)) =
      ⋃ (k) (hk : τ k = j), (fun y => hk ▸ y) '' ((Sigma.mk k ⁻¹' D).domRestrict (f k) ''
        (incl k ⁻¹' Z)) := by
    intro Z j
    refine (hpre Z j).antisymm ?_
    intro y hy
    obtain ⟨k, hk, _, ⟨a, ha, rfl⟩, rfl⟩ := mem_iUnion₂.1 hy
    exact hpre' Z j k hk a ha
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨?_, ?_, ?_⟩
  · exact (continuous_sigma_map.2 hfc).comp continuous_subtype_val
  · intro Z hZ
    refine isClosed_sigma_iff.2 fun j => ?_
    rw [himage Z j]
    -- the union has at most one non-empty member
    by_cases hex : ∃ k, τ k = j ∧ (Sigma.mk k ⁻¹' D).Nonempty
    · obtain ⟨k₀, hk₀, hn₀⟩ := hex
      have heq : (⋃ (k) (hk : τ k = j), (fun y => hk ▸ y) '' ((Sigma.mk k ⁻¹' D).domRestrict
          (f k) '' (incl k ⁻¹' Z))) = (fun y => hk₀ ▸ y) '' ((Sigma.mk k₀ ⁻¹' D).domRestrict
          (f k₀) '' (incl k₀ ⁻¹' Z)) := by
        refine subset_antisymm ?_ (subset_iUnion₂_of_subset k₀ hk₀ subset_rfl)
        refine iUnion₂_subset fun k hk => ?_
        rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        obtain rfl := hunique j k k₀ hk hk₀ ⟨_, a.2⟩ hn₀
        exact ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      rw [heq]
      subst hk₀
      have := (hf k₀).isClosedMap _ (hZ.preimage (hincl k₀))
      convert this using 1
      exact Set.image_id _
    · simp only [not_exists, not_and] at hex
      convert isClosed_empty
      refine eq_empty_of_forall_notMem fun y hy => ?_
      obtain ⟨k, hk, _, ⟨a, -, rfl⟩, rfl⟩ := mem_iUnion₂.1 hy
      exact hex k hk ⟨_, a.2⟩
  · rintro ⟨j, y⟩
    have hfib : D.domRestrict (Sigma.map τ f) ⁻¹' {⟨j, y⟩} =
        ⋃ (k) (hk : τ k = j), incl k '' ((Sigma.mk k ⁻¹' D).domRestrict (f k) ⁻¹'
          {hk.symm ▸ y}) := by
      ext z
      obtain ⟨k, a, rfl⟩ := hsurj z
      simp only [mem_preimage, mem_singleton_iff, mem_iUnion]
      rw [hcomp]
      constructor
      · intro h
        obtain ⟨hk, hy⟩ := Sigma.mk.inj_iff.1 h
        refine ⟨k, hk, a, ?_, rfl⟩
        subst hk
        exact eq_of_heq hy
      · rintro ⟨k', hk', a', ha', he⟩
        have hk'' : k' = k := by
          have h1 : (incl k' a').1.1 = (incl k a).1.1 := congrArg (fun z : D => z.1.1) he
          exact h1
        subst hk''
        have : a' = a := by
          have h2 := congrArg (fun z : D => z.1) he
          exact Subtype.ext (eq_of_heq (Sigma.mk.inj_iff.1 h2).2)
        subst this
        subst hk'
        change f k' a'.1 = y at ha'
        rw [ha']
    rw [hfib]
    by_cases hex : ∃ k, τ k = j ∧ (Sigma.mk k ⁻¹' D).Nonempty
    · obtain ⟨k₀, hk₀, hn₀⟩ := hex
      have heq : (⋃ (k) (hk : τ k = j), incl k '' ((Sigma.mk k ⁻¹' D).domRestrict (f k) ⁻¹'
          {hk.symm ▸ y})) = incl k₀ '' ((Sigma.mk k₀ ⁻¹' D).domRestrict (f k₀) ⁻¹'
          {hk₀.symm ▸ y}) := by
        refine subset_antisymm ?_ (subset_iUnion₂_of_subset k₀ hk₀ subset_rfl)
        refine iUnion₂_subset fun k hk => ?_
        rintro _ ⟨a, ha, rfl⟩
        obtain rfl := hunique j k k₀ hk hk₀ ⟨_, a.2⟩ hn₀
        exact ⟨a, ha, rfl⟩
      rw [heq]
      exact ((hf k₀).isCompact_preimage isCompact_singleton).image (hincl k₀)
    · simp only [not_exists, not_and] at hex
      convert isCompact_empty
      refine eq_empty_of_forall_notMem fun z hz => ?_
      obtain ⟨k, hk, a, -, rfl⟩ := mem_iUnion₂.1 hz
      exact hex k hk ⟨_, a.2⟩

/-- A map out of an empty space is proper. -/
theorem isProperMap_of_isEmpty' {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [IsEmpty X]
    (f : X → Y) : IsProperMap f := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨⟨fun s _ => ?_⟩, fun s _ => ?_, fun y => ?_⟩
  · rw [Set.eq_empty_of_isEmpty (f ⁻¹' s)]; exact isOpen_empty
  · rw [Set.eq_empty_of_isEmpty s, image_empty]; exact isClosed_empty
  · rw [Set.eq_empty_of_isEmpty (f ⁻¹' {y})]; exact isCompact_empty

end ProperSigma

section Model
variable {C : GCT.{0}} (S : C.PolyfoldConstruction) {ι : Type} (Ψ : ι → S.Unif)

theorem exists_isProperMap_model' (x : S.ModelObj Ψ) :
    ∃ V : Set (S.ModelObj Ψ), IsOpen V ∧ x ∈ V ∧
      IsProperMap (((S.modelGroupoid Ψ).src ⁻¹' closure V).domRestrict
        (S.modelGroupoid Ψ).tgt) := by
  obtain ⟨i, q⟩ := x
  obtain ⟨U, hU, hqU, hprop⟩ := S.proposition_17_1_11 (Ψ i) q
  refine ⟨S.objMk Ψ i '' U, isOpenMap_sigmaMk (σ := fun i => (Ψ i).1.O) _ hU, ⟨q, hqU, rfl⟩, ?_⟩
  have hcl : closure (S.objMk Ψ i '' U) = S.objMk Ψ i '' closure U :=
    (IsClosedEmbedding.sigmaMk (σ := fun i => (Ψ i).1.O) (i := i)).closure_image_eq U
  rw [hcl]
  set D := (S.modelGroupoid Ψ).src ⁻¹' (S.objMk Ψ i '' closure U)
  -- the pieces of `D` lie over `λ₀ = i`
  have hD : ∀ p : ι × ι, (S.morMk Ψ p ⁻¹' D).Nonempty → p.1 = i := by
    rintro p ⟨a, q', -, hq'⟩
    exact ((Sigma.mk.inj_iff.1 hq').1).symm
  have hτ : ∀ p p' : ι × ι, (S.morMk Ψ p ⁻¹' D).Nonempty → (S.morMk Ψ p' ⁻¹' D).Nonempty →
      p.2 = p'.2 → p = p' := fun p p' hp hp' h => Prod.ext ((hD p hp).trans (hD p' hp').symm) h
  have hpiece : ∀ p : ι × ι, IsProperMap ((S.morMk Ψ p ⁻¹' D).domRestrict
      fun a : S.Tr (Ψ p.1) (Ψ p.2) => a.tgt) := by
    rintro ⟨i', j⟩
    by_cases hi : i' = i
    · subst hi
      have hDp : S.morMk Ψ (i', j) ⁻¹' D =
          (fun a : S.Tr (Ψ i') (Ψ j) => a.src) ⁻¹' closure U := by
        ext a
        constructor
        · rintro ⟨q', hq', he⟩
          have : q' = a.src := eq_of_heq (Sigma.mk.inj_iff.1 he).2
          change a.src ∈ closure U
          rw [← this]
          exact hq'
        · intro ha
          exact ⟨a.src, ha, rfl⟩
      rw [hDp]
      exact hprop (Ψ j)
    · have : IsEmpty (S.morMk Ψ (i', j) ⁻¹' D) :=
        ⟨fun a => hi (hD (i', j) ⟨a.1, a.2⟩)⟩
      exact isProperMap_of_isEmpty' _
  exact isProperMap_domRestrict_sigmaMap' (A := fun p : ι × ι => S.Tr (Ψ p.1) (Ψ p.2))
    (B := fun i => (Ψ i).1.O) Prod.snd (fun p a => a.tgt)
    (fun p => S.continuous_trTgt (Ψ p.1) (Ψ p.2)) D hτ hpiece

/-- A copy of `modelEpGroupoid` whose properness field is the local copy
`exists_isProperMap_model'`; equal to `modelEpGroupoid` by `rfl` (proof irrelevance). -/
noncomputable def modelEpGroupoid' : EpGroupoid (S.ModelObj Ψ) (S.ModelMor Ψ) where
  toGroupoidStr := S.modelGroupoid Ψ
  PObj := S.modelObjPolyfold Ψ
  PMor := S.modelMorPolyfold Ψ
  isLocalScDiffeo_src := S.isLocalScDiffeo_modelSrc Ψ
  isLocalScDiffeo_tgt := S.isLocalScDiffeo_modelTgt Ψ
  isScSmoothMap_unit := S.isScSmoothMap_modelUnit Ψ
  isScSmoothMap_inv := S.isScSmoothMap_modelInv Ψ
  exists_isProperMap := exists_isProperMap_model' S Ψ
  isScSmoothComp := S.isScSmoothComp_model Ψ

theorem isTame_modelEpGroupoid' (h : S.IsTame) : (modelEpGroupoid' S Ψ).IsTame :=
  (MPolyfold.isTame_sigma_iff _).2 fun i => by
    obtain ⟨α, hα⟩ := (Ψ i).2
    exact h α _ hα

end Model

example : @modelEpGroupoid' = @Polyfold.GCT.PolyfoldConstruction.modelEpGroupoid.{0} := rfl

open Lean Elab Term Meta in
/-- `replace_modelEpGroupoid% t`: the term `t` with every occurrence of the constant
`Polyfold.GCT.PolyfoldConstruction.modelEpGroupoid.{0}` replaced by
`RoundTrip.V17_16.modelEpGroupoid'`. -/
elab "replace_modelEpGroupoid% " t:term : term => do
  let e ← instantiateMVars (← elabTerm t none)
  let e' := e.replace fun s => match s with
    | .const n us =>
      if n == ``Polyfold.GCT.PolyfoldConstruction.modelEpGroupoid && us.all (·.isZero) then
        some (.const ``RoundTrip.V17_16.modelEpGroupoid' [])
      else none
    | _ => none
  if e'.getUsedConstants.contains ``Polyfold.GCT.PolyfoldConstruction.modelEpGroupoid then
    throwError "replace_modelEpGroupoid%: an occurrence at nonzero universes is left"
  return e'

/-- `A` with `modelEpGroupoid` replaced by its copy `modelEpGroupoid'`. -/
def A' : Prop := replace_modelEpGroupoid%
  ((type_of% @Polyfold.GCT.PolyfoldConstruction.exists_isProperMap_model.{0}) ∧
  (type_of% @Polyfold.isProperMap_domRestrict_sigmaMap.{0, 0, 0, 0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.isTame_modelEpGroupoid.{0}) ∧
  (type_of% @Polyfold.GCT.PolyfoldConstruction.theorem_17_1_14.{0}))

theorem A_eq_A' : A = A' := rfl

theorem A'_to_B : A' → B := fun hA => main_to_B hA.2.2.2

theorem A_to_B : A → B := fun hA => A'_to_B (A_eq_A' ▸ hA)

theorem B_to_A' : B → A' := fun hB =>
  ⟨fun {_} S {_} Ψ x => exists_isProperMap_model' S Ψ x,
    fun τ f hfc D hτ hf => isProperMap_domRestrict_sigmaMap' τ f hfc D hτ hf,
    fun {_} S {_} Ψ h => isTame_modelEpGroupoid' S Ψ h, B_to_main hB⟩

theorem B_to_A : B → A := fun hB => A_eq_A' ▸ B_to_A' hB

#rt_check RoundTrip.V17_16.A'_to_B [Polyfold.GCT.PolyfoldConstruction.exists_isProperMap_model,
  Polyfold.isProperMap_domRestrict_sigmaMap, Polyfold.GCT.PolyfoldConstruction.isTame_modelEpGroupoid,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_14]
#rt_check RoundTrip.V17_16.B_to_A' [Polyfold.GCT.PolyfoldConstruction.exists_isProperMap_model,
  Polyfold.isProperMap_domRestrict_sigmaMap, Polyfold.GCT.PolyfoldConstruction.isTame_modelEpGroupoid,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_14]
#rt_check RoundTrip.V17_16.main_to_B [Polyfold.GCT.PolyfoldConstruction.exists_isProperMap_model,
  Polyfold.isProperMap_domRestrict_sigmaMap, Polyfold.GCT.PolyfoldConstruction.isTame_modelEpGroupoid,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_14]
#rt_check RoundTrip.V17_16.B_to_main [Polyfold.GCT.PolyfoldConstruction.exists_isProperMap_model,
  Polyfold.isProperMap_domRestrict_sigmaMap, Polyfold.GCT.PolyfoldConstruction.isTame_modelEpGroupoid,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_14]
/--
error: rt_check FAIL: RoundTrip.V17_16.A_to_B uses [Polyfold.GCT.PolyfoldConstruction.exists_isProperMap_model,
 Polyfold.isProperMap_domRestrict_sigmaMap]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V17_16.A_to_B [Polyfold.GCT.PolyfoldConstruction.exists_isProperMap_model,
  Polyfold.isProperMap_domRestrict_sigmaMap, Polyfold.GCT.PolyfoldConstruction.isTame_modelEpGroupoid,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_14]
/--
error: rt_check FAIL: RoundTrip.V17_16.B_to_A uses [Polyfold.GCT.PolyfoldConstruction.exists_isProperMap_model,
 Polyfold.isProperMap_domRestrict_sigmaMap]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V17_16.B_to_A [Polyfold.GCT.PolyfoldConstruction.exists_isProperMap_model,
  Polyfold.isProperMap_domRestrict_sigmaMap, Polyfold.GCT.PolyfoldConstruction.isTame_modelEpGroupoid,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_14]
#rt_overlap RoundTrip.V17_16.B_to_A' [Polyfold.GCT.PolyfoldConstruction.exists_isProperMap_model,
  Polyfold.isProperMap_domRestrict_sigmaMap, Polyfold.GCT.PolyfoldConstruction.isTame_modelEpGroupoid,
  Polyfold.GCT.PolyfoldConstruction.theorem_17_1_14]

end RoundTrip.V17_16
