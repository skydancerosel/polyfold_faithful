import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_10

/-! Round trip for V10_10 (2021 Proposition 10.1.13, p. 472, new in the 2021 edition: for an
equivalence `F`, `F_R : 𝐗^R → 𝐘^R` is well defined, continuous and open, and `𝐗^R` is Hausdorff
iff `𝐘^R` is).

The item lists the definition `EpFunctor.reducedMap` (vocabulary, `F_R = Quot.lift`, defined for
`F` a local sc-diffeomorphism on objects) and nine theorems; `A` is the conjunction of their types,
universes at `0`:
* `mor_mem_nonEffectivePart`, `mem_nonEffectivePart_of_mor`, `nonEffectivePart_eq` (for `F` a
  local sc-diffeomorphism on objects: `𝐗^T = F⁻¹(𝐘^T) ∩ {s = t}`);
* `EpGroupoid.continuousAt_comp` (composition is continuous at a point along composable families,
  any `α : Type`);
* `IsEquivalence.isClosed_nonEffectivePart_iff` (`𝐗^T` closed iff `𝐘^T` closed, for equivalences);
* `continuous_reducedMap`, `isOpenMap_reducedMap` (for `F` a local sc-diffeomorphism on objects);
* `proposition_10_1_13` (for an equivalence: `F_R` continuous and open, `T2 𝐗^R ↔ T2 𝐘^R`);
* `EpGroupoid.theorem_7_2_22_2021` (Chapter 7: `T2 𝐗^R`, (LUC), `𝐗^T` closed are equivalent).

`B`: for B's own Definition 10.1.1 (`IsEquivB`), `F_R` is well defined (`φ ∼ φ' ⇒ [Fφ] = [Fφ']`),
some `f` with `f [φ] = [F φ]` is continuous and open, and `T2 𝐗^R ↔ T2 𝐘^R`.

* Glue `isEquivB_iff`: `IsEquivB F ↔ F.IsEquivalence` (as in `RoundTrip/Items/V10_7.lean`).
* `A_to_B`: `proposition_10_1_13` with `f = F.reducedMap _`; well-definedness through `reducedMap`
  (`Quot.sound`).
* `B_to_A`: `proposition_10_1_13` from `B` (`B`'s `f` is `reducedMap` by `Quot.ind`);
  `isClosed_nonEffectivePart_iff` from `B`'s Hausdorff equivalence and the (non-item) criterion
  `proposition_7_2_17_2021` (`T2 𝐗^R ↔ 𝐗^T` closed).  The other seven conjuncts are not
  consequences of `B`: five are about functors that are only local sc-diffeomorphisms on objects
  (`B` is about equivalences only), `continuousAt_comp` is a general lemma on ep-groupoids, and
  `theorem_7_2_22_2021` is a Chapter 7 theorem about a single ep-groupoid.  They are re-proved
  outright below (the project's proofs, copied, from non-item lemmas).
-/

namespace RoundTrip.V10_10
open Polyfold Set Function Topology Filter

universe u v

section Glue

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']

/-- B's Definition 10.1.1 is the project's `EpFunctor.IsEquivalence`. -/
theorem isEquivB_iff {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y) :
    IsEquivB F ↔ F.IsEquivalence := by
  constructor
  · rintro ⟨⟨hfaith, hfull⟩, ⟨e, he⟩, hloc⟩
    have hfun : (fun q : X.OrbitSpace => (e q : Y.OrbitSpace)) = F.orbitMap := by
      funext q
      induction q using Quot.ind with | mk x => exact he x
    refine ⟨(GroupoidFunctor.full_iff _).2 hfull, (GroupoidFunctor.faithful_iff _).2 hfaith,
      ?_, hloc⟩
    rw [← hfun]
    exact e.isHomeomorph
  · intro h
    exact ⟨⟨(GroupoidFunctor.faithful_iff _).1 h.faithful, (GroupoidFunctor.full_iff _).1 h.full⟩,
      ⟨h.isHomeomorph_orbitMap.homeomorph, fun _ => rfl⟩, h.isLocalScDiffeo_obj⟩

end Glue

/-- The project's statement (universes at `0`), one definition per theorem. -/
def A1 : Prop := type_of% @Polyfold.EpFunctor.mor_mem_nonEffectivePart.{0, 0}
def A2 : Prop := type_of% @Polyfold.EpFunctor.mem_nonEffectivePart_of_mor.{0, 0}
def A3 : Prop := type_of% @Polyfold.EpFunctor.nonEffectivePart_eq.{0, 0}
def A4 : Prop := type_of% @Polyfold.EpGroupoid.continuousAt_comp.{0, 0}
def A5 : Prop := type_of% @Polyfold.EpFunctor.IsEquivalence.isClosed_nonEffectivePart_iff.{0, 0}
def A6 : Prop := type_of% @Polyfold.EpFunctor.continuous_reducedMap.{0, 0}
def A7 : Prop := type_of% @Polyfold.EpFunctor.isOpenMap_reducedMap.{0, 0}
def A8 : Prop := type_of% @Polyfold.EpFunctor.proposition_10_1_13.{0, 0}
def A9 : Prop := type_of% @Polyfold.EpGroupoid.theorem_7_2_22_2021.{0}

/-- The project's statement. -/
def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A6 ∧ A7 ∧ A8 ∧ A9

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.mor_mem_nonEffectivePart.{0, 0},
    @Polyfold.EpFunctor.mem_nonEffectivePart_of_mor.{0, 0},
    @Polyfold.EpFunctor.nonEffectivePart_eq.{0, 0},
    @Polyfold.EpGroupoid.continuousAt_comp.{0, 0},
    @Polyfold.EpFunctor.IsEquivalence.isClosed_nonEffectivePart_iff.{0, 0},
    @Polyfold.EpFunctor.continuous_reducedMap.{0, 0},
    @Polyfold.EpFunctor.isOpenMap_reducedMap.{0, 0},
    @Polyfold.EpFunctor.proposition_10_1_13.{0, 0},
    @Polyfold.EpGroupoid.theorem_7_2_22_2021.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨-, -, -, -, -, -, -, h8, -⟩
  intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF
  have hF' := (isEquivB_iff F).1 hF
  obtain ⟨⟨hc, ho⟩, hT⟩ := h8 hF'
  refine ⟨fun φ φ' h => ?_, ⟨F.reducedMap hF'.isLocalScDiffeo_obj, fun _ => rfl, hc, ho⟩, hT⟩
  change F.reducedMap hF'.isLocalScDiffeo_obj (X.reducedπ φ) =
    F.reducedMap hF'.isLocalScDiffeo_obj (X.reducedπ φ')
  exact congrArg _ (Quot.sound h)

/-! ### The conjuncts outside `B`, re-proved outright (the project's proofs) -/

section Outright

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

theorem mor_mem_nonEffectivePart' (F : EpFunctor X Y)
    (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) {φ : Mor} (hφ : φ ∈ X.nonEffectivePart) :
    F.mor φ ∈ Y.nonEffectivePart := by
  rw [X.mem_nonEffectivePart_iff] at hφ
  rw [Y.mem_nonEffectivePart_iff]
  obtain ⟨U, V, g, hφU, hd⟩ := F.isLocalScDiffeoAt_mor (hF.at (X.src φ))
  have hmap : map F.mor (𝓝 φ) = 𝓝 (F.mor φ) := hd.toOpenPartialHomeomorph.map_nhds_eq hφU
  rw [← hmap, eventually_map]
  filter_upwards [hφ] with ψ hψ
  rw [F.src_mor, F.tgt_mor, hψ]

theorem mem_nonEffectivePart_of_mor' (F : EpFunctor X Y)
    (hF : X.PObj.IsLocalScDiffeo Y.PObj F.obj) {φ : Mor} (hst : X.src φ = X.tgt φ)
    (h : F.mor φ ∈ Y.nonEffectivePart) : φ ∈ X.nonEffectivePart := by
  rw [X.mem_nonEffectivePart_iff]
  have h1 : ∀ᶠ ψ in 𝓝 φ, F.obj (X.src ψ) = F.obj (X.tgt ψ) := by
    filter_upwards [(F.continuous_mor.tendsto φ).eventually (Y.mem_nonEffectivePart_iff.1 h)]
      with ψ hψ
    rwa [F.src_mor, F.tgt_mor] at hψ
  obtain ⟨U, V, g, hxU, hd⟩ := hF (X.src φ)
  have hs : ∀ᶠ ψ in 𝓝 φ, X.src ψ ∈ U :=
    (X.continuous_src.tendsto φ).eventually (hd.isOpen_source.mem_nhds hxU)
  have ht : ∀ᶠ ψ in 𝓝 φ, X.tgt ψ ∈ U :=
    (X.continuous_tgt.tendsto φ).eventually (hd.isOpen_source.mem_nhds (by rw [← hst]; exact hxU))
  filter_upwards [h1, hs, ht] with ψ h1 hs ht
  exact hd.injOn hs ht h1

theorem nonEffectivePart_eq' : A3 := by
  intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF
  exact Set.ext fun _ => ⟨fun h => ⟨mor_mem_nonEffectivePart' F hF h,
    EpGroupoid.src_eq_tgt_of_mem_nonEffectivePart h⟩,
    fun h => mem_nonEffectivePart_of_mor' F hF h.2 h.1⟩

theorem continuousAt_comp' : A4 := by
  intro Obj Mor _ _ _ _ _ _ α _ X f g a hf hg h
  have hS : ContinuousOn (fun q : Mor × Mor => X.comp q.1 q.2)
      (MPolyfold.fibredProduct X.src X.tgt) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact X.continuous_comp_fibredProduct
  have hpa : (f a, g a) ∈ MPolyfold.fibredProduct X.src X.tgt := h.self_of_nhds
  have ht : Tendsto (fun z => (f z, g z)) (𝓝 a)
      (𝓝[MPolyfold.fibredProduct X.src X.tgt] (f a, g a)) :=
    tendsto_nhdsWithin_iff.2 ⟨hf.prodMk_nhds hg, h⟩
  exact (hS _ hpa).tendsto.comp ht

theorem continuous_reducedMap' : A6 := by
  intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF
  -- (the project's proof is `continuous_quot_lift _ …`, whose `_` unifies with the banned
  -- well-definedness proof inside `reducedMap`; we go through the quotient map `reducedπ`)
  exact X.isOpenQuotientMap_reducedπ.isQuotientMap.continuous_iff.2
    (Y.continuous_reducedπ.comp F.continuous_mor)

theorem isOpenMap_reducedMap' : A7 := by
  intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF O hO
  have he : F.reducedMap hF '' O = Y.reducedπ '' (F.mor '' (X.reducedπ ⁻¹' O)) := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨φ, rfl⟩ := X.surjective_reducedπ q
      exact ⟨F.mor φ, ⟨φ, hq, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨φ, hφ, rfl⟩, rfl⟩
      exact ⟨X.reducedπ φ, hφ, rfl⟩
  rw [he]
  exact Y.isOpenMap_reducedπ _
    ((F.isLocalScDiffeo_mor hF).isOpenMap _ (hO.preimage X.continuous_reducedπ))

theorem theorem_7_2_22_2021' : A9 := by
  intro Obj Mor _ _ _ _ _ _ X
  tfae_have 1 ↔ 3 := X.proposition_7_2_17_2021
  tfae_have 2 ↔ 3 := X.proposition_7_2_21_2021
  tfae_finish

end Outright

theorem B_to_A : B → A := by
  intro hB
  have h5 : A5 := by
    intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF
    rw [← X.proposition_7_2_17_2021, ← Y.proposition_7_2_17_2021]
    exact (hB Obj Mor Obj' Mor' X Y F ((isEquivB_iff F).2 hF)).2.2
  have h8 : A8 := by
    intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ X Y F hF
    obtain ⟨-, ⟨f, hf, hc, ho⟩, hT⟩ := hB Obj Mor Obj' Mor' X Y F ((isEquivB_iff F).2 hF)
    have he : F.reducedMap hF.isLocalScDiffeo_obj = f := by
      funext q
      induction q using Quot.ind with | mk φ => exact (hf φ).symm
    rw [he]
    exact ⟨⟨hc, ho⟩, hT⟩
  exact ⟨@mor_mem_nonEffectivePart', @mem_nonEffectivePart_of_mor', nonEffectivePart_eq',
    continuousAt_comp', h5, continuous_reducedMap', isOpenMap_reducedMap', h8,
    theorem_7_2_22_2021'⟩

/-! ### Harness checks

The statements of `continuous_reducedMap`, `isOpenMap_reducedMap` and `proposition_10_1_13`
(`A6`, `A7`, `A8`) mention the definition `EpFunctor.reducedMap`, whose well-definedness proof
(the `Quot.lift` side condition, abstracted as a `_proof_N` field) uses the banned
`mor_mem_nonEffectivePart`.  So every term mentioning `A` reaches it, and plain `#rt_check` fails
on both directions for that name only (recorded with `#guard_msgs`); `#rt_check_soft` passes. -/

/--
error: rt_check FAIL: RoundTrip.V10_10.A_to_B uses [Polyfold.EpFunctor.mor_mem_nonEffectivePart]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_10.A_to_B [Polyfold.EpFunctor.mor_mem_nonEffectivePart,
  Polyfold.EpFunctor.mem_nonEffectivePart_of_mor, Polyfold.EpFunctor.nonEffectivePart_eq,
  Polyfold.EpGroupoid.continuousAt_comp,
  Polyfold.EpFunctor.IsEquivalence.isClosed_nonEffectivePart_iff,
  Polyfold.EpFunctor.continuous_reducedMap, Polyfold.EpFunctor.isOpenMap_reducedMap,
  Polyfold.EpFunctor.proposition_10_1_13, Polyfold.EpGroupoid.theorem_7_2_22_2021]

/--
error: rt_check FAIL: RoundTrip.V10_10.B_to_A uses [Polyfold.EpFunctor.mor_mem_nonEffectivePart]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_10.B_to_A [Polyfold.EpFunctor.mor_mem_nonEffectivePart,
  Polyfold.EpFunctor.mem_nonEffectivePart_of_mor, Polyfold.EpFunctor.nonEffectivePart_eq,
  Polyfold.EpGroupoid.continuousAt_comp,
  Polyfold.EpFunctor.IsEquivalence.isClosed_nonEffectivePart_iff,
  Polyfold.EpFunctor.continuous_reducedMap, Polyfold.EpFunctor.isOpenMap_reducedMap,
  Polyfold.EpFunctor.proposition_10_1_13, Polyfold.EpGroupoid.theorem_7_2_22_2021]

#rt_check_soft RoundTrip.V10_10.A_to_B [Polyfold.EpFunctor.mor_mem_nonEffectivePart,
  Polyfold.EpFunctor.mem_nonEffectivePart_of_mor, Polyfold.EpFunctor.nonEffectivePart_eq,
  Polyfold.EpGroupoid.continuousAt_comp,
  Polyfold.EpFunctor.IsEquivalence.isClosed_nonEffectivePart_iff,
  Polyfold.EpFunctor.continuous_reducedMap, Polyfold.EpFunctor.isOpenMap_reducedMap,
  Polyfold.EpFunctor.proposition_10_1_13, Polyfold.EpGroupoid.theorem_7_2_22_2021]
#rt_check_soft RoundTrip.V10_10.B_to_A [Polyfold.EpFunctor.mor_mem_nonEffectivePart,
  Polyfold.EpFunctor.mem_nonEffectivePart_of_mor, Polyfold.EpFunctor.nonEffectivePart_eq,
  Polyfold.EpGroupoid.continuousAt_comp,
  Polyfold.EpFunctor.IsEquivalence.isClosed_nonEffectivePart_iff,
  Polyfold.EpFunctor.continuous_reducedMap, Polyfold.EpFunctor.isOpenMap_reducedMap,
  Polyfold.EpFunctor.proposition_10_1_13, Polyfold.EpGroupoid.theorem_7_2_22_2021]
#rt_overlap RoundTrip.V10_10.B_to_A [Polyfold.EpFunctor.mor_mem_nonEffectivePart,
  Polyfold.EpFunctor.mem_nonEffectivePart_of_mor, Polyfold.EpFunctor.nonEffectivePart_eq,
  Polyfold.EpGroupoid.continuousAt_comp,
  Polyfold.EpFunctor.IsEquivalence.isClosed_nonEffectivePart_iff,
  Polyfold.EpFunctor.continuous_reducedMap, Polyfold.EpFunctor.isOpenMap_reducedMap,
  Polyfold.EpFunctor.proposition_10_1_13, Polyfold.EpGroupoid.theorem_7_2_22_2021]

end RoundTrip.V10_10
