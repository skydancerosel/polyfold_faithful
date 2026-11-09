import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_6

/-!
Round trip for V10_6 (2021 Proposition 10.1.6, p. 464 (2017: Proposition 10.3, p. 336): if `F`
and `Φ ∘ F` are equivalences and `Φ` is sc-smooth, `Φ` is an equivalence).

The item lists the definition `MPolyfold.IsLocalScDiffeoAt` (vocabulary) and eight theorems.  `A`
is the conjunction of their types, universes at `0`: `EpFunctor.proposition_10_1_6`, the four
lemmas on local sc-diffeomorphisms at a point `IsLocalScDiffeoAt.comp`, `congr`,
`of_comp_left`, `of_comp_right`, and `EpFunctor.isLocalScDiffeoAt_mor`, `isLocalScDiffeo_mor`,
`isLocalScDiffeoAt_obj_tgt` (transport along morphisms).

`B`: for sc-smooth functors `F : X → Y`, `Φ : Y → Z` and any `H : X → Z` equal to `Φ ∘ F` on
objects and morphisms, `IsEquivB F → IsEquivB H → IsEquivB Φ`.

* `A ⇒ B`: `H = Φ.comp F` (`EpFunctor.ext`), `A`'s `proposition_10_1_6`, and the glue between
  `IsEquivB` and the project's `IsEquivalence` (the project's orbit space with the quotient
  topology is definitionally the blind `Quot`; `full_iff`, `faithful_iff` for (1)).
* `B ⇒ A`: `proposition_10_1_6` is `B` with `H := Φ.comp F` (`rfl` equations).  The seven lemmas
  are general facts about local sc-diffeomorphisms and functors (no equivalence in their
  hypotheses), not consequences of `B`; they are re-proved outright (`comp'`, `congr'`, ...,
  copies of the project's proofs, each built on the previous copies and non-item lemmas such as
  `IsScDiffeoOn.restrict`, `IsScDiffeoOn.comp`, `IsScDiffeoOn.symm`).
-/

namespace RoundTrip.V10_6
open Polyfold Set Function Topology Filter

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpFunctor.proposition_10_1_6.{0, 0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.IsLocalScDiffeoAt.comp.{0, 0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.IsLocalScDiffeoAt.congr.{0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.IsLocalScDiffeoAt.of_comp_left.{0, 0, 0}) ∧
  (type_of% @Polyfold.MPolyfold.IsLocalScDiffeoAt.of_comp_right.{0, 0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.isLocalScDiffeoAt_mor.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.isLocalScDiffeo_mor.{0, 0}) ∧
  (type_of% @Polyfold.EpFunctor.isLocalScDiffeoAt_obj_tgt.{0, 0})

theorem A_holds : A :=
  ⟨@EpFunctor.proposition_10_1_6.{0, 0, 0}, @MPolyfold.IsLocalScDiffeoAt.comp.{0, 0, 0},
    @MPolyfold.IsLocalScDiffeoAt.congr.{0, 0}, @MPolyfold.IsLocalScDiffeoAt.of_comp_left.{0, 0, 0},
    @MPolyfold.IsLocalScDiffeoAt.of_comp_right.{0, 0, 0}, @EpFunctor.isLocalScDiffeoAt_mor.{0, 0},
    @EpFunctor.isLocalScDiffeo_mor.{0, 0}, @EpFunctor.isLocalScDiffeoAt_obj_tgt.{0, 0}⟩

/-! ### Glue -/

section Glue

variable {Obj Mor Obj' Mor' : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

theorem orbitHomeoB_iff (F : EpFunctor X Y) : OrbitHomeoB F ↔ IsHomeomorph F.orbitMap := by
  constructor
  · rintro ⟨e, he⟩
    have : (F.orbitMap : X.OrbitSpace → Y.OrbitSpace) = e := by
      funext a
      induction a using Quotient.inductionOn with | h x => exact (he x).symm
    rw [this]
    exact e.isHomeomorph
  · intro h
    exact ⟨h.homeomorph, fun _ => rfl⟩

theorem isEquivB_iff (F : EpFunctor X Y) : IsEquivB F ↔ F.IsEquivalence :=
  ⟨fun h => ⟨(GroupoidFunctor.full_iff _).2 h.1.2, (GroupoidFunctor.faithful_iff _).2 h.1.1,
      (orbitHomeoB_iff F).1 h.2.1, h.2.2⟩,
    fun h => ⟨⟨(GroupoidFunctor.faithful_iff _).1 h.faithful,
      (GroupoidFunctor.full_iff _).1 h.full⟩, (orbitHomeoB_iff F).2 h.isHomeomorph_orbitMap,
      h.isLocalScDiffeo_obj⟩⟩

end Glue

/-! ### Re-proofs of the seven lemmas (copies of the project's proofs) -/

section Reproof

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

theorem comp' {f : X → Y} {g : Y → Z} {x : X}
    (hg : Q.IsLocalScDiffeoAt S g (f x)) (hf : P.IsLocalScDiffeoAt Q f x) :
    P.IsLocalScDiffeoAt S (g ∘ f) x := by
  obtain ⟨U₁, V₁, h₁, hx, hd₁⟩ := hf
  obtain ⟨U₂, V₂, h₂, hfx, hd₂⟩ := hg
  have hU : IsOpen (U₁ ∩ f ⁻¹' U₂) :=
    hd₁.isScSmoothOn.continuousOn.isOpen_inter_preimage hd₁.isOpen_source hd₂.isOpen_source
  have e₁ := hd₁.restrict hU inter_subset_left
  have hsub : V₁ ∩ h₁ ⁻¹' (U₁ ∩ f ⁻¹' U₂) ⊆ U₂ := fun y hy => by
    have := hy.2.2
    rwa [mem_preimage, hd₁.right_inv y hy.1] at this
  exact ⟨U₁ ∩ f ⁻¹' U₂, _, h₁ ∘ h₂, ⟨hx, hfx⟩, (hd₂.restrict e₁.isOpen_target hsub).comp e₁⟩

theorem congr' {f f' : X → Y} {x : X} (hf : P.IsLocalScDiffeoAt Q f x)
    (h : f =ᶠ[𝓝 x] f') : P.IsLocalScDiffeoAt Q f' x := by
  obtain ⟨U, V, g, hx, hd⟩ := hf
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.1 h
  have hUW : IsOpen (U ∩ W) := hd.isOpen_source.inter hWo
  exact ⟨U ∩ W, _, g, ⟨hx, hxW⟩,
    (hd.restrict hUW inter_subset_left).congr fun y hy => hWsub hy.2⟩

theorem of_comp_left' {s : Y → Z} {τ : X → Y} {x : X}
    (hs : Q.IsLocalScDiffeoAt S s (τ x)) (hτ : Continuous τ)
    (h : P.IsLocalScDiffeoAt S (s ∘ τ) x) : P.IsLocalScDiffeoAt Q τ x := by
  obtain ⟨W, V, σ, hxW, hd⟩ := hs
  have h1 : S.IsLocalScDiffeoAt Q σ ((s ∘ τ) x) := hd.symm.isLocalScDiffeoAt (hd.mapsTo hxW)
  refine congr' (comp' h1 h) ?_
  filter_upwards [hτ.continuousAt.preimage_mem_nhds (hd.isOpen_source.mem_nhds hxW)] with z hz
  exact hd.left_inv _ hz

theorem of_comp_right' {f : X → Y} {g : Y → Z} {x : X}
    (hf : P.IsLocalScDiffeoAt Q f x) (h : P.IsLocalScDiffeoAt S (g ∘ f) x) :
    Q.IsLocalScDiffeoAt S g (f x) := by
  obtain ⟨U, V, k, hxU, hd⟩ := hf
  have hk : Q.IsLocalScDiffeoAt P k (f x) := hd.symm.isLocalScDiffeoAt (hd.mapsTo hxU)
  have h' : P.IsLocalScDiffeoAt S (g ∘ f) (k (f x)) := by rw [hd.left_inv x hxU]; exact h
  refine congr' (comp' h' hk) ?_
  filter_upwards [hd.isOpen_target.mem_nhds (hd.mapsTo hxU)] with z hz
  simp only [Function.comp_apply, hd.right_inv z hz]

end Reproof

section ReproofFunctor

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} (F : EpFunctor X Y)

theorem isLocalScDiffeoAt_mor' {φ : Mor}
    (h : X.PObj.IsLocalScDiffeoAt Y.PObj F.obj (X.src φ)) :
    X.PMor.IsLocalScDiffeoAt Y.PMor F.mor φ := by
  have h1 : X.PMor.IsLocalScDiffeoAt Y.PObj (Y.src ∘ F.mor) φ :=
    congr' (comp' h (X.isLocalScDiffeo_src.at φ))
      (Eventually.of_forall fun z => (F.src_mor z).symm)
  exact of_comp_left' (Y.isLocalScDiffeo_src.at (F.mor φ)) F.continuous_mor h1

theorem isLocalScDiffeo_mor' (h : X.PObj.IsLocalScDiffeo Y.PObj F.obj) :
    X.PMor.IsLocalScDiffeo Y.PMor F.mor := fun _ => isLocalScDiffeoAt_mor' F (h.at _)

theorem isLocalScDiffeoAt_obj_tgt' {φ : Mor}
    (h : X.PObj.IsLocalScDiffeoAt Y.PObj F.obj (X.src φ)) :
    X.PObj.IsLocalScDiffeoAt Y.PObj F.obj (X.tgt φ) := by
  have h1 : X.PMor.IsLocalScDiffeoAt Y.PObj (F.obj ∘ X.tgt) φ :=
    congr' (comp' (Y.isLocalScDiffeo_tgt.at (F.mor φ)) (isLocalScDiffeoAt_mor' F h))
      (Eventually.of_forall fun z => F.tgt_mor z)
  exact of_comp_right' (X.isLocalScDiffeo_tgt.at φ) h1

end ReproofFunctor

/-! ### `A ⇒ B` -/

theorem A_to_B : A → B := by
  intro hA Obj Mor Obj' Mor' Obj'' Mor'' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ X Y Z F Φ H hHo hHm
    hF hH
  have e : H = Φ.comp F := EpFunctor.ext hHo hHm
  subst e
  exact (isEquivB_iff Φ).2 (hA.1 ((isEquivB_iff F).1 hF) ((isEquivB_iff _).1 hH))

/-! ### `B ⇒ A` -/

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, @comp', @congr', @of_comp_left', @of_comp_right', @isLocalScDiffeoAt_mor',
    @isLocalScDiffeo_mor', @isLocalScDiffeoAt_obj_tgt'⟩
  intro Obj Mor _ _ _ _ _ _ Obj' Mor' _ _ _ _ _ _ Obj'' Mor'' _ _ _ _ _ _ X Y Z F Φ hF hΦF
  exact (isEquivB_iff Φ).1 (hB _ _ _ _ _ _ X Y Z F Φ (Φ.comp F) rfl rfl ((isEquivB_iff F).2 hF)
    ((isEquivB_iff _).2 hΦF))

#rt_check RoundTrip.V10_6.A_to_B [Polyfold.EpFunctor.proposition_10_1_6,
  Polyfold.MPolyfold.IsLocalScDiffeoAt.comp, Polyfold.MPolyfold.IsLocalScDiffeoAt.congr,
  Polyfold.MPolyfold.IsLocalScDiffeoAt.of_comp_left,
  Polyfold.MPolyfold.IsLocalScDiffeoAt.of_comp_right, Polyfold.EpFunctor.isLocalScDiffeoAt_mor,
  Polyfold.EpFunctor.isLocalScDiffeo_mor, Polyfold.EpFunctor.isLocalScDiffeoAt_obj_tgt]
#rt_check RoundTrip.V10_6.B_to_A [Polyfold.EpFunctor.proposition_10_1_6,
  Polyfold.MPolyfold.IsLocalScDiffeoAt.comp, Polyfold.MPolyfold.IsLocalScDiffeoAt.congr,
  Polyfold.MPolyfold.IsLocalScDiffeoAt.of_comp_left,
  Polyfold.MPolyfold.IsLocalScDiffeoAt.of_comp_right, Polyfold.EpFunctor.isLocalScDiffeoAt_mor,
  Polyfold.EpFunctor.isLocalScDiffeo_mor, Polyfold.EpFunctor.isLocalScDiffeoAt_obj_tgt]
#rt_overlap RoundTrip.V10_6.B_to_A [Polyfold.EpFunctor.proposition_10_1_6,
  Polyfold.MPolyfold.IsLocalScDiffeoAt.comp, Polyfold.MPolyfold.IsLocalScDiffeoAt.congr,
  Polyfold.MPolyfold.IsLocalScDiffeoAt.of_comp_left,
  Polyfold.MPolyfold.IsLocalScDiffeoAt.of_comp_right, Polyfold.EpFunctor.isLocalScDiffeoAt_mor,
  Polyfold.EpFunctor.isLocalScDiffeo_mor, Polyfold.EpFunctor.isLocalScDiffeoAt_obj_tgt]

end RoundTrip.V10_6
