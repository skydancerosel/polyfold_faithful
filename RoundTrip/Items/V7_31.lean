import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_31

/-! Round trip for V7_31 (p. 238: the morphisms `𝐀 = {φ | s φ, t φ ∈ A}` of a saturated
sub-M-polyfold `A` form a sub-M-polyfold of `𝐗`, via `𝐫 = (s|𝐔(φ))⁻¹ ∘ r ∘ s`).

`A` is the conjunction of the types of the listed theorems, at universe `0` (B lives in `Type`):
`src_mem_of_tgt_mem_of_isSaturated`, `morOn_eq_preimage_src`, `morOn_eq_preimage_tgt`,
`isSubMPolyfold_preimage_src`, `isSubMPolyfold_preimage_tgt` (for EVERY sub-M-polyfold `A`, no
saturation), `isSubMPolyfold_morOn`, `isScSmoothMap_val_subMor` (fact (1) for `𝐀`) and
`isScSmoothOn_retractInto_subMor` (fact (2) for `𝐀`), all in `Polyfold.EpGroupoid`.
`subMorPolyfold` is a definition (vocabulary).

`A → B` (not proved).  B = (a) the choice `s : 𝐔(φ) → U(a)` sc-diffeomorphism plus a retraction
`r` of `U(a)` onto `U(a) ∩ A` exists at every `φ ∈ 𝐀`; (b) for EVERY such choice `σ ∘ r ∘ s`
retracts `𝐔` onto `𝐔 ∩ 𝐀`; (c) `𝐀` is a sub-M-polyfold; (d) some structure `Q` on `𝐀` with the
facts (1)–(4).  Everything except the tangent-space facts (3), (4) of (d) is proved
(`A_to_B_noTangent`): (a) by the shrinking `U = (V ∩ V₀) ∩ r⁻¹(V ∩ V₀)` (re-done here, A has no
such statement), (b) by `comp_retract` with A's `morOn_eq_preimage_src` (hypothesis used),
(c) is A's `isSubMPolyfold_morOn`, (d) (1), (2) are A's facts for `Q = subMorPolyfold hA`.  The
tangent-space facts (3), (4) for `𝐀` are not in A: the project does not restate Part I's
chart-level `proposition_2_3_19_three/4` for `T_φ𝐗`, `T_φ𝐀` (gap G.7, see `SubGroupoid.lean`); the
missing glue is the same as for items V2_25/V7_30 (several hundred lines of tangent-map work),
believed true, not attempted.

`B → A` (proved; only partly from B).  `isSubMPolyfold_morOn` is B's (c).  The other conjuncts
are not consequences of B and are proved outright: the three saturation identities (elementary,
via `isSaturated_iff` and `ι`); the preimage lemmas `isSubMPolyfold_preimage_src/tgt`, which
hold for every sub-M-polyfold `A` while B only treats saturated `A` — re-proved here
(`isSubMPolyfold_preimage`, the same `g ∘ r ∘ f` construction used for (a), (b)); facts (1), (2)
for the specific `subMorPolyfold hA` from Part I's `subPolyfold_inclusion_isScSmooth`,
`subPolyfold_retraction_isScSmooth` (B only gives SOME `Q`).

Harness: the types of `isScSmoothMap_val_subMor`, `isScSmoothOn_retractInto_subMor` mention
`subMorPolyfold hA = subPolyfold (X.isSubMPolyfold_morOn hA)`, whose body passes the banned
`isSubMPolyfold_morOn` (and through it `morOn_eq_preimage_src`, `isSubMPolyfold_preimage_src`) as
a non-abstracted argument; so every term mentioning A fails `#rt_check` and `#rt_check_soft`.
As in V2_24, `A_to_B_noTangent = A'_to_B_noTangent ∘ A_to_A'` (`A'`: `Q` existential; `A_to_A'` a
projection) and `#rt_check` passes on `A'_to_B_noTangent`; `B_to_A` and `A_to_B_noTangent` pass the
traversal with the body of `subMorPolyfold` not unfolded (`#rt_check_except_defs`). -/

namespace RoundTrip.V7_31
open Polyfold Set
open scoped Polyfold.EpGroupoid

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.src_mem_of_tgt_mem_of_isSaturated.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.morOn_eq_preimage_src.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.morOn_eq_preimage_tgt.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isSubMPolyfold_preimage_src.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isSubMPolyfold_preimage_tgt.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isSubMPolyfold_morOn.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isScSmoothMap_val_subMor.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isScSmoothOn_retractInto_subMor.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.src_mem_of_tgt_mem_of_isSaturated.{0},
    @Polyfold.EpGroupoid.morOn_eq_preimage_src.{0},
    @Polyfold.EpGroupoid.morOn_eq_preimage_tgt.{0},
    @Polyfold.EpGroupoid.isSubMPolyfold_preimage_src.{0},
    @Polyfold.EpGroupoid.isSubMPolyfold_preimage_tgt.{0},
    @Polyfold.EpGroupoid.isSubMPolyfold_morOn.{0},
    @Polyfold.EpGroupoid.isScSmoothMap_val_subMor.{0},
    @Polyfold.EpGroupoid.isScSmoothOn_retractInto_subMor.{0}⟩

/-! ### The construction `g ∘ r ∘ f` -/

section Gen

variable {M O : Type} [TopologicalSpace M] [T2Space M] [ParacompactSpace M]
  [TopologicalSpace O] [T2Space O] [ParacompactSpace O] {PM : MPolyfold M} {PO : MPolyfold O}

/-- For an sc-diffeomorphism `f : W → U` with inverse `g` and a retraction `r` of `U` onto
`U ∩ A`, `g ∘ r ∘ f` is a retraction of `W` onto `W ∩ f⁻¹(A)`. -/
theorem comp_retract {f : M → O} {g : O → M} {W : Set M} {U : Set O} {r : O → O} {A : Set O}
    (hd : PM.IsScDiffeoOn PO f g W U) (hr : IsRetractOntoB PO r U A) :
    IsRetractOntoB PM (g ∘ r ∘ f) W (f ⁻¹' A) := by
  obtain ⟨hrU, hrs, hri, hrA⟩ := hr
  have hr_eq : ∀ y ∈ U ∩ A, r y = y := fun y hy => by
    rw [← hrA] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hri z hz
  have hr_mem : ∀ y ∈ U, r y ∈ A := fun y hy => by
    have h : r y ∈ r '' U := mem_image_of_mem r hy
    rw [hrA] at h
    exact h.2
  have hmaps : MapsTo (g ∘ r ∘ f) W W := fun y hy => hd.mapsTo_inv (hrU (hd.mapsTo hy))
  refine ⟨hmaps, ?_, fun y hy => ?_, ?_⟩
  · exact MPolyfold.IsScSmoothOn.comp hd.isScSmoothOn_inv
      (MPolyfold.IsScSmoothOn.comp hrs hd.isScSmoothOn hd.mapsTo) fun y hy => hrU (hd.mapsTo hy)
  · simp only [Function.comp_apply, hd.right_inv _ (hrU (hd.mapsTo hy)), hri _ (hd.mapsTo hy)]
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨hmaps hz, ?_⟩
      change f (g (r (f z))) ∈ A
      rw [hd.right_inv _ (hrU (hd.mapsTo hz))]
      exact hr_mem _ (hd.mapsTo hz)
    · rintro ⟨hy, hyA⟩
      refine ⟨y, hy, ?_⟩
      change g (r (f y)) = y
      rw [hr_eq _ ⟨hd.mapsTo hy, hyA⟩, hd.left_inv _ hy]

/-- **Shrinking** (the text's "possibly smaller `U(a)`"): from an sc-diffeomorphism `f : W → V`
at `x` and a retraction of `X` onto a sub-M-polyfold `A ∋ f x`, an sc-diffeomorphism
`f : W' → U` at `x` and a retraction `r : U → U` onto `U ∩ A`. -/
theorem exists_shrink {f : M → O} {g : O → M} {W : Set M} {V : Set O} {x : M} (hxW : x ∈ W)
    (hd : PM.IsScDiffeoOn PO f g W V) {A : Set O} (hA : PO.IsSubMPolyfold A) (hx : f x ∈ A) :
    ∃ (W' : Set M) (U : Set O) (r : O → O), x ∈ W' ∧ f x ∈ U ∧
      PM.IsScDiffeoOn PO f g W' U ∧ IsRetractOntoB PO r U A := by
  obtain ⟨V₀, hV₀, hfxV₀, r, -, hrs, hri, hrA⟩ := hA (f x) hx
  have hr_eq : ∀ y ∈ A ∩ V₀, r y = y := fun y hy => by
    rw [← hrA] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hri z hz
  have hr_mem : ∀ y ∈ V₀, r y ∈ A := fun y hy => by
    have h : r y ∈ r '' V₀ := mem_image_of_mem r hy
    rw [hrA] at h
    exact h.1
  have hVo : IsOpen V := hd.isScSmoothOn_inv.isOpen
  set U := (V ∩ V₀) ∩ r ⁻¹' (V ∩ V₀) with hU
  have hUo : IsOpen U := (hrs.continuousOn.mono inter_subset_right).isOpen_inter_preimage
    (hVo.inter hV₀) (hVo.inter hV₀)
  have hfx : f x ∈ U := ⟨⟨hd.mapsTo hxW, hfxV₀⟩, by
    rw [mem_preimage, hr_eq _ ⟨hx, hfxV₀⟩]; exact ⟨hd.mapsTo hxW, hfxV₀⟩⟩
  have hd' := (hd.symm.restrict hUo fun y hy => hy.1.1).symm
  refine ⟨W ∩ f ⁻¹' U, U, r, ⟨hxW, hfx⟩, hfx, hd', fun y hy => ⟨hy.2, ?_⟩,
    hrs.mono hUo fun y hy => hy.1.2, fun y hy => hri y hy.1.2, ?_⟩
  · rw [mem_preimage, hri _ hy.1.2]; exact hy.2
  · ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨hz.2, by rw [mem_preimage, hri _ hz.1.2]; exact hz.2⟩, hr_mem _ hz.1.2⟩
    · rintro ⟨hy, hyA⟩
      exact ⟨y, hy, hr_eq _ ⟨hyA, hy.1.2⟩⟩

/-- The preimage of a sub-M-polyfold under a local sc-diffeomorphism is a sub-M-polyfold. -/
theorem isSubMPolyfold_preimage {f : M → O} (hf : PM.IsLocalScDiffeo PO f) {A : Set O}
    (hA : PO.IsSubMPolyfold A) : PM.IsSubMPolyfold (f ⁻¹' A) := by
  intro x hx
  obtain ⟨W, V, g, hxW, hd⟩ := hf x
  obtain ⟨W', U, r, hxW', -, hd', hr⟩ := exists_shrink hxW hd hA hx
  obtain ⟨h1, h2, h3, h4⟩ := comp_retract hd' hr
  exact ⟨W', hd'.isScSmoothOn.isOpen, hxW', g ∘ r ∘ f, h1, h2, h3, by rw [h4, inter_comm]⟩

/-- B's (2) from the project's fact (2) (`retractInto a₀`), for every `g` agreeing with `r`. -/
theorem fact2_of {S : Set M} [ParacompactSpace S] {Q : MPolyfold S}
    (h : ∀ (d : PM.SubData S) (a₀ : S), PM.IsScSmoothOn Q (d.retractInto a₀) d.V)
    (V : Set M) (r : M → M) (hV : IsOpen V) (hrV : MapsTo r V V) (hsm : PM.IsScSmoothOn PM r V)
    (hid : ∀ x ∈ V, r (r x) = r x) (him : r '' V = S ∩ V) (g : M → S)
    (hg : ∀ x ∈ V, (g x : M) = r x) : PM.IsScSmoothOn Q g V := by
  let d : PM.SubData S := ⟨V, r, hV, hrV, hsm, hid, him⟩
  rcases V.eq_empty_or_nonempty with hV0 | ⟨x₀, _⟩
  · subst hV0
    exact MPolyfold.IsScSmoothOn.of_exists_charts isOpen_empty (continuousOn_empty _)
      fun x hx => absurd hx (notMem_empty x)
  · refine (h d (g x₀)).congr fun x hx => Subtype.ext ?_
    rw [MPolyfold.SubData.retractInto_val d (g x₀) hx, hg x hx]

end Gen

/-! ### `A → B` without the tangent-space facts -/

/-- B without the tangent-space facts (3), (4) of (d). -/
def B_noTangent : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (A : Set Obj), X.PObj.IsSubMPolyfold A → X.IsSaturated A →
    (∀ φ ∈ X.morOn A, ∃ (W : Set Mor) (U : Set Obj) (σ : Obj → Mor) (r : Obj → Obj),
      φ ∈ W ∧ X.src φ ∈ U ∧ X.PMor.IsScDiffeoOn X.PObj X.src σ W U ∧
      IsRetractOntoB X.PObj r U A) ∧
    (∀ (W : Set Mor) (U : Set Obj) (σ : Obj → Mor) (r : Obj → Obj),
      X.PMor.IsScDiffeoOn X.PObj X.src σ W U → IsRetractOntoB X.PObj r U A →
      IsRetractOntoB X.PMor (σ ∘ r ∘ X.src) W (X.morOn A)) ∧
    X.PMor.IsSubMPolyfold (X.morOn A) ∧
    (∃ (_ : ParacompactSpace (X.morOn A)) (Q : MPolyfold (X.morOn A)),
      (Q.IsScSmoothMap X.PMor (Subtype.val : X.morOn A → Mor) ∧
        Topology.IsEmbedding (Subtype.val : X.morOn A → Mor)) ∧
      (∀ (V : Set Mor) (r : Mor → Mor), IsOpen V → Set.MapsTo r V V →
        X.PMor.IsScSmoothOn X.PMor r V → (∀ x ∈ V, r (r x) = r x) → r '' V = X.morOn A ∩ V →
        ∀ g : Mor → X.morOn A, (∀ x ∈ V, (g x : Mor) = r x) → X.PMor.IsScSmoothOn Q g V))

/-- `B_noTangent` is a weakening of B. -/
theorem B_to_B_noTangent : B → B_noTangent := by
  intro hB Obj Mor _ _ _ _ _ _ X S hS hsat
  obtain ⟨ha, hb, hc, hp, Q, h1, h2, -⟩ := hB Obj Mor X S hS hsat
  exact ⟨ha, hb, hc, hp, Q, h1, h2⟩

/-- A with the structure `Q` on `𝐀` existentially quantified (keeps `subMorPolyfold` out of the
checked proof, see the harness note). -/
def A' : Prop :=
  (type_of% @Polyfold.EpGroupoid.morOn_eq_preimage_src.{0}) ∧
    (type_of% @Polyfold.EpGroupoid.isSubMPolyfold_morOn.{0}) ∧
    ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (S : Set Obj), X.IsEpSubgroupoid S →
      ∃ (_ : ParacompactSpace (X.morOn S)) (Q : MPolyfold (X.morOn S)),
        (Q.IsScSmoothMap X.PMor Subtype.val ∧ Topology.IsEmbedding (Subtype.val : X.morOn S → Mor)) ∧
        ∀ (d : X.PMor.SubData (X.morOn S)) (a₀ : X.morOn S),
          X.PMor.IsScSmoothOn Q (d.retractInto a₀) d.V

theorem A_to_A' : A → A' := by
  rintro ⟨-, h2, -, -, -, h6, h7, h8⟩
  exact ⟨h2, h6, fun Obj Mor _ _ _ _ _ _ X S hS =>
    ⟨inferInstance, EpGroupoid.subMorPolyfold hS, h7 hS, h8 hS⟩⟩

theorem A'_to_B_noTangent : A' → B_noTangent := by
  rintro ⟨h2, h6, h78⟩ Obj Mor _ _ _ _ _ _ X S hS hsat
  have hA : X.IsEpSubgroupoid S := ⟨hS, hsat⟩
  refine ⟨fun φ hφ => ?_, fun W U σ r hd hr => ?_, h6 X hA, ?_⟩
  · obtain ⟨W, V, σ, hφW, hd⟩ := X.isLocalScDiffeo_src φ
    obtain ⟨W', U, r, h1, h2, h3, h4⟩ := exists_shrink hφW hd hS hφ.1
    exact ⟨W', U, σ, r, h1, h2, h3, h4⟩
  · rw [h2 X hsat]
    exact comp_retract hd hr
  · obtain ⟨hp, Q, h7, h8⟩ := h78 Obj Mor X S hA
    exact ⟨hp, Q, h7, fact2_of h8⟩

theorem A_to_B_noTangent : A → B_noTangent := fun h => A'_to_B_noTangent (A_to_A' h)

/-! ### `B → A` -/

theorem B_to_A : B → A := by
  intro hB
  have hsrc : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
      (S : Set Obj), X.IsSaturated S → ∀ φ : Mor, X.tgt φ ∈ S → X.src φ ∈ S := by
    intro Obj Mor _ _ _ _ _ _ X S hS φ h
    have h' := X.isSaturated_iff.1 hS (X.inv φ) (by rw [X.src_inv]; exact h)
    rwa [X.tgt_inv] at h'
  refine ⟨fun hS _ h => hsrc _ _ _ _ hS _ h, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X S hS
    exact ext fun φ => ⟨fun h => h.1, fun h => ⟨h, X.isSaturated_iff.1 hS φ h⟩⟩
  · intro Obj Mor _ _ _ _ _ _ X S hS
    exact ext fun φ => ⟨fun h => h.2, fun h => ⟨hsrc _ _ X S hS φ h, h⟩⟩
  · intro Obj Mor _ _ _ _ _ _ X S hS
    exact isSubMPolyfold_preimage X.isLocalScDiffeo_src hS
  · intro Obj Mor _ _ _ _ _ _ X S hS
    exact isSubMPolyfold_preimage X.isLocalScDiffeo_tgt hS
  · intro Obj Mor _ _ _ _ _ _ X S hS
    exact (hB Obj Mor X S hS.isSubMPolyfold hS.isSaturated).2.2.1
  · -- the sub-M-polyfold proof is B's (c), not the banned `isSubMPolyfold_morOn`
    intro Obj Mor _ _ _ _ _ _ X S hS
    exact ⟨MPolyfold.subPolyfold_inclusion_isScSmooth
      (hB Obj Mor X S hS.isSubMPolyfold hS.isSaturated).2.2.1, Topology.IsEmbedding.subtypeVal⟩
  · intro Obj Mor _ _ _ _ _ _ X S hS d a₀
    exact MPolyfold.subPolyfold_retraction_isScSmooth
      (hB Obj Mor X S hS.isSubMPolyfold hS.isSaturated).2.2.1 d a₀

open Lean Elab Command in
/-- `#rt_check_except_defs T [d₁, …] [n₁, …]`: the harness traversal `rtCollect` with the bodies of
the definitions `dᵢ` not unfolded; fails if the proof of `T` reaches some `nᵢ` elsewhere. -/
elab "#rt_check_except_defs " t:ident " [" ds:ident,* "]" " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let seen := ds.getElems.foldl (fun s d => s.insert d.getId) NameSet.empty
  let used := rtCollect env roots.toList seen
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do throwError "FAIL: {t.getId} uses {bad} outside the bodies of the definitions"
  logInfo m!"OK: {t.getId} reaches the banned declarations only through the bodies of the definitions {ds.getElems.toList.map (·.getId)}"

#rt_check RoundTrip.V7_31.A'_to_B_noTangent [Polyfold.EpGroupoid.src_mem_of_tgt_mem_of_isSaturated,
  Polyfold.EpGroupoid.morOn_eq_preimage_src, Polyfold.EpGroupoid.morOn_eq_preimage_tgt,
  Polyfold.EpGroupoid.isSubMPolyfold_preimage_src, Polyfold.EpGroupoid.isSubMPolyfold_preimage_tgt,
  Polyfold.EpGroupoid.isSubMPolyfold_morOn, Polyfold.EpGroupoid.isScSmoothMap_val_subMor,
  Polyfold.EpGroupoid.isScSmoothOn_retractInto_subMor]
#rt_check_except_defs RoundTrip.V7_31.A_to_B_noTangent [Polyfold.EpGroupoid.subMorPolyfold]
  [Polyfold.EpGroupoid.src_mem_of_tgt_mem_of_isSaturated,
  Polyfold.EpGroupoid.morOn_eq_preimage_src, Polyfold.EpGroupoid.morOn_eq_preimage_tgt,
  Polyfold.EpGroupoid.isSubMPolyfold_preimage_src, Polyfold.EpGroupoid.isSubMPolyfold_preimage_tgt,
  Polyfold.EpGroupoid.isSubMPolyfold_morOn, Polyfold.EpGroupoid.isScSmoothMap_val_subMor,
  Polyfold.EpGroupoid.isScSmoothOn_retractInto_subMor]
#rt_check_except_defs RoundTrip.V7_31.B_to_A [Polyfold.EpGroupoid.subMorPolyfold]
  [Polyfold.EpGroupoid.src_mem_of_tgt_mem_of_isSaturated,
  Polyfold.EpGroupoid.morOn_eq_preimage_src, Polyfold.EpGroupoid.morOn_eq_preimage_tgt,
  Polyfold.EpGroupoid.isSubMPolyfold_preimage_src, Polyfold.EpGroupoid.isSubMPolyfold_preimage_tgt,
  Polyfold.EpGroupoid.isSubMPolyfold_morOn, Polyfold.EpGroupoid.isScSmoothMap_val_subMor,
  Polyfold.EpGroupoid.isScSmoothOn_retractInto_subMor]
/-- error: rt_check FAIL: RoundTrip.V7_31.B_to_A uses [Polyfold.EpGroupoid.morOn_eq_preimage_src,
 Polyfold.EpGroupoid.isSubMPolyfold_preimage_src,
 Polyfold.EpGroupoid.isSubMPolyfold_morOn] -/
#guard_msgs in
#rt_check RoundTrip.V7_31.B_to_A [Polyfold.EpGroupoid.src_mem_of_tgt_mem_of_isSaturated,
  Polyfold.EpGroupoid.morOn_eq_preimage_src, Polyfold.EpGroupoid.morOn_eq_preimage_tgt,
  Polyfold.EpGroupoid.isSubMPolyfold_preimage_src, Polyfold.EpGroupoid.isSubMPolyfold_preimage_tgt,
  Polyfold.EpGroupoid.isSubMPolyfold_morOn, Polyfold.EpGroupoid.isScSmoothMap_val_subMor,
  Polyfold.EpGroupoid.isScSmoothOn_retractInto_subMor]
#rt_overlap RoundTrip.V7_31.B_to_A [Polyfold.EpGroupoid.src_mem_of_tgt_mem_of_isSaturated,
  Polyfold.EpGroupoid.morOn_eq_preimage_src, Polyfold.EpGroupoid.morOn_eq_preimage_tgt,
  Polyfold.EpGroupoid.isSubMPolyfold_preimage_src, Polyfold.EpGroupoid.isSubMPolyfold_preimage_tgt,
  Polyfold.EpGroupoid.isSubMPolyfold_morOn, Polyfold.EpGroupoid.isScSmoothMap_val_subMor,
  Polyfold.EpGroupoid.isScSmoothOn_retractInto_subMor]

end RoundTrip.V7_31
