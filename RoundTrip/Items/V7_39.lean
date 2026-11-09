import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_39

/-! Round trip for V7_39 (Proposition 7.9, p. 242: the M-polyfold structure of `𝐗^R`).

`A` is the conjunction of the types of the eleven listed theorems, universes at `0`:
`isQuotientMap_reducedπ`, `isOpenMap_reducedπ`, `injOn_reducedπ`, `reducedChart_compatible`,
`isChart_reducedChart`, `isScDiffeoOn_reducedπ`, `isLocalScDiffeo_reducedπ`, `proposition_7_2_10`,
`t2Space_reducedMor_of_isEffective`, `paracompactSpace_reducedMor_of_isEffective`,
`paracompactSpace_reducedMor_of_t3`.  The definitions `reducedπ`, `reducedChart`,
`reducedCharts`, `reducedAtlas`, `reducedPolyfold` are vocabulary.  `reducedPolyfold` and the
theorems about it take `[T2Space X.ReducedMor] [ParacompactSpace X.ReducedMor]` as hypotheses.

Dictionary: `B`'s `NatRepB`/`TxB`/`RelB` are the project's `NaturalRep`/`trivialSet`/`ReducedRel`
(`relB_eq : RelB X = X.ReducedRel`), so `B`'s `XRB X = Quot (RelB X)` with the quotient topology
*is* `X.ReducedMor` after rewriting the relation (`rintro r rfl` transports every statement).
`B`'s `IsSrcSheetB X W` is literally the project's sheet hypothesis `IsScDiffeoOn src σ W V`.

* `A → B`: **not proved; a genuine difference.**  `B`'s last conjunct asserts, for *every*
  ep-groupoid, that `𝐗^R` is Hausdorff and paracompact (and then carries an M-polyfold structure
  making each `Ψ` an sc-diffeomorphism).  `A` has these only for effective `X`
  (`t2Space_reducedMor_of_isEffective`, …) or as instance hypotheses of `reducedPolyfold`.  The
  blind formalizer believes the Hausdorff claim fails (a dimension-jumping retract with a `ℤ/2`
  action that is trivial on one side only), and the project's own notes say the same; we did not
  attempt `¬ B`.  The other two conjuncts of `B` follow from `A`; `body_of_A` (`π(W)` open and `π|W` a
  homeomorphism from `isOpenMap_reducedπ` and `injOn_reducedπ`; the transitions are `σ₁ ∘ s` on an
  open set), and so does the third once `𝐗^R` is Hausdorff and paracompact (`Q = reducedPolyfold`,
  from `isScDiffeoOn_reducedπ`).  `A_and_t2_to_B`: `A` together with "`𝐗^R` is Hausdorff and
  paracompact for every `X`" gives `B` (checked with `#rt_check_soft`, using `A`).
* `B → A`: proved.  From `B`: `isOpenMap_reducedπ` (cover by restricted sheets, `B`(1)),
  `injOn_reducedπ` (`B`(1)), `reducedChart_compatible` (the sc-smoothness of `σ₂ ∘ s` on the
  overlap is `B`(2); the rest copies the project's private `reducedChart_transition`), and the
  three Hausdorff/paracompact conjuncts (`B`(3), which gives them without effectiveness).
  `isQuotientMap_reducedπ` is Mathlib; `isChart_reducedChart`, `isScDiffeoOn_reducedπ`,
  `isLocalScDiffeo_reducedπ`, `proposition_7_2_10` concern the project's specific atlas (not `B`'s
  `Q`) and are re-proved by copying the project's proofs, with `isOpenMap_reducedπ` replaced by
  the `B`-derived one.

`#rt_check_soft` is used: the statements mention `reducedChart` (proof field `isOpen_source` uses
the banned `isOpenMap_reducedπ`) and `reducedPolyfold` (its atlas's `compatible` uses the banned
`reducedChart_compatible`).
-/

namespace RoundTrip.V7_39
open Polyfold Set Filter Topology Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.isQuotientMap_reducedπ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isOpenMap_reducedπ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.injOn_reducedπ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.reducedChart_compatible.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isChart_reducedChart.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScDiffeoOn_reducedπ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_reducedπ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.proposition_7_2_10.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.t2Space_reducedMor_of_isEffective.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.paracompactSpace_reducedMor_of_isEffective.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.paracompactSpace_reducedMor_of_t3.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.isQuotientMap_reducedπ.{0}, @Polyfold.EpGroupoid.isOpenMap_reducedπ.{0},
    @Polyfold.EpGroupoid.injOn_reducedπ.{0}, @Polyfold.EpGroupoid.reducedChart_compatible.{0},
    @Polyfold.EpGroupoid.isChart_reducedChart.{0}, @Polyfold.EpGroupoid.isScDiffeoOn_reducedπ.{0},
    @Polyfold.EpGroupoid.isLocalScDiffeo_reducedπ.{0}, @Polyfold.EpGroupoid.proposition_7_2_10.{0},
    @Polyfold.EpGroupoid.t2Space_reducedMor_of_isEffective.{0},
    @Polyfold.EpGroupoid.paracompactSpace_reducedMor_of_isEffective.{0},
    @Polyfold.EpGroupoid.paracompactSpace_reducedMor_of_t3.{0}⟩

section Dictionary
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor} {x : Obj}

/-- The project's natural representation as `B`'s. -/
def toB (R : X.NaturalRep x) : NatRepB X x where
  U := R.U
  isOpen_U := R.isOpen_U
  isConnected_U := R.isConnected_U
  mem_U := R.mem_U
  Φ := R.Φ
  Γ := R.Γ
  diffeo g := ⟨_, R.isScDiffeoOn_Φ g⟩
  hom := R.Φ_mul
  smooth := R.isScSmoothOn_Γ
  Γ_x := R.Γ_self
  src_Γ := R.src_Γ
  tgt_Γ := R.tgt_Γ
  unique := R.existsUnique_Γ

theorem NatRepB.Φ_one (R : NatRepB X x) : ∀ y ∈ R.U, R.Φ 1 y = y := by
  intro y hy
  obtain ⟨ψ, hψ⟩ := R.diffeo 1
  have h := R.hom 1 1 y hy
  rw [mul_one] at h
  have := congrArg ψ h
  rw [hψ.left_inv _ hy, hψ.left_inv _ (hψ.mapsTo hy)] at this
  exact this.symm

/-- `B`'s natural representation as the project's. -/
def ofB (R : NatRepB X x) : X.NaturalRep x where
  U := R.U
  isOpen_U := R.isOpen_U
  isConnected_U := R.isConnected_U
  mem_U := R.mem_U
  Φ := R.Φ
  Γ := R.Γ
  isScDiffeoOn_Φ g := by
    obtain ⟨ψ, hψ⟩ := R.diffeo g
    obtain ⟨ψ', hψ'⟩ := R.diffeo g⁻¹
    exact ⟨hψ.isScSmoothOn, hψ'.isScSmoothOn, hψ.mapsTo, hψ'.mapsTo,
      fun y hy => by rw [← R.hom _ _ y hy, inv_mul_cancel, R.Φ_one y hy],
      fun y hy => by rw [← R.hom _ _ y hy, mul_inv_cancel, R.Φ_one y hy]⟩
  Φ_mul := R.hom
  isScSmoothOn_Γ := R.smooth
  Γ_self := R.Γ_x
  src_Γ := R.src_Γ
  tgt_Γ := R.tgt_Γ
  existsUnique_Γ := R.unique

theorem TxB_eq (x : Obj) : TxB X x = X.trivialSet x := by
  ext g
  exact ⟨fun ⟨R, h⟩ => ⟨ofB R, h⟩, fun ⟨R, h⟩ => ⟨toB R, h⟩⟩

theorem relB_iff {φ φ' : Mor} : RelB X φ φ' ↔ X.ReducedRel φ φ' := by
  refine ⟨fun ⟨h1, g, hg, he⟩ => ⟨h1, g, ?_, he⟩, fun ⟨h1, g, hg, he⟩ => ⟨h1, g, ?_, he⟩⟩
  · rw [← TxB_eq]; exact hg
  · rw [TxB_eq]; exact hg

theorem relB_eq : RelB X = X.ReducedRel := funext fun _ => funext fun _ => propext relB_iff

end Dictionary

/-! ### What `A` gives of `B`: everything except the Hausdorff/paracompact claim -/

section FromA
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- `B`'s body for `X`, with `RelB X` generalized to any `r = ReducedRel`, from `A`; the third
conjunct under the hypotheses that `Quot r` is Hausdorff and paracompact. -/
theorem body_of_A (hA : A) : ∀ r : Mor → Mor → Prop, r = X.ReducedRel →
    (∀ W : Set Mor, IsSrcSheetB X W → IsOpen (Quot.mk r '' W) ∧
      ∃ e : W ≃ₜ (Quot.mk r '' W), ∀ φ : W, (e φ : Quot r) = Quot.mk r φ) ∧
    (∀ W₀ W₁ : Set Mor, IsSrcSheetB X W₀ → IsSrcSheetB X W₁ → ∀ τ : Mor → Mor,
      (∀ φ ∈ W₀ ∩ Quot.mk r ⁻¹' (Quot.mk r '' W₁), τ φ ∈ W₁ ∧ Quot.mk r (τ φ) = Quot.mk r φ) →
      X.PMor.IsScSmoothOn X.PMor τ (W₀ ∩ Quot.mk r ⁻¹' (Quot.mk r '' W₁))) ∧
    (∀ [T2Space (Quot r)] [ParacompactSpace (Quot r)], ∃ Q : MPolyfold (Quot r),
      ∀ W : Set Mor, IsSrcSheetB X W →
        ∃ g : Quot r → Mor, X.PMor.IsScDiffeoOn Q (Quot.mk r) g W (Quot.mk r '' W)) := by
  rintro r rfl
  obtain ⟨-, hopen, hinjA, -, -, hdiff, -⟩ := hA
  refine ⟨fun W ⟨σ, V, hS⟩ => ?_, fun W₀ W₁ ⟨σ₀, V₀, hS₀⟩ ⟨σ₁, V₁, hS₁⟩ τ hτ => ?_, ?_⟩
  · have hemb : IsOpenEmbedding (W.domRestrict X.reducedπ) :=
      .of_continuous_injective_isOpenMap (X.continuous_reducedπ.comp continuous_subtype_val)
        (injOn_iff_injective.1 (hinjA hS)) ((hopen X).domRestrict hS.isScSmoothOn.isOpen)
    exact ⟨hopen X _ hS.isScSmoothOn.isOpen,
      hemb.isEmbedding.toHomeomorph.trans (Homeomorph.setCongr (range_domRestrict _ _)),
      fun φ => rfl⟩
  · have hD : IsOpen (W₀ ∩ X.reducedπ ⁻¹' (X.reducedπ '' W₁)) :=
      hS₀.isScSmoothOn.isOpen.inter
        ((hopen X _ hS₁.isScSmoothOn.isOpen).preimage X.continuous_reducedπ)
    have hf : X.PMor.IsScSmoothOn X.PMor (fun φ => σ₁ (X.src φ)) (X.src ⁻¹' V₁) :=
      MPolyfold.IsScSmoothOn.comp hS₁.isScSmoothOn_inv
        (X.isScSmoothMap_src.mono (hS₁.isScSmoothOn_inv.isOpen.preimage X.continuous_src)
          (subset_univ _)) fun _ hφ => hφ
    have hτs : ∀ φ ∈ W₀ ∩ X.reducedπ ⁻¹' (X.reducedπ '' W₁), X.src (τ φ) = X.src φ :=
      fun φ hφ => EpGroupoid.ReducedRel.src_eq (X.reducedπ_eq_iff.1 (hτ φ hφ).2)
    refine (hf.mono hD fun φ hφ => ?_).congr fun φ hφ => ?_
    · rw [mem_preimage, ← hτs φ hφ]
      exact hS₁.mapsTo (hτ φ hφ).1
    · show σ₁ (X.src φ) = τ φ
      rw [← hτs φ hφ, hS₁.left_inv _ (hτ φ hφ).1]
  · intro i1 i2
    have : T2Space X.ReducedMor := i1
    have : ParacompactSpace X.ReducedMor := i2
    exact ⟨X.reducedPolyfold, fun W ⟨σ, V, hS⟩ => ⟨_, hdiff hS⟩⟩

end FromA

/-- **`A` plus "`𝐗^R` is Hausdorff and paracompact for every `X`" gives `B`**: the Hausdorff and
paracompact claim is the only part of `B` that `A` lacks. -/
theorem A_and_t2_to_B (hA : A)
    (ht : ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
      T2Space (XRB X) ∧ ParacompactSpace (XRB X)) : B := by
  intro Obj Mor _ _ _ _ _ _ X
  obtain ⟨i1, i2⟩ := ht Obj Mor X
  obtain ⟨h1, h2, h3⟩ := body_of_A X hA _ relB_eq
  exact ⟨h1, h2, i1, i2, @h3 i1 i2⟩

/-! ### `B`'s three conjuncts, transported to the project's `𝐗^R` -/

section FromB
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- `B`(1): on a sheet `W`, `π(W)` is open and `π` is injective on `W`. -/
theorem sheet_of_B (hB : B) {σ : Obj → Mor} {W : Set Mor} {V : Set Obj}
    (hS : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) :
    IsOpen (X.reducedπ '' W) ∧ InjOn X.reducedπ W := by
  obtain ⟨h1, -, -⟩ := hB Obj Mor X
  obtain ⟨ho, e, he⟩ := h1 W ⟨σ, V, hS⟩
  have hinj : InjOn (πB X) W := fun φ hφ φ' hφ' hπ => by
    have : e ⟨φ, hφ⟩ = e ⟨φ', hφ'⟩ := Subtype.ext (by rw [he, he]; exact hπ)
    exact congrArg Subtype.val (e.injective this)
  have key : ∀ r : Mor → Mor → Prop, r = X.ReducedRel →
      IsOpen (Quot.mk r '' W) ∧ InjOn (Quot.mk r) W →
      IsOpen (X.reducedπ '' W) ∧ InjOn X.reducedπ W := by
    rintro r rfl h
    exact h
  exact key _ relB_eq ⟨ho, hinj⟩

/-- `B`(2): the transitions are sc-smooth. -/
theorem trans_of_B (hB : B) {σ₀ σ₁ : Obj → Mor} {W₀ W₁ : Set Mor} {V₀ V₁ : Set Obj}
    (hS₀ : X.PMor.IsScDiffeoOn X.PObj X.src σ₀ W₀ V₀)
    (hS₁ : X.PMor.IsScDiffeoOn X.PObj X.src σ₁ W₁ V₁) {τ : Mor → Mor}
    (hτ : ∀ φ ∈ W₀ ∩ X.reducedπ ⁻¹' (X.reducedπ '' W₁),
      τ φ ∈ W₁ ∧ X.reducedπ (τ φ) = X.reducedπ φ) :
    X.PMor.IsScSmoothOn X.PMor τ (W₀ ∩ X.reducedπ ⁻¹' (X.reducedπ '' W₁)) := by
  obtain ⟨-, h2, -⟩ := hB Obj Mor X
  have key : ∀ r : Mor → Mor → Prop, r = X.ReducedRel →
      ((∀ φ ∈ W₀ ∩ Quot.mk r ⁻¹' (Quot.mk r '' W₁), τ φ ∈ W₁ ∧ Quot.mk r (τ φ) = Quot.mk r φ) →
        X.PMor.IsScSmoothOn X.PMor τ (W₀ ∩ Quot.mk r ⁻¹' (Quot.mk r '' W₁))) →
      X.PMor.IsScSmoothOn X.PMor τ (W₀ ∩ X.reducedπ ⁻¹' (X.reducedπ '' W₁)) := by
    rintro r rfl h
    exact h hτ
  exact key _ relB_eq (h2 W₀ W₁ ⟨σ₀, V₀, hS₀⟩ ⟨σ₁, V₁, hS₁⟩ τ)

/-- `B`(3): `𝐗^R` is Hausdorff and paracompact (for every `X`). -/
theorem t2_para_of_B (hB : B) : T2Space X.ReducedMor ∧ ParacompactSpace X.ReducedMor := by
  obtain ⟨-, -, i1, i2, -⟩ := hB Obj Mor X
  have key : ∀ r : Mor → Mor → Prop, r = X.ReducedRel → T2Space (Quot r) →
      ParacompactSpace (Quot r) → T2Space X.ReducedMor ∧ ParacompactSpace X.ReducedMor := by
    rintro r rfl h1 h2
    exact ⟨h1, h2⟩
  exact key _ relB_eq i1 i2

/-- `π` is open, from `B`(1) on restricted sheets. -/
theorem isOpenMap_of_B (hB : B) : IsOpenMap X.reducedπ := by
  intro O hO
  refine isOpen_iff_forall_mem_open.2 ?_
  rintro _ ⟨φ, hφO, rfl⟩
  obtain ⟨W, V, σ, hφW, hS⟩ := X.isLocalScDiffeo_src φ
  have hS' := hS.restrict (hS.isScSmoothOn.isOpen.inter hO) inter_subset_left
  exact ⟨X.reducedπ '' (W ∩ O), image_mono inter_subset_right, (sheet_of_B X hB hS').1,
    ⟨φ, ⟨hφW, hφO⟩, rfl⟩⟩

variable {X}

/-- The transition of two charts `Ψ`, with the sc-smoothness of `σ₂ ∘ s` from `B`(2) (the rest
copies the project's private `reducedChart_transition`). -/
theorem reducedChart_transition' (hB : B) {σ₁ σ₂ : Obj → Mor} {W₁ W₂ : Set Mor}
    {V₁ V₂ : Set Obj} {ψ₁ ψ₂ : MChart Mor} (hψ₁ : X.PMor.IsChart ψ₁) (hψ₂ : X.PMor.IsChart ψ₂)
    (hS₁ : X.PMor.IsScDiffeoOn X.PObj X.src σ₁ W₁ V₁) (h₁ : ψ₁.source ⊆ W₁)
    (hS₂ : X.PMor.IsScDiffeoOn X.PObj X.src σ₂ W₂ V₂) (h₂ : ψ₂.source ⊆ W₂) :
    IsScSmoothRetractMap ψ₁.model.E ψ₁.model.C
      ((X.reducedChart ψ₁ hS₁ h₁).overlap (X.reducedChart ψ₂ hS₂ h₂)) ψ₂.model.E ψ₂.model.C
      ((X.reducedChart ψ₂ hS₂ h₂).overlap (X.reducedChart ψ₁ hS₁ h₁))
      ((X.reducedChart ψ₁ hS₁ h₁).transition (X.reducedChart ψ₂ hS₂ h₂)) := by
  have hD : IsOpen (ψ₁.source ∩ X.reducedπ ⁻¹' (X.reducedπ '' ψ₂.source)) :=
    ψ₁.isOpen_source.inter ((isOpenMap_of_B X hB _ ψ₂.isOpen_source).preimage
      X.continuous_reducedπ)
  have hf : X.PMor.IsScSmoothOn X.PMor (fun φ => σ₂ (X.src φ))
      (W₁ ∩ X.reducedπ ⁻¹' (X.reducedπ '' W₂)) := by
    refine trans_of_B X hB hS₁ hS₂ fun φ hφ => ?_
    obtain ⟨φ', hφ', he⟩ := hφ.2
    have hs : X.src φ' = X.src φ := EpGroupoid.ReducedRel.src_eq (X.reducedπ_eq_iff.1 he)
    show σ₂ (X.src φ) ∈ W₂ ∧ X.reducedπ (σ₂ (X.src φ)) = X.reducedπ φ
    rw [← hs, hS₂.left_inv _ hφ']
    exact ⟨hφ', he⟩
  have hsub : ψ₁.source ∩ X.reducedπ ⁻¹' (X.reducedπ '' ψ₂.source) ⊆
      (W₁ ∩ X.reducedπ ⁻¹' (X.reducedπ '' W₂)) ∩ ψ₁.source := fun φ hφ =>
    ⟨⟨h₁ hφ.1, image_mono h₂ hφ.2⟩, hφ.1⟩
  have hmaps : MapsTo (fun φ => σ₂ (X.src φ))
      (ψ₁.source ∩ X.reducedπ ⁻¹' (X.reducedπ '' ψ₂.source)) ψ₂.source := fun φ hφ => by
    obtain ⟨φ', hφ', he⟩ := hφ.2
    change σ₂ (X.src φ) ∈ ψ₂.source
    rw [← EpGroupoid.ReducedRel.src_eq (X.reducedπ_eq_iff.1 he), hS₂.left_inv _ (h₂ hφ')]
    exact hφ'
  have key := hf.smooth ψ₁ ψ₂ hψ₁ hψ₂ _ hD hsub hmaps
  have hmt := (X.reducedChart ψ₁ hS₁ h₁).transition_mapsTo (X.reducedChart ψ₂ hS₂ h₂)
  rw [X.overlap_reducedChart hS₁ h₁ hS₂ h₂] at hmt ⊢
  exact key.mono_target hmt

end FromB

/-! ### The conjuncts of `A` from `B` -/

theorem isQuotientMap' : type_of% @Polyfold.EpGroupoid.isQuotientMap_reducedπ.{0} := by
  intro Obj Mor _ _ _ _ _ _ X
  exact isQuotientMap_quot_mk

theorem isOpenMap' (hB : B) : type_of% @Polyfold.EpGroupoid.isOpenMap_reducedπ.{0} := by
  intro Obj Mor _ _ _ _ _ _ X
  exact isOpenMap_of_B X hB

theorem injOn' (hB : B) : type_of% @Polyfold.EpGroupoid.injOn_reducedπ.{0} := by
  intro Obj Mor _ _ _ _ _ _ X σ W V hS
  exact (sheet_of_B X hB hS).2

theorem reducedChart_compatible' (hB : B) :
    type_of% @Polyfold.EpGroupoid.reducedChart_compatible.{0} := by
  intro Obj Mor _ _ _ _ _ _ X σ₁ σ₂ W₁ W₂ V₁ V₂ ψ₁ ψ₂ hψ₁ hψ₂ hS₁ h₁ hS₂ h₂
  exact ⟨reducedChart_transition' hB hψ₁ hψ₂ hS₁ h₁ hS₂ h₂,
    reducedChart_transition' hB hψ₂ hψ₁ hS₂ h₂ hS₁ h₁⟩

/-- Outright: the charts `Ψ` belong to the project's atlas by definition. -/
theorem isChart_reducedChart' : type_of% @Polyfold.EpGroupoid.isChart_reducedChart.{0} := by
  intro Obj Mor _ _ _ _ _ _ X σ W V _ _ ψ hψ hS hψW
  exact X.reducedPolyfold.isChart_of_mem ⟨ψ, σ, W, V, hS, hψW, hψ, rfl⟩

/-- Copy of the project's proof (about the project's atlas, not `B`'s `Q`), with the `B`-derived
openness of `π`. -/
theorem isScDiffeoOn_reducedπ' (hB : B) :
    type_of% @Polyfold.EpGroupoid.isScDiffeoOn_reducedπ.{0} := by
  intro Obj Mor _ _ _ _ _ _ X σ W V _ _ hS
  exact {
    isScSmoothOn := by
      refine MPolyfold.IsScSmoothOn.of_exists_charts hS.isScSmoothOn.isOpen
        X.continuous_reducedπ.continuousOn fun φ hφ => ?_
      obtain ⟨ψ, hψ, hφψ⟩ := X.PMor.exists_isChart_mem_source φ
      have ho : IsOpen (ψ.source ∩ W) := ψ.isOpen_source.inter hS.isScSmoothOn.isOpen
      let ψ' := ψ.restrict inter_subset_left ho
      have hψ' : X.PMor.IsChart ψ' := MPolyfold.IsChart.restrict _ hψ _ _
      refine ⟨ψ', X.reducedChart ψ' hS inter_subset_right, ψ'.source, hψ',
        isChart_reducedChart' hψ' hS inter_subset_right, ho, ⟨hφψ, hφ⟩, fun x hx => ⟨hx.2, hx⟩,
        fun x hx => ⟨x, hx, rfl⟩, ?_⟩
      rw [ψ'.image_source]
      refine (isScSmoothRetractMap_id _).congr fun z hz => ?_
      change z = ψ' (σ (X.src (ψ'.symm z)))
      rw [hS.left_inv _ (inter_subset_right (ψ'.symm_mapsTo hz)), ψ'.apply_symm_apply hz]
    isScSmoothOn_inv := by
      refine MPolyfold.IsScSmoothOn.of_exists_charts
        (isOpenMap_of_B X hB _ hS.isScSmoothOn.isOpen)
        (EpGroupoid.continuousOn_sheet_inv hS) fun q hq => ?_
      obtain ⟨φ, hφ, rfl⟩ := hq
      obtain ⟨ψ, hψ, hφψ⟩ := X.PMor.exists_isChart_mem_source φ
      have ho : IsOpen (ψ.source ∩ W) := ψ.isOpen_source.inter hS.isScSmoothOn.isOpen
      let ψ' := ψ.restrict inter_subset_left ho
      have hψ' : X.PMor.IsChart ψ' := MPolyfold.IsChart.restrict _ hψ _ _
      refine ⟨X.reducedChart ψ' hS inter_subset_right, ψ', X.reducedπ '' ψ'.source,
        isChart_reducedChart' hψ' hS inter_subset_right, hψ',
        isOpenMap_of_B X hB _ ψ'.isOpen_source, ⟨φ, ⟨hφψ, hφ⟩, rfl⟩,
        fun x hx => ⟨image_mono inter_subset_right hx, hx⟩, ?_, ?_⟩
      · rintro _ ⟨φ', hφ', rfl⟩
        change σ (X.src φ') ∈ ψ'.source
        rw [hS.left_inv φ' hφ'.2]
        exact hφ'
      · rw [← X.reducedChart_source ψ' hS inter_subset_right, MChart.image_source]
        refine (isScSmoothRetractMap_id _).congr fun z hz => ?_
        change z = ψ' (σ (X.src (ψ'.symm z)))
        rw [hS.left_inv _ (inter_subset_right (ψ'.symm_mapsTo hz)), ψ'.apply_symm_apply hz]
    mapsTo := fun _ hφ => ⟨_, hφ, rfl⟩
    mapsTo_inv := fun _ hq => EpGroupoid.sheet_inv_mem hS hq
    left_inv := fun _ hφ => EpGroupoid.sheet_inv_π hS hφ
    right_inv := fun _ hq => EpGroupoid.π_sheet_inv hS hq }

theorem isLocalScDiffeo_reducedπ' (hB : B) :
    type_of% @Polyfold.EpGroupoid.isLocalScDiffeo_reducedπ.{0} := by
  intro Obj Mor _ _ _ _ _ _ X _ _ φ
  obtain ⟨W, V, σ, hφ, hS⟩ := X.isLocalScDiffeo_src φ
  exact ⟨W, _, _, hφ, isScDiffeoOn_reducedπ' hB hS⟩

theorem proposition_7_9' (hB : B) : type_of% @Polyfold.EpGroupoid.proposition_7_2_10.{0} := by
  intro Obj Mor _ _ _ _ _ _ X _ _
  exact ⟨rfl, fun _ hχ => X.reducedPolyfold.isChart_of_mem hχ,
    fun _ _ _ hS => ⟨isOpenMap_of_B X hB _ hS.isScSmoothOn.isOpen, isScDiffeoOn_reducedπ' hB hS⟩,
    isLocalScDiffeo_reducedπ' hB X⟩

theorem B_to_A : B → A := fun hB =>
  ⟨isQuotientMap', isOpenMap' hB, injOn' hB, reducedChart_compatible' hB, isChart_reducedChart',
    isScDiffeoOn_reducedπ' hB, isLocalScDiffeo_reducedπ' hB, proposition_7_9' hB,
    fun {_ _} _ _ _ _ _ _ {X} _ => (t2_para_of_B X hB).1,
    fun {_ _} _ _ _ _ _ _ {X} _ => (t2_para_of_B X hB).2,
    fun {_ _} _ _ _ _ _ _ X _ _ => (t2_para_of_B X hB).2⟩

#rt_check_soft RoundTrip.V7_39.A_and_t2_to_B [Polyfold.EpGroupoid.isQuotientMap_reducedπ,
  Polyfold.EpGroupoid.isOpenMap_reducedπ, Polyfold.EpGroupoid.injOn_reducedπ,
  Polyfold.EpGroupoid.reducedChart_compatible, Polyfold.EpGroupoid.isChart_reducedChart,
  Polyfold.EpGroupoid.isScDiffeoOn_reducedπ, Polyfold.EpGroupoid.isLocalScDiffeo_reducedπ,
  Polyfold.EpGroupoid.proposition_7_2_10, Polyfold.EpGroupoid.t2Space_reducedMor_of_isEffective,
  Polyfold.EpGroupoid.paracompactSpace_reducedMor_of_isEffective,
  Polyfold.EpGroupoid.paracompactSpace_reducedMor_of_t3]
#rt_check_soft RoundTrip.V7_39.B_to_A [Polyfold.EpGroupoid.isQuotientMap_reducedπ,
  Polyfold.EpGroupoid.isOpenMap_reducedπ, Polyfold.EpGroupoid.injOn_reducedπ,
  Polyfold.EpGroupoid.reducedChart_compatible, Polyfold.EpGroupoid.isChart_reducedChart,
  Polyfold.EpGroupoid.isScDiffeoOn_reducedπ, Polyfold.EpGroupoid.isLocalScDiffeo_reducedπ,
  Polyfold.EpGroupoid.proposition_7_2_10, Polyfold.EpGroupoid.t2Space_reducedMor_of_isEffective,
  Polyfold.EpGroupoid.paracompactSpace_reducedMor_of_isEffective,
  Polyfold.EpGroupoid.paracompactSpace_reducedMor_of_t3]
#rt_overlap RoundTrip.V7_39.B_to_A [Polyfold.EpGroupoid.isQuotientMap_reducedπ,
  Polyfold.EpGroupoid.isOpenMap_reducedπ, Polyfold.EpGroupoid.injOn_reducedπ,
  Polyfold.EpGroupoid.reducedChart_compatible, Polyfold.EpGroupoid.isChart_reducedChart,
  Polyfold.EpGroupoid.isScDiffeoOn_reducedπ, Polyfold.EpGroupoid.isLocalScDiffeo_reducedπ,
  Polyfold.EpGroupoid.proposition_7_2_10, Polyfold.EpGroupoid.t2Space_reducedMor_of_isEffective,
  Polyfold.EpGroupoid.paracompactSpace_reducedMor_of_isEffective,
  Polyfold.EpGroupoid.paracompactSpace_reducedMor_of_t3]

end RoundTrip.V7_39
