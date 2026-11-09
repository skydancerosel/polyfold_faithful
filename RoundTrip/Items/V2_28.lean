import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_28

/-! Round trip for V2_28 (Proposition 2.24: `d_X` is invariant under sc-diffeomorphism germs).

`A` is the conjunction of the types of the listed theorems `Polyfold.proposition_2_4_4`,
`Polyfold.MPolyfold.transportChart_isChart` and `Polyfold.MPolyfold.degIndex_le_of_isScDiffeoOn`,
all instantiated at universes `0, 0` (B lives in `Type`).  `IsScDiffeoOn` and `transportChart` are
definitions (vocabulary); B uses the project's `IsScDiffeoOn` itself (the blind author checked it
is the text's "germ of sc-diffeomorphisms `f : (U, x) → (V, f(x))`" with `x ∈ U`).

* `proposition_2_4_4` is B verbatim (same binders, `x ∈ U`, `P.IsScDiffeoOn Q f g U V`).
* `degIndex_le_of_isScDiffeoOn` (one inequality) follows from B.
* `transportChart_isChart` (the chart `ψ ∘ f` of `X` built from a chart `ψ` of `Y` is a chart of the
  structure) is the main step of the proof, not of the statement; B does not imply it (B speaks
  only of `d_X`, not of charts).  In `B → A` it is re-proved directly from the definition of
  `IsScSmoothOn` (the argument of the project, written out again: the transition maps are
  `φ ∘ g ∘ ψ⁻¹` and `ψ ∘ f ∘ φ⁻¹`). -/

namespace RoundTrip.V2_28
open Polyfold Set MPolyfold

/-- The project's statement (universes `0, 0`). -/
def A : Prop :=
  (type_of% @Polyfold.proposition_2_4_4.{0, 0}) ∧
    (type_of% @Polyfold.MPolyfold.transportChart_isChart.{0, 0}) ∧
    (type_of% @Polyfold.MPolyfold.degIndex_le_of_isScDiffeoOn.{0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.proposition_2_4_4.{0, 0}, @Polyfold.MPolyfold.transportChart_isChart.{0, 0},
    @Polyfold.MPolyfold.degIndex_le_of_isScDiffeoOn.{0, 0}⟩

section Glue

variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {f : X → Y} {g : Y → X} {U : Set X} {V : Set Y}

/-- The transported chart is a chart of the structure of `X` (direct proof). -/
theorem transportChart_isChart' (h : P.IsScDiffeoOn Q f g U V) {ψ : MChart Y} (hψ : Q.IsChart ψ) :
    P.IsChart (transportChart h ψ) := by
  intro φ hφ
  have hφ' : P.IsChart φ := P.isChart_of_mem hφ
  set χ := transportChart h ψ with hχ
  set s := φ.source ∩ χ.source with hs
  have hso : IsOpen s := φ.isOpen_source.inter χ.isOpen_source
  set V'' := V ∩ ψ.source ∩ g ⁻¹' φ.source with hV''
  have hV''o : IsOpen V'' :=
    (h.isScSmoothOn_inv.continuousOn.mono inter_subset_left).isOpen_inter_preimage
      (h.isScSmoothOn_inv.isOpen.inter ψ.isOpen_source) φ.isOpen_source
  have hfs : f '' s = V'' := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxφ, hxU, hxψ⟩, rfl⟩
      exact ⟨⟨h.mapsTo hxU, hxψ⟩, by rw [mem_preimage, h.left_inv x hxU]; exact hxφ⟩
    · rintro ⟨⟨hyV, hyψ⟩, hyφ⟩
      refine ⟨g y, ⟨hyφ, h.mapsTo_inv hyV, ?_⟩, h.right_inv y hyV⟩
      rw [mem_preimage, h.right_inv y hyV]; exact hyψ
  have hχs : χ.overlap φ = ψ '' V'' := by
    change (ψ ∘ f) '' (χ.source ∩ φ.source) = ψ '' V''
    rw [inter_comm, image_comp, ← hs, hfs]
  constructor
  · rw [hχs]
    have := h.isScSmoothOn_inv.smooth ψ φ hψ hφ' V'' hV''o (fun y hy => ⟨hy.1.1, hy.1.2⟩)
      fun y hy => hy.2
    refine this.mono_target ?_
    rintro _ ⟨y, hy, rfl⟩
    change φ (g (ψ.symm (ψ y))) ∈ φ.overlap χ
    rw [ψ.symm_apply_apply hy.1.2]
    refine ⟨g y, ⟨hy.2, h.mapsTo_inv hy.1.1, ?_⟩, rfl⟩
    rw [mem_preimage, h.right_inv y hy.1.1]; exact hy.1.2
  · have := h.isScSmoothOn.smooth φ ψ hφ' hψ s hso (fun x hx => ⟨hx.2.1, hx.1⟩) fun x hx => hx.2.2
    refine this.mono_target ?_
    rintro _ ⟨x, hx, rfl⟩
    change ψ (f (φ.symm (φ x))) ∈ χ.overlap φ
    rw [φ.symm_apply_apply hx.1]
    exact ⟨x, ⟨hx.2, hx.1⟩, rfl⟩

end Glue

/-- `A → B`: B is `proposition_2_4_4`. -/
theorem A_to_B : A → B := by
  rintro ⟨h224, -, -⟩ X _ _ _ P Y _ _ _ Q f g U V x hx h
  exact h224 h hx

/-- `B → A`: `proposition_2_4_4` and its half are B; `transportChart_isChart` is re-proved. -/
theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_⟩
  · intro X _ _ _ P Y _ _ _ Q f g U V h x hx
    exact hB X P Y Q f g U V x hx h
  · intro X _ _ _ P Y _ _ _ Q f g U V h ψ hψ
    exact transportChart_isChart' h hψ
  · intro X _ _ _ P Y _ _ _ Q f g U V h x hx
    exact (hB X P Y Q f g U V x hx h).le

#rt_check RoundTrip.V2_28.A_to_B [Polyfold.proposition_2_4_4,
  Polyfold.MPolyfold.transportChart_isChart, Polyfold.MPolyfold.degIndex_le_of_isScDiffeoOn]
#rt_check RoundTrip.V2_28.B_to_A [Polyfold.proposition_2_4_4,
  Polyfold.MPolyfold.transportChart_isChart, Polyfold.MPolyfold.degIndex_le_of_isScDiffeoOn]
#rt_overlap RoundTrip.V2_28.B_to_A [Polyfold.proposition_2_4_4,
  Polyfold.MPolyfold.transportChart_isChart, Polyfold.MPolyfold.degIndex_le_of_isScDiffeoOn]

end RoundTrip.V2_28
