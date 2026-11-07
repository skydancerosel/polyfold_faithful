import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V7_23

/-! Round trip for V7_23 (pp. 232–233: the map `Φ̂ : G_x → Diff_sc(𝐔(x))`).

`A` is the conjunction of the types of the ten listed theorems, universes at `0`:
`NaturalRep.Φhat_Γ`, `Φhat_mem_image`, `index_Φhat`, `src_Φhat`, `tgt_Φhat`, `Φ_conj`,
`Φhat_one`, `Φhat_mul`, `isScDiffeoOn_Φhat`, `image_Φhat` (`Φhat` itself is a definition: the
conjugation `Φ̂(g)(φ) = Γ(g, t φ) ∘ φ ∘ Γ(g, s φ)⁻¹`, a total map).  All are stated for
`R : X.NaturalRep x`, whose `U` is **connected**.

* `B` uses the text's formula `Φ̂(g)(φ) = Γ(g h g⁻¹, g ∗ s φ)` for `φ ∈ 𝐔(h)` (`PhiHatB`, with the
  index chosen), and claims (i)–(v) for **every** natural action (`U` open, not necessarily
  connected), plus (vi) the existence of a small connected `U(x)` with the sheet decomposition.
* `A → B` fails as a proof: `A` cannot be applied to a disconnected `U` (no `NaturalRep` with
  that `U`), and on such `U` the project's conjugation formula need not agree with `PhiHatB`
  (that agreement is `Φhat_Γ`, which rests on the functoriality of `Γ`, i.e. on connectedness).
  We believe (i)–(v) are nevertheless true for disconnected `U` (the text's formula needs only
  property (3) of Theorem 7.1: the index of `Γ(k, z)` is `k`), so this is proof effort: one would
  have to re-prove (i)–(v), in particular the sc-smoothness (ii), outright.  (vi) would follow from
  `A` with `theorem_7_1` and the sheet lemmas.
* `B → A`: on a natural representation, `R.Φhat g = PhiHatB g` on `𝐔(x)` (`agree`, via the text's
  formula, which follows from `Γ_mul`, `Γ_inv`, results of V7_22).  Then `src_Φhat`, `tgt_Φhat`
  come from (v), `Φhat_mul` from (iii), `Φhat_one` from (i), `Φhat_mem_image`, `image_Φhat` from
  (iv), `isScDiffeoOn_Φhat` from (ii) (the inverse is identified with `Φ̂(g⁻¹)`).  `Φhat_Γ`,
  `index_Φhat`, `Φ_conj` are formulas about the project's own `Φhat`/`index` and are re-proved
  outright (from `Γ_mul`, `Γ_inv`, `Φ_mul`). -/

namespace RoundTrip.V7_23
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.NaturalRep.Φhat_Γ.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.Φhat_mem_image.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.index_Φhat.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.src_Φhat.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.tgt_Φhat.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.Φ_conj.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.Φhat_one.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.Φhat_mul.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_Φhat.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.NaturalRep.image_Φhat.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.NaturalRep.Φhat_Γ.{0}, @Polyfold.EpGroupoid.NaturalRep.Φhat_mem_image.{0},
    @Polyfold.EpGroupoid.NaturalRep.index_Φhat.{0}, @Polyfold.EpGroupoid.NaturalRep.src_Φhat.{0},
    @Polyfold.EpGroupoid.NaturalRep.tgt_Φhat.{0}, @Polyfold.EpGroupoid.NaturalRep.Φ_conj.{0},
    @Polyfold.EpGroupoid.NaturalRep.Φhat_one.{0}, @Polyfold.EpGroupoid.NaturalRep.Φhat_mul.{0},
    @Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_Φhat.{0},
    @Polyfold.EpGroupoid.NaturalRep.image_Φhat.{0}⟩

/-! ### `B → A` -/

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor} {x : Obj}

/-- `IsScDiffeoOn` is insensitive to changing the map on its source. -/
theorem diffeo_congr {A B : Type} [TopologicalSpace A] [T2Space A] [ParacompactSpace A]
    [TopologicalSpace B] [T2Space B] [ParacompactSpace B] {P : MPolyfold A} {Q : MPolyfold B}
    {f f' : A → B} {g : B → A} {S : Set A} {T : Set B} (h : P.IsScDiffeoOn Q f g S T)
    (hf : EqOn f f' S) : P.IsScDiffeoOn Q f' g S T where
  isScSmoothOn := h.isScSmoothOn.congr hf
  isScSmoothOn_inv := h.isScSmoothOn_inv
  mapsTo a ha := hf ha ▸ h.mapsTo ha
  mapsTo_inv := h.mapsTo_inv
  left_inv a ha := by rw [← hf ha, h.left_inv a ha]
  right_inv b hb := by rw [← hf (h.mapsTo_inv hb), h.right_inv b hb]

/-- ... and the inverse on its target. -/
theorem diffeo_congr_inv {A B : Type} [TopologicalSpace A] [T2Space A] [ParacompactSpace A]
    [TopologicalSpace B] [T2Space B] [ParacompactSpace B] {P : MPolyfold A} {Q : MPolyfold B}
    {f : A → B} {g g' : B → A} {S : Set A} {T : Set B} (h : P.IsScDiffeoOn Q f g S T)
    (hg : EqOn g g' T) : P.IsScDiffeoOn Q f g' S T :=
  (diffeo_congr h.symm hg).symm


/-- The natural action underlying a natural representation. -/
theorem isNatAction_of_rep (R : X.NaturalRep x) : IsNatAction X x R.U R.Φ R.Γ where
  isOpen := R.isOpen_U
  mem := R.mem_U
  diffeo g := ⟨_, R.isScDiffeoOn_Φ g⟩
  hom := R.Φ_mul
  smooth := R.isScSmoothOn_Γ
  Γ_x := R.Γ_self
  src_tgt g y hy := ⟨R.src_Γ g y hy, R.tgt_Γ g y hy⟩
  unique := R.existsUnique_Γ

variable (R : X.NaturalRep x)

/-- The text's formula for the project's `Φ̂` (re-proved from `Γ_mul`, `Γ_inv` of V7_22). -/
theorem Φhat_Γ' (g h : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) :
    R.Φhat g (R.Γ h y) = R.Γ (g * h * g⁻¹) (R.Φ g y) := by
  unfold EpGroupoid.NaturalRep.Φhat
  rw [R.src_Γ h y hy, R.tgt_Γ h y hy, R.Γ_mul g h hy, ← R.Γ_inv g hy,
    ← R.Γ_mul (g * h) g⁻¹ (R.mapsTo_Φ g hy), R.Φ_inv_Φ g hy]

/-- `B`'s chosen index puts `φ` in its sheet. -/
theorem idxB_spec {φ : Mor} (hφ : φ ∈ X.morOn R.U) :
    φ ∈ sheetB X x R.U R.Γ (idxB X x R.U R.Γ φ) := by
  have hex : ∃ h, φ ∈ sheetB X x R.U R.Γ h := by
    obtain ⟨h, hh⟩ := R.exists_Γ_eq hφ
    exact ⟨h, X.src φ, hφ.1, hh⟩
  have : idxB X x R.U R.Γ φ = hex.choose := by
    unfold idxB
    rw [dif_pos hex]
  rw [this]
  exact hex.choose_spec

/-- **The project's `Φ̂` is `B`'s `Φ̂` on `𝐔(x)`.** -/
theorem agree (g : X.Isotropy x) {φ : Mor} (hφ : φ ∈ X.morOn R.U) :
    R.Φhat g φ = PhiHatB X x R.U R.Φ R.Γ g φ := by
  obtain ⟨y, hy, hyφ⟩ := idxB_spec R hφ
  have hsrc : X.src φ = y := by rw [← hyφ, R.src_Γ _ y hy]
  unfold PhiHatB
  rw [hsrc]
  conv_lhs => rw [← hyφ]
  exact Φhat_Γ' R g _ hy

theorem mem_morOn_PhiHatB (hB : B) (g : X.Isotropy x) {φ : Mor} (hφ : φ ∈ X.morOn R.U) :
    PhiHatB X x R.U R.Φ R.Γ g φ ∈ X.morOn R.U := by
  obtain ⟨-, -, -, -, hv⟩ := (hB Obj Mor X x).1 R.U R.Φ R.Γ (isNatAction_of_rep R)
  refine ⟨?_, ?_⟩
  · rw [(hv g φ hφ).1]; exact R.mapsTo_Φ g hφ.1
  · rw [(hv g φ hφ).2]; exact R.mapsTo_Φ g hφ.2

theorem Φhat_one' (hB : B) {φ : Mor} (hφ : φ ∈ X.morOn R.U) : R.Φhat 1 φ = φ := by
  obtain ⟨hi, -, -, -, -⟩ := (hB Obj Mor X x).1 R.U R.Φ R.Γ (isNatAction_of_rep R)
  rw [agree R 1 hφ]
  unfold PhiHatB
  rw [one_mul, inv_one, mul_one, R.Φ_one _ hφ.1]
  exact ((hi φ hφ).2 _ (idxB_spec R hφ)).1.symm

theorem Φhat_mul' (hB : B) (g g' : X.Isotropy x) {φ : Mor} (hφ : φ ∈ X.morOn R.U) :
    R.Φhat (g * g') φ = R.Φhat g (R.Φhat g' φ) := by
  obtain ⟨-, -, hiii, -, -⟩ := (hB Obj Mor X x).1 R.U R.Φ R.Γ (isNatAction_of_rep R)
  rw [agree R (g * g') hφ, agree R g' hφ, agree R g (mem_morOn_PhiHatB R hB g' hφ)]
  exact hiii g g' φ hφ

end

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `Φhat_Γ` (outright, from `Γ_mul`, `Γ_inv`)
    intro Obj Mor _ _ _ _ _ _ X x R g h y hy
    exact Φhat_Γ' R g h hy
  · -- `Φhat_mem_image`, from (iv)
    intro Obj Mor _ _ _ _ _ _ X x R g h φ hφ
    obtain ⟨-, -, -, hiv, -⟩ := (hB Obj Mor X x).1 R.U R.Φ R.Γ (isNatAction_of_rep R)
    obtain ⟨y, hy, rfl⟩ := hφ
    rw [agree R g (R.Γ_mem_morOn h hy)]
    rw [← show sheetB X x R.U R.Γ (g * h * g⁻¹) = R.Γ (g * h * g⁻¹) '' R.U from rfl, ← hiv g h]
    exact mem_image_of_mem _ ⟨y, hy, rfl⟩
  · -- `index_Φhat` (outright)
    intro Obj Mor _ _ _ _ _ _ X x R g φ hφ
    conv_lhs => rw [← R.Γ_index hφ]
    rw [Φhat_Γ' R g _ hφ.1, R.index_Γ _ (R.mapsTo_Φ g hφ.1)]
  · -- `src_Φhat`, from (v)
    intro Obj Mor _ _ _ _ _ _ X x R g φ hφ
    obtain ⟨-, -, -, -, hv⟩ := (hB Obj Mor X x).1 R.U R.Φ R.Γ (isNatAction_of_rep R)
    rw [agree R g hφ]
    exact (hv g φ hφ).1
  · -- `tgt_Φhat`, from (v)
    intro Obj Mor _ _ _ _ _ _ X x R g φ hφ
    obtain ⟨-, -, -, -, hv⟩ := (hB Obj Mor X x).1 R.U R.Φ R.Γ (isNatAction_of_rep R)
    rw [agree R g hφ]
    exact (hv g φ hφ).2
  · -- `Φ_conj` (outright)
    intro Obj Mor _ _ _ _ _ _ X x R g h y hy
    rw [R.Φ_mul _ _ _ (R.mapsTo_Φ g hy), R.Φ_inv_Φ g hy, R.Φ_mul _ _ _ hy]
  · -- `Φhat_one`, from (i)
    intro Obj Mor _ _ _ _ _ _ X x R φ hφ
    exact Φhat_one' R hB hφ
  · -- `Φhat_mul`, from (iii)
    intro Obj Mor _ _ _ _ _ _ X x R g g' φ hφ
    exact Φhat_mul' R hB g g' hφ
  · -- `isScDiffeoOn_Φhat`, from (ii)
    intro Obj Mor _ _ _ _ _ _ X x R g
    obtain ⟨-, hii, -, -, -⟩ := (hB Obj Mor X x).1 R.U R.Φ R.Γ (isNatAction_of_rep R)
    obtain ⟨ψ, hψ⟩ := hii g
    have h1 := diffeo_congr hψ fun φ hφ => (agree R g hφ).symm
    refine diffeo_congr_inv h1 fun φ hφ => ?_
    have hm := h1.mapsTo_inv hφ
    have hr := h1.right_inv φ hφ
    calc ψ φ = R.Φhat 1 (ψ φ) := (Φhat_one' R hB hm).symm
      _ = R.Φhat (g⁻¹ * g) (ψ φ) := by rw [inv_mul_cancel]
      _ = R.Φhat g⁻¹ (R.Φhat g (ψ φ)) := Φhat_mul' R hB _ _ hm
      _ = R.Φhat g⁻¹ φ := by rw [hr]
  · -- `image_Φhat`, from (iv)
    intro Obj Mor _ _ _ _ _ _ X x R g h
    obtain ⟨-, -, -, hiv, -⟩ := (hB Obj Mor X x).1 R.U R.Φ R.Γ (isNatAction_of_rep R)
    have heq : EqOn (R.Φhat g) (PhiHatB X x R.U R.Φ R.Γ g) (R.Γ h '' R.U) := by
      rintro _ ⟨y, hy, rfl⟩
      exact agree R g (R.Γ_mem_morOn h hy)
    rw [heq.image_eq]
    exact hiv g h

#rt_check RoundTrip.V7_23.B_to_A [Polyfold.EpGroupoid.NaturalRep.Φhat_Γ,
  Polyfold.EpGroupoid.NaturalRep.Φhat_mem_image, Polyfold.EpGroupoid.NaturalRep.index_Φhat,
  Polyfold.EpGroupoid.NaturalRep.src_Φhat, Polyfold.EpGroupoid.NaturalRep.tgt_Φhat,
  Polyfold.EpGroupoid.NaturalRep.Φ_conj, Polyfold.EpGroupoid.NaturalRep.Φhat_one,
  Polyfold.EpGroupoid.NaturalRep.Φhat_mul, Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_Φhat,
  Polyfold.EpGroupoid.NaturalRep.image_Φhat]
#rt_overlap RoundTrip.V7_23.B_to_A [Polyfold.EpGroupoid.NaturalRep.Φhat_Γ,
  Polyfold.EpGroupoid.NaturalRep.Φhat_mem_image, Polyfold.EpGroupoid.NaturalRep.index_Φhat,
  Polyfold.EpGroupoid.NaturalRep.src_Φhat, Polyfold.EpGroupoid.NaturalRep.tgt_Φhat,
  Polyfold.EpGroupoid.NaturalRep.Φ_conj, Polyfold.EpGroupoid.NaturalRep.Φhat_one,
  Polyfold.EpGroupoid.NaturalRep.Φhat_mul, Polyfold.EpGroupoid.NaturalRep.isScDiffeoOn_Φhat,
  Polyfold.EpGroupoid.NaturalRep.image_Φhat]

end RoundTrip.V7_23
