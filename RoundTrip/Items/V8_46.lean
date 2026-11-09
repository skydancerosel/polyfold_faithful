import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_46

/-! Round trip for V8_46 (2021 Definition 8.3.5, p. 379: auxiliary norms on strong bundles over
ep-groupoids).

`A` is the conjunction of the types of the three listed theorems, universes at `0`:
`EpStrongBundle.exists_oneVal_eq_μ` (condition (3) is not vacuous: `μ` maps
`𝐗 ₛ×_P W_{0,1}` into `W_{0,1}`), `EpStrongBundle.exists_isAuxNorm_trivial` (every strong bundle
over a trivial ep-groupoid has an auxiliary norm) and `TrivialBundle.exists_isAuxNorm_epBundle`
(no universe parameters; the concrete case `ℝⁿ × ℝᵏ → ℝⁿ`).  The listed
`EpStrongBundle.IsAuxNorm` is the definition the item is about (vocabulary).

`B` says that the project's `IsAuxNorm` is the text's notion (`IsAuxNormB`).  This is proved
outright (`B_holds`): `IsAuxNorm` is Part I's `StrongBundle.IsAuxNorm` (continuity, a complete
norm on every fibre, `P(h_k) → x ∧ N(h_k) → 0 ⇒ h_k → 0_x`) plus the invariance `map_μ`, field
for field `B`'s (1)–(3); `B`'s separately stated `N ≥ 0` is Part I's `IsAuxNorm.nonneg` (it
follows from the fibre norm).  So the definitions agree exactly.

Both directions are therefore vacuous for the audit: `A_to_B` is `B_holds`, and `B_to_A`
re-proves `A`'s three theorems outright (they are a non-vacuity lemma and satisfiability
witnesses, which a definitional equivalence cannot imply). -/

namespace RoundTrip.V8_46
open Polyfold Filter Topology

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.exists_oneVal_eq_μ.{0, 0}) ∧
  (type_of% @Polyfold.EpStrongBundle.exists_isAuxNorm_trivial.{0, 0}) ∧
  (type_of% @Polyfold.TrivialBundle.exists_isAuxNorm_epBundle)

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.exists_oneVal_eq_μ.{0, 0},
    @Polyfold.EpStrongBundle.exists_isAuxNorm_trivial.{0, 0},
    @Polyfold.TrivialBundle.exists_isAuxNorm_epBundle⟩

/-- **The definitions agree**: the project's `EpStrongBundle.IsAuxNorm` is the text's notion. -/
theorem B_holds : B := by
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ Bd E N
  constructor
  · rintro ⟨hN, hμ⟩
    exact ⟨hN.continuous, hN.nonneg, hN.fiber, hN.tendsto_zeroOne, hμ⟩
  · rintro ⟨hc, -, hf, ht, hμ⟩
    exact ⟨⟨hc, hf, ht⟩, hμ⟩

/-! ### `A → B` (outright: `B` is a definitional statement) -/

theorem A_to_B : A → B := fun _ => B_holds

/-! ### `B → A` (outright re-proofs of the witness theorems) -/

section Outright

theorem exists_oneVal_eq_μ' {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    {X : EpGroupoid Obj Mor} {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W]
    {P : W → Obj} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {B : StrongBundle X.PObj P} (E : EpStrongBundle X B) (k : B.One) (φ : Mor)
    (hk : P (B.oneVal k) = X.src φ) : ∃ h : B.One, B.oneVal h = E.μ ⟨(φ, B.oneVal k), hk⟩ := by
  have := B.paracompactSpace_pullback X.PMor X.src
  have hmem : (⟨(φ, B.oneVal k), hk⟩ : pullbackSpace P X.src) ∈
      (B.pullback X.isScSmoothMap_src).oneSet :=
    (B.mem_oneSet_pullback_iff X.isScSmoothMap_src _).2 (B.oneVal_mem k)
  exact ⟨B.oneMk _ (E.isStrongBundleMap.mapsTo_oneSet hmem), rfl⟩

theorem exists_isAuxNorm_trivial' {Z : Type} [TopologicalSpace Z] [T2Space Z]
    [ParacompactSpace Z] {PZ : MPolyfold Z} {W : Type} [TopologicalSpace W] [T2Space W]
    [ParacompactSpace W] {P : W → Z} [∀ x, AddCommGroup (P ⁻¹' {x})]
    [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PZ P) :
    ∃ N : B.One → ℝ, (EpStrongBundle.trivial B).IsAuxNorm N := by
  obtain ⟨N, hN⟩ := proposition_5_3_exists (B := B)
  exact ⟨N, hN, fun h k _ _ hhk => by rw [B.oneVal_injective hhk]⟩

end Outright

theorem B_to_A : B → A := fun _ =>
  ⟨@exists_oneVal_eq_μ', @exists_isAuxNorm_trivial',
    fun n k => exists_isAuxNorm_trivial' (TrivialBundle.bundle n k)⟩

#rt_check RoundTrip.V8_46.A_to_B [Polyfold.EpStrongBundle.exists_oneVal_eq_μ,
  Polyfold.EpStrongBundle.exists_isAuxNorm_trivial, Polyfold.TrivialBundle.exists_isAuxNorm_epBundle]
#rt_check RoundTrip.V8_46.B_to_A [Polyfold.EpStrongBundle.exists_oneVal_eq_μ,
  Polyfold.EpStrongBundle.exists_isAuxNorm_trivial, Polyfold.TrivialBundle.exists_isAuxNorm_epBundle]
#rt_overlap RoundTrip.V8_46.B_to_A [Polyfold.EpStrongBundle.exists_oneVal_eq_μ,
  Polyfold.EpStrongBundle.exists_isAuxNorm_trivial, Polyfold.TrivialBundle.exists_isAuxNorm_epBundle]
#rt_overlap RoundTrip.V8_46.A_to_B [Polyfold.EpStrongBundle.exists_oneVal_eq_μ,
  Polyfold.EpStrongBundle.exists_isAuxNorm_trivial, Polyfold.TrivialBundle.exists_isAuxNorm_epBundle]

end RoundTrip.V8_46
