import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_24

/-! Round trip for V2_24 (Proposition 2.21 (1), (2): the M-polyfold structure of a
sub-M-polyfold).

`A` is the conjunction of the types of the listed theorems (all at universe `0`, B lives in
`Type`): `SubData.image_shrink`, `SubData.rho_isScSmooth`, `SubData.isScRetract_image`,
`subChart_compatible`, `subPolyfold_inclusion_isScSmooth`, `subPolyfold_retraction_isScSmooth`,
`IsScSmoothRetractMap.mono_source` (no universe) and `paracompactSpace_of_isClosed`.
`SubData`, `SubData.shrink`, `subChart`, `subAtlas`, `subPolyfold` are definitions (vocabulary).

`A → B` (proved).  `Q := subPolyfold hA` (the atlas of all sub-charts
`(φ|_{W ∩ A}, W ∩ A, (φ(W ∩ A), C, E))`):
* (1) is A's `subPolyfold_inclusion_isScSmooth`; the embedding conjunct is
  `Topology.IsEmbedding.subtypeVal` (subspace topology on both sides);
* (2): B's data `(V, r)` is exactly a `SubData P A`; A's `subPolyfold_retraction_isScSmooth`
  gives the sc-smoothness of the project's `i⁻¹ ∘ r` (`retractInto a₀`, junk value `a₀` off `V`),
  and every `g` agreeing with `r` on `V` is handled by `IsScSmoothOn.congr` (`V = ∅` separately,
  where no junk value `a₀ : A` need exist);
* B also asserts `ParacompactSpace ↥A` for EVERY sub-M-polyfold.  A only contains
  `paracompactSpace_of_isClosed` (closed `A`); the general case is the project lemma
  `MPolyfold.paracompactSpace_subtype` (Metrizable.lean, via Theorem 2.16), outside this item.
Harness: `subPolyfold` is built from `subAtlas` and `subChart`.  `subAtlas._proof_1` (the
`compatible` field) uses the banned `subChart_compatible` (and through it `mono_source`), and the
body of `subChart` passes the banned `isScRetract_image` (and through it `rho_isScSmooth`,
`image_shrink`) as the retract proof of its model `φ(W ∩ A)`, NOT abstracted into a `_proof_N`.
So every term mentioning `A` (whose statement contains `subPolyfold`) fails `#rt_check` and also
`#rt_check_soft` (documented with `#guard_msgs`).  As in items V2_53/V2_61, `A_to_B` is factored as
`A'_to_B ∘ A_to_A'` (`A'`: A's (1), (2) with `Q` existentially quantified; `A_to_A'` a
projection), and `#rt_check` passes on `A'_to_B`; as in item V1_32, a local
`#rt_check_except_defs` runs the harness traversal on `A_to_B` with the bodies of `subChart` and
`subAtlas` not unfolded, and passes.

`B → A` (not proved; genuine).  B only asserts that SOME paracompactness instance and SOME
structure `Q` with (1), (2) exist.  A is about the project's specific construction: the
set-theoretic and chart lemmas `image_shrink` (`r(W) = W ∩ A`), `rho_isScSmooth`,
`isScRetract_image`, `subChart_compatible`, the general retract lemma `mono_source` and
`paracompactSpace_of_isClosed` say nothing about `Q` and cannot be extracted from B; (1), (2) for
`subPolyfold hA` itself would follow from B only after showing that every `Q` with (1), (2) has the
sub-charts among its charts (compatibility via `κ ∘ χ⁻¹ = κ ∘ (i⁻¹ ∘ r) ∘ φ⁻¹` and
`χ ∘ κ⁻¹ = φ ∘ i ∘ κ⁻¹`), i.e. the uniqueness of the natural structure — new chart work, and the
remaining conjuncts would still have to be re-proved without B. -/

namespace RoundTrip.V2_24
open Polyfold Set MPolyfold

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.SubData.image_shrink.{0}) ∧
    (type_of% @Polyfold.MPolyfold.SubData.rho_isScSmooth.{0}) ∧
    (type_of% @Polyfold.MPolyfold.SubData.isScRetract_image.{0}) ∧
    (type_of% @Polyfold.MPolyfold.subChart_compatible.{0}) ∧
    (type_of% @Polyfold.MPolyfold.subPolyfold_inclusion_isScSmooth.{0}) ∧
    (type_of% @Polyfold.MPolyfold.subPolyfold_retraction_isScSmooth.{0}) ∧
    (type_of% @Polyfold.IsScSmoothRetractMap.mono_source) ∧
    (type_of% @Polyfold.MPolyfold.paracompactSpace_of_isClosed.{0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.SubData.image_shrink.{0}, @Polyfold.MPolyfold.SubData.rho_isScSmooth.{0},
    @Polyfold.MPolyfold.SubData.isScRetract_image.{0}, @Polyfold.MPolyfold.subChart_compatible.{0},
    @Polyfold.MPolyfold.subPolyfold_inclusion_isScSmooth.{0},
    @Polyfold.MPolyfold.subPolyfold_retraction_isScSmooth.{0},
    @Polyfold.IsScSmoothRetractMap.mono_source,
    @Polyfold.MPolyfold.paracompactSpace_of_isClosed.{0}⟩

/-- The existential form of A's (1), (2) (`Q` quantified instead of `subPolyfold hA`), used to keep
the definitions `subChart`, `subAtlas` out of the checked proof (see the harness note). -/
def A' : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X) (S : Set X),
    P.IsSubMPolyfold S → ∀ [ParacompactSpace S], ∃ Q : MPolyfold S,
      Q.IsScSmoothMap P (Subtype.val : S → X) ∧
        ∀ (d : P.SubData S) (a₀ : S), P.IsScSmoothOn Q (d.retractInto a₀) d.V

/-- `A → A'`: a projection, `Q = subPolyfold hS`. -/
theorem A_to_A' : A → A' := by
  rintro ⟨-, -, -, -, hincl, hretr, -, -⟩ X _ _ _ P S hS _
  exact ⟨subPolyfold hS, hincl hS, hretr hS⟩

/-- `A' → B`: (1) and (2) from A', paracompactness of `A` from the project's
`paracompactSpace_subtype`. -/
theorem A'_to_B : A' → B := by
  intro hA' X _ _ _ P S hS
  have : ParacompactSpace S := P.paracompactSpace_subtype S
  obtain ⟨Q, hincl, hretr⟩ := hA' X P S hS
  refine ⟨inferInstance, Q, ⟨hincl, Topology.IsEmbedding.subtypeVal⟩, ?_⟩
  intro V r hV hrV hsm hidem himg g hg
  let d : P.SubData S := ⟨V, r, hV, hrV, hsm, hidem, himg⟩
  rcases V.eq_empty_or_nonempty with hV0 | ⟨x₀, hx₀⟩
  · subst hV0
    exact IsScSmoothOn.of_exists_charts isOpen_empty (continuousOn_empty _)
      fun x hx => absurd hx (notMem_empty x)
  · have h := hretr d (g x₀)
    refine h.congr fun x hx => Subtype.ext ?_
    rw [SubData.retractInto_val d (g x₀) hx, hg x hx]

/-- `A → B`. -/
theorem A_to_B : A → B := fun h => A'_to_B (A_to_A' h)

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

#rt_check RoundTrip.V2_24.A'_to_B [Polyfold.MPolyfold.SubData.image_shrink,
  Polyfold.MPolyfold.SubData.rho_isScSmooth, Polyfold.MPolyfold.SubData.isScRetract_image,
  Polyfold.MPolyfold.subChart_compatible, Polyfold.MPolyfold.subPolyfold_inclusion_isScSmooth,
  Polyfold.MPolyfold.subPolyfold_retraction_isScSmooth, Polyfold.IsScSmoothRetractMap.mono_source,
  Polyfold.MPolyfold.paracompactSpace_of_isClosed]
-- `A_to_B` itself cannot pass `#rt_check`/`#rt_check_soft`: its binder type `A` mentions
-- `subPolyfold`, whose chart definition `subChart` passes the banned `SubData.isScRetract_image` as
-- the (non-abstracted) retract proof of its model `φ(W ∩ A)`, and `subAtlas._proof_1` uses the banned
-- `subChart_compatible`.  The traversal with those two bodies not unfolded passes:
#rt_check_except_defs RoundTrip.V2_24.A_to_B [Polyfold.MPolyfold.subChart,
  Polyfold.MPolyfold.subAtlas] [Polyfold.MPolyfold.SubData.image_shrink,
  Polyfold.MPolyfold.SubData.rho_isScSmooth, Polyfold.MPolyfold.SubData.isScRetract_image,
  Polyfold.MPolyfold.subChart_compatible, Polyfold.MPolyfold.subPolyfold_inclusion_isScSmooth,
  Polyfold.MPolyfold.subPolyfold_retraction_isScSmooth, Polyfold.IsScSmoothRetractMap.mono_source,
  Polyfold.MPolyfold.paracompactSpace_of_isClosed]
/-- error: rt_check_soft FAIL: RoundTrip.V2_24.A_to_B uses [Polyfold.MPolyfold.SubData.image_shrink,
 Polyfold.MPolyfold.SubData.rho_isScSmooth,
 Polyfold.MPolyfold.SubData.isScRetract_image] -/
#guard_msgs in
#rt_check_soft RoundTrip.V2_24.A_to_B [Polyfold.MPolyfold.SubData.image_shrink,
  Polyfold.MPolyfold.SubData.rho_isScSmooth, Polyfold.MPolyfold.SubData.isScRetract_image,
  Polyfold.MPolyfold.subChart_compatible, Polyfold.MPolyfold.subPolyfold_inclusion_isScSmooth,
  Polyfold.MPolyfold.subPolyfold_retraction_isScSmooth, Polyfold.IsScSmoothRetractMap.mono_source,
  Polyfold.MPolyfold.paracompactSpace_of_isClosed]

end RoundTrip.V2_24
