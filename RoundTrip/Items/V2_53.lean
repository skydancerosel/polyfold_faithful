import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V2_53

/-! Round trip for V2_53 (Proposition 2.46: fibred products).

`A` is the conjunction of the types of the theorems `MPolyfold.isSubMPolyfold_fibredProduct`,
`isScDiffeoOn_snd_fibredProduct`, `isScDiffeoOn_fst_fibredProduct`,
`degIndex_fibredProduct_eq_snd`, `degIndex_fibredProduct_eq_fst`, `isTame_fibredProduct`,
`proposition_2_5_20` and `proposition_2_5_20_of_isLocalScDiffeo`, all at universes `0, 0, 0`.
`IsLocalScDiffeo`, `fibredProduct`, `fibredSubDataL` are definitions (vocabulary; B uses the
first two).

`A → B` (proved): sub-M-polyfold is `isSubMPolyfold_fibredProduct`; the tame clause is
`isTame_fibredProduct` with `degIndex_fibredProduct_eq_snd`; the last clause is
`proposition_2_5_20_of_isLocalScDiffeo`.  The paracompactness of the fibred product that B asks for
is Mathlib's (closed subspace of the paracompact `X × Y`).  Instances of `ParacompactSpace` and
proofs of `IsSubMPolyfold` are propositions, so the subpolyfolds built with different proofs agree
definitionally.

Harness note: the *statement* of `proposition_2_5_20_of_isLocalScDiffeo` contains the banned
`isSubMPolyfold_fibredProduct` (in `subPolyfold (isSubMPolyfold_fibredProduct hf hg.isScSmoothMap)`),
so every proof whose type mentions `A` reaches it, and both `#rt_check` and `#rt_check_soft` fail on
`A_to_B` for that reason alone.  `A_to_B` is therefore factored as `A'_to_B ∘ A_to_A'`: `A'` is
the same statements with that proof (and the paracompactness instance) universally quantified,
`A_to_A'` is a projection, and `#rt_check` passes on `A'_to_B`.

`B → A` fails for a genuine reason: `A` proves `d(x, y) = d_Y(y)` (`degIndex_fibredProduct_eq_snd`,
inside `proposition_2_5_20`) and, for two local sc-diffeomorphisms, `d = d_X = d_Y`
(`proposition_2_5_20_of_isLocalScDiffeo`), WITHOUT any tameness, whereas B asserts
`d = d_Y` only when `Y` is tame and `d = d_X = d_Y` only when `X`, `Y` are both tame.  B also says
nothing about the explicit local sc-diffeomorphisms `π₁`, `π₂` and their inverses
(`isScDiffeoOn_snd/fst_fibredProduct`).  B does give `isSubMPolyfold_fibredProduct` and
`isTame_fibredProduct` exactly (`B_to_sub`, `B_to_tame`). -/

namespace RoundTrip.V2_53
open Polyfold Set

/-- The project's statement (universes `0`). -/
def A : Prop :=
  (type_of% @Polyfold.MPolyfold.isSubMPolyfold_fibredProduct.{0, 0, 0}) ∧
    (type_of% @Polyfold.MPolyfold.isScDiffeoOn_snd_fibredProduct.{0, 0, 0}) ∧
    (type_of% @Polyfold.MPolyfold.isScDiffeoOn_fst_fibredProduct.{0, 0, 0}) ∧
    (type_of% @Polyfold.MPolyfold.degIndex_fibredProduct_eq_snd.{0, 0, 0}) ∧
    (type_of% @Polyfold.MPolyfold.degIndex_fibredProduct_eq_fst.{0, 0, 0}) ∧
    (type_of% @Polyfold.MPolyfold.isTame_fibredProduct.{0, 0, 0}) ∧
    (type_of% @Polyfold.MPolyfold.proposition_2_5_20.{0, 0, 0}) ∧
    (type_of% @Polyfold.MPolyfold.proposition_2_5_20_of_isLocalScDiffeo.{0, 0, 0})

theorem A_holds : A :=
  ⟨@Polyfold.MPolyfold.isSubMPolyfold_fibredProduct.{0, 0, 0},
    @Polyfold.MPolyfold.isScDiffeoOn_snd_fibredProduct.{0, 0, 0},
    @Polyfold.MPolyfold.isScDiffeoOn_fst_fibredProduct.{0, 0, 0},
    @Polyfold.MPolyfold.degIndex_fibredProduct_eq_snd.{0, 0, 0},
    @Polyfold.MPolyfold.degIndex_fibredProduct_eq_fst.{0, 0, 0},
    @Polyfold.MPolyfold.isTame_fibredProduct.{0, 0, 0},
    @Polyfold.MPolyfold.proposition_2_5_20.{0, 0, 0},
    @Polyfold.MPolyfold.proposition_2_5_20_of_isLocalScDiffeo.{0, 0, 0}⟩

/-- The last statement of Proposition 2.46 as in `proposition_2_5_20_of_isLocalScDiffeo`, with the
sub-M-polyfold proof and the paracompactness instance universally quantified. -/
def Last : Prop :=
  ∀ {X Y Z : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y]
    [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {P : MPolyfold X} {Q : MPolyfold Y}
    {S : MPolyfold Z} [ParacompactSpace (X × Y)] {f : X → Z} {g : Y → Z},
    P.IsLocalScDiffeo S f → Q.IsLocalScDiffeo S g →
    ∀ (hA : (P.prod Q).IsSubMPolyfold (MPolyfold.fibredProduct f g))
      [ParacompactSpace (MPolyfold.fibredProduct f g)] (a : MPolyfold.fibredProduct f g),
      ((P.prod Q).subPolyfold hA).degIndex a = P.degIndex (a : X × Y).1 ∧
        ((P.prod Q).subPolyfold hA).degIndex a = Q.degIndex (a : X × Y).2 ∧
        (P.IsTame → Q.IsTame → 2 * ((P.prod Q).subPolyfold hA).degIndex a =
          (P.prod Q).degIndex (a : X × Y))

/-- `A` without the statement that mentions the banned proof. -/
def A' : Prop :=
  (type_of% @Polyfold.MPolyfold.isSubMPolyfold_fibredProduct.{0, 0, 0}) ∧
    (type_of% @Polyfold.MPolyfold.degIndex_fibredProduct_eq_snd.{0, 0, 0}) ∧
    (type_of% @Polyfold.MPolyfold.isTame_fibredProduct.{0, 0, 0}) ∧ Last

theorem A_to_A' : A → A' := by
  intro hA
  obtain ⟨hsub, -, -, hdsnd, -, htame, -, hlast⟩ := hA
  refine ⟨hsub, hdsnd, htame, ?_⟩
  intro X Y Z _ _ _ _ _ _ _ _ _ P Q S _ f g hf hg hA _ a
  exact hlast hf hg a

theorem A'_to_B : A' → B := by
  intro hA X Y Z _ _ _ _ _ _ _ _ _ _ P Q S f g hf hg
  obtain ⟨hsub, hdsnd, htame, hlast⟩ := hA
  have hA' := hsub hf hg
  have hpc : ParacompactSpace (MPolyfold.fibredProduct f g) :=
    (MPolyfold.isClosed_fibredProduct hf.continuous
      (continuousOn_univ.1 hg.continuousOn)).isClosedEmbedding_subtypeVal.paracompactSpace
  refine ⟨hA', fun hQ => ⟨hA', hpc, htame hA' hf hg hQ, fun p => hdsnd hA' hf hg p⟩,
    fun hg' hP hQ => ⟨hA', hpc, fun p => ?_⟩⟩
  obtain ⟨h1, h2, h3⟩ := hlast hf hg' hA' p
  exact ⟨h3 hP hQ, h1, h2⟩

theorem A_to_B : A → B := fun h => A'_to_B (A_to_A' h)

/-- `B` gives `isSubMPolyfold_fibredProduct`. -/
theorem B_to_sub (hB : B) : type_of% @Polyfold.MPolyfold.isSubMPolyfold_fibredProduct.{0, 0, 0} := by
  intro X Y Z _ _ _ _ _ _ _ _ _ P Q S _ f g hf hg
  exact (hB X Y Z P Q S f g hf hg).1

/-- `B` gives `isTame_fibredProduct`. -/
theorem B_to_tame (hB : B) : type_of% @Polyfold.MPolyfold.isTame_fibredProduct.{0, 0, 0} := by
  intro X Y Z _ _ _ _ _ _ _ _ _ P Q S _ f g _ hA hf hg hQ
  obtain ⟨-, h2, -⟩ := hB X Y Z P Q S f g hf hg
  obtain ⟨hA', hpc, htame, -⟩ := h2 hQ
  exact htame

#rt_check RoundTrip.V2_53.A'_to_B [Polyfold.MPolyfold.isSubMPolyfold_fibredProduct,
  Polyfold.MPolyfold.isScDiffeoOn_snd_fibredProduct, Polyfold.MPolyfold.isScDiffeoOn_fst_fibredProduct,
  Polyfold.MPolyfold.degIndex_fibredProduct_eq_snd, Polyfold.MPolyfold.degIndex_fibredProduct_eq_fst,
  Polyfold.MPolyfold.isTame_fibredProduct, Polyfold.MPolyfold.proposition_2_5_20,
  Polyfold.MPolyfold.proposition_2_5_20_of_isLocalScDiffeo]
-- `A_to_B` itself cannot pass `#rt_check`/`#rt_check_soft`: its binder type `A` contains the banned
-- `isSubMPolyfold_fibredProduct` in the statement of `proposition_2_5_20_of_isLocalScDiffeo` (not in a
-- proof).  `A_to_B = A'_to_B ∘ A_to_A'`, where `A_to_A'` is a projection; the check is run on
-- `A'_to_B`, which takes all of its content from the hypothesis `A'`.
#rt_check RoundTrip.V2_53.B_to_tame [Polyfold.MPolyfold.isSubMPolyfold_fibredProduct,
  Polyfold.MPolyfold.isScDiffeoOn_snd_fibredProduct, Polyfold.MPolyfold.isScDiffeoOn_fst_fibredProduct,
  Polyfold.MPolyfold.degIndex_fibredProduct_eq_snd, Polyfold.MPolyfold.degIndex_fibredProduct_eq_fst,
  Polyfold.MPolyfold.isTame_fibredProduct, Polyfold.MPolyfold.proposition_2_5_20,
  Polyfold.MPolyfold.proposition_2_5_20_of_isLocalScDiffeo]
#rt_check RoundTrip.V2_53.B_to_sub [Polyfold.MPolyfold.isSubMPolyfold_fibredProduct,
  Polyfold.MPolyfold.isScDiffeoOn_snd_fibredProduct, Polyfold.MPolyfold.isScDiffeoOn_fst_fibredProduct,
  Polyfold.MPolyfold.degIndex_fibredProduct_eq_snd, Polyfold.MPolyfold.degIndex_fibredProduct_eq_fst,
  Polyfold.MPolyfold.isTame_fibredProduct, Polyfold.MPolyfold.proposition_2_5_20,
  Polyfold.MPolyfold.proposition_2_5_20_of_isLocalScDiffeo]

end RoundTrip.V2_53
