import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_63

set_option maxSynthPendingDepth 3

/-!
Round trip for V10_63 (2021 Proposition 10.1.10, p. 470; 2017: Proposition 10.4).

The item lists four theorems; `A` is the conjunction of their types, universes at `0`:
`proposition_10_1_10_one` (for equivalences `F, G : X → Y` with `F.orbitMap = G.orbitMap` and
`X` with (LR): inside every open `O ∋ x` a natural representation `R` with an sc-smooth
`α : R.U → 𝐘`, `α_z : F(z) → G(z)`), `proposition_10_1_10_one_of_isLR_right` (the same with (LR)
for `Y` instead), `proposition_10_1_10_two` (`F.tangent.orbitMap = G.tangent.orbitMap`, under the
hypotheses of (1)), and the witness `proposition_10_1_10_hypotheses` (point ep-groupoid).

`B`: for `X, Y : EP.{0}` both with (LR), equivalences `F, G` with `|F(x)| = |G(x)|` for all `x`:
(1) every `x` has some natural representation `R` and `α` as above (no smallness), and
(2) `|TF(p)| = |TG(p)|` for every tangent vector `p`.

* `A_to_B`: `F.orbitMap = G.orbitMap` from the pointwise hypothesis (quotient induction,
  `orbitMap_π`); (1) is `proposition_10_1_10_one` with `O = univ`; (2) is
  `proposition_10_1_10_two` evaluated at `|p|`.
* `B_to_A`: `B` needs (LR) on both sides; from (LR) on one side the other follows by the non-item
  Proposition 10.1.9 (`EpFunctor.proposition_10_1_9`).  The smallness `R.U ⊆ O` of A's (1) is
  recovered by shrinking: Theorem 7.1.13 (`theorem_7_1`) gives a natural representation inside
  `O ∩ R.U`, on which `α` is still sc-smooth.  (2) by quotient induction.  The witness is
  re-proved outright (`IsEquivalence.id`, `isSLR_pointEP`).
-/

namespace RoundTrip.V10_63
open Polyfold Set Function

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  type_of% @Polyfold.EpFunctor.proposition_10_1_10_one.{0, 0} ∧
  type_of% @Polyfold.EpFunctor.proposition_10_1_10_one_of_isLR_right.{0, 0} ∧
  type_of% @Polyfold.EpFunctor.proposition_10_1_10_two.{0, 0} ∧
  type_of% @Polyfold.EquivalenceLRExamples.proposition_10_1_10_hypotheses

theorem A_holds : A :=
  ⟨@Polyfold.EpFunctor.proposition_10_1_10_one.{0, 0},
    @Polyfold.EpFunctor.proposition_10_1_10_one_of_isLR_right.{0, 0},
    @Polyfold.EpFunctor.proposition_10_1_10_two.{0, 0},
    Polyfold.EquivalenceLRExamples.proposition_10_1_10_hypotheses⟩

theorem A_to_B : A → B := by
  rintro ⟨h1, -, h2, -⟩ X Y F G hX _ hF hG hFG
  have hFG' : F.orbitMap = G.orbitMap := by
    funext q
    induction q using Quotient.inductionOn with | h x => ?_
    exact (F.orbitMap_π x).trans ((hFG x).trans (G.orbitMap_π x).symm)
  refine ⟨fun x => ?_, fun p => ?_⟩
  · obtain ⟨R, -, α, hα, hst⟩ := h1 hF hG hFG' hX x isOpen_univ (mem_univ x)
    exact ⟨R, α, hα, hst⟩
  · have e := congrFun (h2 hF hG hFG' hX) (X.X.tangentEpGroupoid.π p)
    rwa [F.tangent.orbitMap_π, G.tangent.orbitMap_π] at e

section FromB

variable (hB : B)
include hB

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

/-- `B` for ep-groupoids given by their spaces. -/
theorem B' {F G : EpFunctor X Y} (hF : F.IsEquivalence) (hG : G.IsEquivalence)
    (hFG : F.orbitMap = G.orbitMap) (hX : X.IsLR) :
    (∀ x : Obj, ∃ (R : X.NaturalRep x) (α : Obj → Mor'),
        X.PObj.IsScSmoothOn Y.PMor α R.U ∧
        ∀ z ∈ R.U, Y.src (α z) = F.obj z ∧ Y.tgt (α z) = G.obj z) ∧
    (∀ p : X.PObj.TangentSpace,
        Y.tangentEpGroupoid.π (F.tangent.obj p) = Y.tangentEpGroupoid.π (G.tangent.obj p)) :=
  hB (EP.mk Obj Mor X) (EP.mk Obj' Mor' Y) F G hX
    ((EpFunctor.proposition_10_1_9 hF).1 hX) hF hG fun x => by
      rw [← F.orbitMap_π, ← G.orbitMap_π, hFG]

theorem one' {F G : EpFunctor X Y} (hF : F.IsEquivalence) (hG : G.IsEquivalence)
    (hFG : F.orbitMap = G.orbitMap) (hX : X.IsLR) (x : Obj) {O : Set Obj} (hO : IsOpen O)
    (hxO : x ∈ O) :
    ∃ R : X.NaturalRep x, R.U ⊆ O ∧ ∃ α : Obj → Mor', X.PObj.IsScSmoothOn Y.PMor α R.U ∧
      ∀ z ∈ R.U, Y.src (α z) = F.obj z ∧ Y.tgt (α z) = G.obj z := by
  obtain ⟨R, α, hα, hst⟩ := (B' hB hF hG hFG hX).1 x
  -- shrink `R.U` into `O` (Theorem 7.1.13)
  obtain ⟨R', hR'⟩ := X.theorem_7_1 x (hO.inter R.isOpen_U) ⟨hxO, R.mem_U⟩
  exact ⟨R', fun u hu => (hR' hu).1, α, hα.mono R'.isOpen_U fun u hu => (hR' hu).2,
    fun z hz => hst z (hR' hz).2⟩

end FromB

theorem B_to_A : B → A := by
  intro hB
  refine ⟨fun hF hG hFG hX x _ hO hxO => one' hB hF hG hFG hX x hO hxO,
    fun hF hG hFG hY x _ hO hxO =>
      one' hB hF hG hFG ((EpFunctor.proposition_10_1_9 hF).2 hY) x hO hxO,
    fun {Obj Mor} _ _ _ _ _ _ {Obj' Mor'} _ _ _ _ _ _ {X Y F G} hF hG hFG hX => ?_,
    ⟨EpFunctor.IsEquivalence.id _, EpFunctor.IsEquivalence.id _, rfl,
      EpGroupoid.Examples.isSLR_pointEP 0⟩⟩
  funext q
  induction q using Quotient.inductionOn with | h v => ?_
  change F.tangent.orbitMap (X.tangentEpGroupoid.π v) = G.tangent.orbitMap
    (X.tangentEpGroupoid.π v)
  rw [F.tangent.orbitMap_π, G.tangent.orbitMap_π]
  exact (B' hB hF hG hFG hX).2 v

#rt_check RoundTrip.V10_63.A_to_B [Polyfold.EpFunctor.proposition_10_1_10_one,
  Polyfold.EpFunctor.proposition_10_1_10_one_of_isLR_right,
  Polyfold.EpFunctor.proposition_10_1_10_two,
  Polyfold.EquivalenceLRExamples.proposition_10_1_10_hypotheses]
#rt_check RoundTrip.V10_63.B_to_A [Polyfold.EpFunctor.proposition_10_1_10_one,
  Polyfold.EpFunctor.proposition_10_1_10_one_of_isLR_right,
  Polyfold.EpFunctor.proposition_10_1_10_two,
  Polyfold.EquivalenceLRExamples.proposition_10_1_10_hypotheses]
#rt_overlap RoundTrip.V10_63.B_to_A [Polyfold.EpFunctor.proposition_10_1_10_one,
  Polyfold.EpFunctor.proposition_10_1_10_one_of_isLR_right,
  Polyfold.EpFunctor.proposition_10_1_10_two,
  Polyfold.EquivalenceLRExamples.proposition_10_1_10_hypotheses]

end RoundTrip.V10_63
