import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_3

/-! Round trip for V8_3 (Theorem 8.1.1 = 2017 Theorem 8.1: the tangent ep-groupoid `T(X, 𝐗)`).

The listed definitions `tangentGroupoidStr`, `tangentEpGroupoid`, `tangentProjFunctor`,
`liftOne` are vocabulary; `A` is the conjunction of the types of `EpGroupoid.theorem_8_1` and
`EpGroupoid.theorem_8_1_tame`, universes at `0` (the tangent spaces are then in `Type 1`).
`theorem_8_1` identifies the M-polyfolds and structure maps of the project's `tangentEpGroupoid`
(all `rfl` except the (8.5) clause) and the maps of `tangentProjFunctor`; that `(TX, T𝐗)` *is* an
ep-groupoid and `(p, 𝐩)` a functor is carried by the definitions themselves (their proof fields,
Lemmas 8.2–8.7), not by the theorem's type.

* `A → B`: `G` is the groupoid of `tangentEpGroupoid`.  B's structure maps: `rfl`, the unit by the
  project lemmas `tBase_tUnit`, `tSrc_tUnit`, the composition by `theorem_8_1`'s `comp = tComp`
  (B's `tCompB` is `tComp` by `rfl`).  B's Definition 7.3 for `G` with `TX`, `T𝐗` is read off the
  fields of `tangentEpGroupoid` exactly as in V7_3 (`IsProperMap` gives B's "continuous with compact
  preimages"; B's existential sub-M-polyfold data is the project's `isSubMPolyfold_fibredProduct`
  with its paracompactness instances).  The functor clauses: base points of `Ts`, `Tt`, `Tu` are
  the project lemmas `levelVal_tangentProj_tSrc/tTgt`, `tBase_tUnit`, the composition clause is
  `theorem_8_1`'s (8.5) clause, sc-smoothness of `p` into `X¹` is Part I's `tangentProj_isScSmooth`.
  Tameness is `theorem_8_1_tame` (`EpGroupoid.IsTame` is `PObj.IsTame`).
* `B → A`: all clauses of `theorem_8_1` but (8.5) are `rfl`; (8.5) — `k ∘ h` lies over
  `p k ∘ p h` and `Ts(k ∘ h) = Ts h` — follows from B's `G`: its composition is `tCompB = tComp`
  on composable pairs, B's functor clause gives the base point and `G.src_comp` the source.
  `theorem_8_1_tame` is B's tameness clause. -/

namespace RoundTrip.V8_3
open Polyfold

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.theorem_8_1.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.theorem_8_1_tame.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.theorem_8_1.{0}, @Polyfold.EpGroupoid.theorem_8_1_tame.{0}⟩

/-! ### `A → B` -/

theorem A_to_B : A → B := by
  rintro ⟨h81, htame⟩ Obj Mor _ _ _ _ _ _ X
  obtain ⟨-, -, -, -, hcomp, -, -, hspec, -, -⟩ := h81 X
  refine ⟨X.isScSmoothMap_src, X.isScSmoothMap_tgt, X.isScSmoothMap_inv,
    ⟨X.tangentEpGroupoid.toGroupoidStr, rfl, rfl, fun k h _ => congrFun (congrFun hcomp k) h,
      fun a => ⟨X.tBase_tUnit a, X.tSrc_tUnit a⟩, rfl, ?_, fun k => X.levelVal_tangentProj_tSrc k,
      fun k => X.levelVal_tangentProj_tTgt k, fun k h hkh => (hspec k h hkh).1,
      fun a => X.tBase_tUnit a, X.PObj.tangentProj_isScSmooth, X.PMor.tangentProj_isScSmooth⟩,
    htame X⟩
  -- Definition 7.3 for `(TX, T𝐗)`, from the fields of `tangentEpGroupoid`
  refine ⟨X.tangentEpGroupoid.isLocalScDiffeo_src, X.tangentEpGroupoid.isLocalScDiffeo_tgt,
    X.tangentEpGroupoid.isScSmoothMap_unit, X.tangentEpGroupoid.isScSmoothMap_inv,
    fun x => ?_, ?_⟩
  · obtain ⟨V, hV, hxV, hp⟩ := X.tangentEpGroupoid.exists_isProperMap x
    exact ⟨V, hV, hxV, hp.continuous, fun K hK => hp.isCompact_preimage hK⟩
  · let i1 := MPolyfold.paracompactSpace_prod X.tangentEpGroupoid.PMor X.tangentEpGroupoid.PMor
    let i2 := (X.tangentEpGroupoid.PMor.prod X.tangentEpGroupoid.PMor).paracompactSpace_subtype
      (MPolyfold.fibredProduct X.tangentEpGroupoid.src X.tangentEpGroupoid.tgt)
    exact ⟨i1, MPolyfold.isSubMPolyfold_fibredProduct X.tangentEpGroupoid.isLocalScDiffeo_src
      X.tangentEpGroupoid.isScSmoothMap_tgt, i2, X.tangentEpGroupoid.isScSmoothComp⟩

/-! ### `B → A` -/

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X
    obtain ⟨_, _, _, ⟨G, hGs, hGt, hGc, -, -, -, -, -, hfc, -, -, -⟩, -⟩ := hB Obj Mor X
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun k h hkh => ?_, rfl, rfl⟩
    have hkh' : X.tSrc k = X.tTgt h := hkh
    have hG : G.src k = G.tgt h := by rw [hGs, hGt]; exact hkh'
    have hc : G.comp k h = X.tComp k h := hGc k h hkh'
    refine ⟨?_, ?_⟩
    · change X.tBase (X.tComp k h) = X.comp (X.tBase k) (X.tBase h)
      rw [← hc]
      exact hfc k h hG
    · change X.tSrc (X.tComp k h) = X.tSrc h
      have h1 := G.src_comp k h hG
      rw [hc, hGs] at h1
      exact h1
  · intro Obj Mor _ _ _ _ _ _ X hX
    exact (hB Obj Mor X).2.2.2.2 hX

#rt_check RoundTrip.V8_3.A_to_B [Polyfold.EpGroupoid.theorem_8_1,
  Polyfold.EpGroupoid.theorem_8_1_tame]
#rt_check RoundTrip.V8_3.B_to_A [Polyfold.EpGroupoid.theorem_8_1,
  Polyfold.EpGroupoid.theorem_8_1_tame]
#rt_overlap RoundTrip.V8_3.B_to_A [Polyfold.EpGroupoid.theorem_8_1,
  Polyfold.EpGroupoid.theorem_8_1_tame]

end RoundTrip.V8_3
