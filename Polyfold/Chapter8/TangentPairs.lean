import Polyfold.Chapter8.TangentFibred

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §8.1,
**Remark 8.1.10**, pp. 364–365 (2017: Remark 8.1, pp. 264–265): the M-polyfold structure on the
set of pairs `(Tφ, a)` for which `G` is an sc-diffeomorphism, and the triples `(a, Tφ, b)`
(row V8.12).

# The second description of the morphisms of `T(X, 𝐗)`

## The text, paraphrased

(Remark 8.1.10) `G : T𝐗 → {(Tφ, a) | φ ∈ 𝐗₁, a ∈ T_{s(φ)}X}`, `G(φ, h) = (Tφ, Ts(h))`, is a
bijection, and the right-hand side can be given an M-polyfold structure for which `G` is an
sc-diffeomorphism.  The pairs `(Tφ, a)` can be identified with the triples `(a, Tφ, b)`,
`b = Tφ(a)`.

## What is formalized (namespace `Polyfold.EpGroupoid`)

* `TangentPairs X`: the set of pairs `(φ, a)`, `φ ∈ 𝐗¹`, `a ∈ TX` with `s(φ) = p(a)` (so
  `a ∈ T_{s(φ)}X`), the fibred product `𝐗¹ _{s}×_{p} TX`; `tangentPairsPolyfold`: its M-polyfold
  structure, a sub-M-polyfold of `𝐗¹ × TX` (Proposition 2.5.20, `s : 𝐗¹ → X¹` being a local
  sc-diffeomorphism).
* `remarkGInto : T𝐗 → TangentPairs`, `v ↦ (p(v), Ts(v))` (`remarkG` of `TangentEp.lean` with
  values in the M-polyfold of pairs), `tangentPairsEquiv` (the bijection), and
  **`remark_8_1_10_scDiffeo`**: `G` is an sc-diffeomorphism `T𝐗 → 𝐗¹ _{s}×_{p} TX`.
* `remarkTriple v = (Ts v, p(v), Tt v)` and **`remark_8_1_10_triples`**: it is injective, with
  range the triples `(a, φ, b)`, `φ ∈ 𝐗₁`, `a ∈ T_{s(φ)}X`, `b = Tφ(a)` (Chapter 7's
  `tangentMor`).

## The reading

As in row V8.12, the first entry `Tφ` of a pair is recorded by its label `φ` (as a bare map the
assignment is not injective, `remark_8_1_10_not_injective`).  The M-polyfold structure is the
natural one of the fibred product; `G` is an sc-diffeomorphism for it, since `G` commutes with
the local sc-diffeomorphisms `Ts : T𝐗 → TX` and `π₂ : 𝐗¹ _{s}×_{p} TX → TX`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u v w

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y}
  {Z : Type w} [TopologicalSpace Z] [T2Space Z] [ParacompactSpace Z] {S : MPolyfold Z}

/-- For a local sc-diffeomorphism `f` and an sc-smooth `g`, the projection `π₂ : X _f×_g Y → Y`
is a local sc-diffeomorphism (the proof of Proposition 2.5.20). -/
theorem isLocalScDiffeo_sndOfFibredProduct [ParacompactSpace (X × Y)] {f : X → Z} {g : Y → Z}
    [ParacompactSpace (fibredProduct f g)] (hf : P.IsLocalScDiffeo S f)
    (hg : Q.IsScSmoothMap S g) :
    (subPolyfold (isSubMPolyfold_fibredProduct hf hg)).IsLocalScDiffeo Q
      (fun a => (a : X × Y).2) := by
  intro a
  obtain ⟨W, V, σ, haW, hd⟩ := hf a.1.1
  refine ⟨_, _, _, ?_, isScDiffeoOn_snd_fibredProduct (isSubMPolyfold_fibredProduct hf hg) hd hg a⟩
  refine ⟨haW, ?_⟩
  change g a.1.2 ∈ V
  rw [← show f a.1.1 = g a.1.2 from a.2]
  exact hd.mapsTo haW

end MPolyfold

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- The pairs `(φ, a)` with `φ ∈ 𝐗¹` and `a ∈ T_{s(φ)}X`: the fibred product `𝐗¹ _{s}×_{p} TX`
(Remark 8.1.10's set `{(Tφ, a)}`, with `Tφ` recorded by `φ`). -/
def TangentPairs : Type (max u 1) :=
  ↥(MPolyfold.fibredProduct X.liftSrc X.PObj.tangentProj)

instance : TopologicalSpace X.TangentPairs :=
  inferInstanceAs (TopologicalSpace ↥(MPolyfold.fibredProduct X.liftSrc X.PObj.tangentProj))

instance : T2Space X.TangentPairs :=
  inferInstanceAs (T2Space ↥(MPolyfold.fibredProduct X.liftSrc X.PObj.tangentProj))

include X in
theorem paracompactSpace_pairsProd : ParacompactSpace (X.PMor.Level 1 × X.PObj.TangentSpace) :=
  MPolyfold.paracompactSpace_prod X.PMor.shift X.PObj.tangentPolyfold

theorem paracompactSpace_tangentPairs :
    ParacompactSpace ↥(MPolyfold.fibredProduct X.liftSrc X.PObj.tangentProj) :=
  letI := X.paracompactSpace_pairsProd
  (X.PMor.shift.prod X.PObj.tangentPolyfold).paracompactSpace_subtype _

instance : ParacompactSpace X.TangentPairs := X.paracompactSpace_tangentPairs

/-- The M-polyfold structure on the pairs `(Tφ, a)` (Remark 8.1.10): the sub-M-polyfold
`𝐗¹ _{s}×_{p} TX` of `𝐗¹ × TX`. -/
def tangentPairsPolyfold : MPolyfold X.TangentPairs :=
  letI := X.paracompactSpace_pairsProd
  letI := X.paracompactSpace_tangentPairs
  MPolyfold.subPolyfold
    (MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_liftSrc
      X.PObj.tangentProj_isScSmooth)

/-- `(φ, a) ↦ a` is a local sc-diffeomorphism `𝐗¹ _{s}×_{p} TX → TX`. -/
theorem isLocalScDiffeo_tangentPairs_snd :
    X.tangentPairsPolyfold.IsLocalScDiffeo X.PObj.tangentPolyfold
      (fun b : X.TangentPairs => b.1.2) :=
  letI := X.paracompactSpace_pairsProd
  letI := X.paracompactSpace_tangentPairs
  MPolyfold.isLocalScDiffeo_sndOfFibredProduct X.isLocalScDiffeo_liftSrc
    X.PObj.tangentProj_isScSmooth

/-- **`G : (φ, h) ↦ (Tφ, Ts(h))`** of Remark 8.1.10, with values in the M-polyfold of pairs. -/
def remarkGInto (v : X.PMor.TangentSpace) : X.TangentPairs :=
  ⟨(X.PMor.tangentProj v, X.tSrc v),
    MPolyfold.level_ext (X.levelVal_tangentProj_tSrc v).symm⟩

theorem remarkGInto_fst (v : X.PMor.TangentSpace) :
    X.PMor.levelVal 1 (X.remarkGInto v).1.1 = (X.remarkG v).1 := rfl

theorem remarkGInto_snd (v : X.PMor.TangentSpace) : (X.remarkGInto v).1.2 = (X.remarkG v).2 := rfl

theorem bijective_remarkGInto : Bijective X.remarkGInto := by
  refine ⟨fun v w h => ?_, fun b => ?_⟩
  · have h' := congrArg Subtype.val h
    exact X.tangent_ext (congrArg (X.PMor.levelVal 1) (congrArg Prod.fst h')) (congrArg Prod.snd h')
  · have hb : X.liftSrc b.1.1 = X.PObj.tangentProj b.1.2 := b.2
    obtain ⟨v, hv, hva⟩ := X.exists_tSrc_eq (φ := b.1.1) (a := b.1.2)
      (by rw [← hb]; rfl)
    exact ⟨v, Subtype.ext (Prod.ext hv hva)⟩

/-- The bijection `G` of Remark 8.1.10. -/
def tangentPairsEquiv : X.PMor.TangentSpace ≃ X.TangentPairs :=
  Equiv.ofBijective X.remarkGInto X.bijective_remarkGInto

theorem continuous_remarkGInto : Continuous X.remarkGInto :=
  Continuous.subtype_mk
    ((X.PMor.tangentProj_isScSmooth.continuousOn.mono (subset_univ _) |>
      continuousOn_univ.1).prodMk X.continuous_tSrc) _

/-- **2021 Remark 8.1.10, p. 365 (2017: Remark 8.1, p. 265): `G` is an sc-diffeomorphism** from
`T𝐗` onto the M-polyfold `𝐗¹ _{s}×_{p} TX` of pairs `(Tφ, a)`, `φ ∈ 𝐗₁`, `a ∈ T_{s(φ)}X`. -/
theorem remark_8_1_10_scDiffeo :
    X.PMor.tangentPolyfold.IsScDiffeoOn X.tangentPairsPolyfold X.remarkGInto
      X.tangentPairsEquiv.symm univ univ :=
  (MPolyfold.isLocalScDiffeo_of_comp_eq X.isLocalScDiffeo_tSrc
    X.isLocalScDiffeo_tangentPairs_snd X.continuous_remarkGInto
    fun _ => rfl).isScDiffeoOn_of_bijective X.tangentPairsEquiv fun _ => rfl

/-! ### The triples `(a, Tφ, b)` -/

/-- The triple `(a, Tφ, b) = (Ts(h), φ, Tt(h))` of a morphism `(φ, h)` of `T𝐗`. -/
def remarkTriple (v : X.PMor.TangentSpace) :
    X.PObj.TangentSpace × Mor × X.PObj.TangentSpace := (X.tSrc v, X.tBase v, X.tTgt v)

/-- **2021 Remark 8.1.10, p. 365: the triples `(a, Tφ, b)`, `b = Tφ(a)`.**  The assignment
`(φ, h) ↦ (Ts(h), φ, Tt(h))` is injective, its third entry is `Tφ` of the first, and its range is
the set of triples `(a, φ, b)` with `φ ∈ 𝐗₁`, `a ∈ T_{s(φ)}X` and `b = Tφ(a)`; the triple of a
composition `(ψ, k) ∘ (φ, h)` is `(Ts(h), ψ ∘ φ, Tt(k))`. -/
theorem remark_8_1_10_triples :
    Injective X.remarkTriple ∧
      (∀ v, (X.remarkTriple v).2.2 = X.tangentMor (X.remarkTriple v).2.1 (X.remarkTriple v).1) ∧
      range X.remarkTriple = {q | q.2.1 ∈ X.PMor.levelSet 1 ∧
        X.PObj.levelVal 1 (X.PObj.tangentProj q.1) = X.src q.2.1 ∧
        q.2.2 = X.tangentMor q.2.1 q.1} ∧
      (∀ k h, X.tSrc k = X.tTgt h → X.remarkTriple (X.tComp k h) =
        (X.tSrc h, X.comp (X.tBase k) (X.tBase h), X.tTgt k)) := by
  refine ⟨fun v w h => X.tangent_ext (congrArg (fun q => q.2.1) h) (congrArg Prod.fst h),
    fun v => (X.tangentMor_tSrc v).symm, ?_, fun k h hkh => ?_⟩
  · ext ⟨a, φ, b⟩
    constructor
    · rintro ⟨v, hv⟩
      simp only [remarkTriple, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact ⟨X.tBase_mem_levelSet v, X.levelVal_tangentProj_tSrc v, (X.tangentMor_tSrc v).symm⟩
    · rintro ⟨hφ, ha, hb⟩
      obtain ⟨v, hv, hva⟩ := X.exists_tSrc_eq' hφ ha
      refine ⟨v, ?_⟩
      have hv' : X.tBase v = φ := hv
      have hva' : X.tSrc v = a := hva
      have hb' : b = X.tangentMor φ a := hb
      rw [hb', ← hv', ← hva', X.tangentMor_tSrc]
      rfl
  · rw [remarkTriple, X.tBase_tComp hkh, X.tSrc_tComp hkh, (X.lemma_8_1_3 hkh).2]

end EpGroupoid

end Polyfold
