import Polyfold.Chapter14.P3W5F6_FaceStructured
import Polyfold.Chapter2.CornerGerms
import Polyfold.Chapter2.SubMPolyfold

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §14.6, Definition 14.6.1,
p. 681 (2017: Definition 14.10): **the restriction `Λ̃_F|F'` is a structured sc⁺-multisection on
`W|(F ∩ F')`**, i.e. its sections are sc⁺ on the corner `F ∩ F'` (gap F6-2 of wave 5).  Numbers
and pages are the 2021 text's.

## What is formalized

* Local level: `IsScPlusOnCornerNear T C O K s x i j`: near `x`, the corner germ
  `O ∩ V ∩ {tᵢ = 0} ∩ {tⱼ = 0}` is an sc-retract and `s` restricted to it is an sc⁺-section.
  `IsScPlusOnFaceNear.isScPlusOnCornerNear`: in a tame local model, sc⁺ on the face germ
  `{tᵢ = 0}` at `x` gives sc⁺ on every corner germ `{tᵢ = tⱼ = 0}` at `x` (the corner germ is a
  retract by Part I's `corner_retraction`, and an sc-smooth map between retracts restricts to
  sub-retracts, `IsScSmoothRetractMap.mono_source`).
* `SBLocalization.IsCornerRelScPlusSectionOn A F F' s U` (**sc⁺-sections of `W|(F ∩ F')`**, read
  in the charts of `X` as `IsFaceRelScPlusSectionOn` is for `W|F`): in every tame strong bundle
  chart, at every point of `U`, on every corner germ `{tᵢ = tⱼ = 0}` whose face germ `{tᵢ = 0}`
  lies in `F` and `{tⱼ = 0}` lies in `F'`, the local representative is sc⁺.
* `IsFaceRelScPlusSectionOn.isCornerRelScPlusSectionOn` (from `F`) and
  `IsFaceRelScPlusSectionOn.isCornerRelScPlusSectionOn'` (from `F'`): sc⁺ relative to either face
  gives sc⁺ on the corner.
* `FaceStructuredTuple.restrictFace_isCornerRelScPlus`: the sections of `Λ̃_F|F'` are sc⁺
  relative to the corner `F ∩ F'`, so the restriction of Definition 14.6.1 is a structured
  sc⁺-multisection on `W|(F ∩ F')`; `isCornerRelScPlusSectionOn_fiberZero` (nonvacuity).
-/

set_option maxSynthPendingDepth 3

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u

section Local

variable {E F W : ScBanach} {n : ℕ}

/-- **sc⁺ on a corner germ**: near `x`, `O ∩ V ∩ {tᵢ = 0} ∩ {tⱼ = 0}` is an sc-retract and the
restriction of `s` to it is an sc⁺-section. -/
def IsScPlusOnCornerNear (T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)) (C O : Set (E 0))
    (K : Set (E 0 × F 0)) (s : E 0 → E 0 × F 1) (x : E 0) (i j : Fin n) : Prop :=
  ∃ V : Set (E 0), IsOpen V ∧ x ∈ V ∧
    IsScRetract E C (O ∩ V ∩ coordHyper T i ∩ coordHyper T j) ∧
    IsScPlusSection C (O ∩ V ∩ coordHyper T i ∩ coordHyper T j) K s

theorem IsScPlusOnCornerNear.symm {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)}
    {C O : Set (E 0)} {K : Set (E 0 × F 0)} {s : E 0 → E 0 × F 1} {x : E 0} {i j : Fin n}
    (h : IsScPlusOnCornerNear T C O K s x i j) : IsScPlusOnCornerNear T C O K s x j i := by
  obtain ⟨V, hV, hxV, hret, hsec⟩ := h
  have e : O ∩ V ∩ coordHyper T j ∩ coordHyper T i = O ∩ V ∩ coordHyper T i ∩ coordHyper T j := by
    ext z; simp only [mem_inter_iff]; tauto
  exact ⟨V, hV, hxV, e ▸ hret, e ▸ hsec⟩

/-- **From a face germ to a corner germ**: in a tame local model `(O, C, E)`, `C = T⁻¹(quadrant)`,
if `s` is sc⁺ on the face germ `{tᵢ = 0}` at `x`, then it is sc⁺ on the corner germ
`{tᵢ = tⱼ = 0}` at `x` for every `j` with `tⱼ(x) = 0`. -/
theorem IsScPlusOnFaceNear.isScPlusOnCornerNear
    {T : ScIso E ((ScBanach.const (Fin n → ℝ)).prod W)} {C O : Set (E 0)} {K : Set (E 0 × F 0)}
    {s : E 0 → E 0 × F 1} {x : E 0} {i j : Fin n} {R : ScRetraction E C}
    (hRO : R.retract = O) (hT : C = T 0 ⁻¹' quadrant n W 0) (hR : R.IsTameWith T) (hxO : x ∈ O)
    (hi : (T 0 x).1 i = 0) (hj : (T 0 x).1 j = 0) (h : IsScPlusOnFaceNear T C O K s x i) :
    IsScPlusOnCornerNear T C O K s x i j := by
  classical
  obtain ⟨V, hV, hxV, hret, hsec⟩ := h
  have hσ : ∀ k ∈ ({i, j} : Finset (Fin n)), (T 0 x).1 k = 0 := fun k hk => by
    rcases Finset.mem_insert.1 hk with rfl | hk
    · exact hi
    · rw [Finset.mem_singleton.1 hk]; exact hj
  obtain ⟨-, -, -, V', hV', hxV', S, -, -, hSret, -⟩ :=
    corner_retraction {i, j} hT hR (hRO ▸ hxO) hσ
  have e : (S.restrict hV).retract = O ∩ (V ∩ V') ∩ coordHyper T i ∩ coordHyper T j := by
    rw [S.restrict_retract, hSret, hRO]
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, coordHyper, Finset.mem_insert,
      Finset.mem_singleton, forall_eq_or_imp, forall_eq]
    tauto
  have hsub : O ∩ (V ∩ V') ∩ coordHyper T i ∩ coordHyper T j ⊆ O ∩ V ∩ coordHyper T i :=
    fun z hz => ⟨⟨hz.1.1.1, hz.1.1.2.1⟩, hz.1.2⟩
  refine ⟨V ∩ V', hV.inter hV', ⟨hxV, hxV'⟩, ⟨S.restrict hV, e⟩,
    ⟨fun z hz => hsec.fst_eq z (hsub hz), hsec.isScSmooth.mono_source hret hsub⟩⟩

end Local

namespace SBLocalization

open StrongBundle EpGroupoid

variable {A : SEP.{u}}

/-- **An sc⁺-section of `W|(F ∩ F')` near `U`, read in the charts of `X`** (Definition 14.6.1,
p. 681): `s` is a section over `U` with values in `W_{0,1}`, and in every tame strong bundle
chart, at every point `y ∈ U`, on every corner germ `{tᵢ = tⱼ = 0}` at `φ(y)` whose face germ
`{tᵢ = 0}` lies in `F` and `{tⱼ = 0}` lies in `F'` (the local model of the corner `F ∩ F'`), the
local representative is an sc⁺-section. -/
def IsCornerRelScPlusSectionOn (A : SEP.{u}) (F F' : Set A.Obj) (s : A.Obj → A.W)
    (U : Set A.Obj) : Prop :=
  (∀ x ∈ U, A.P (s x) = x ∧ s x ∈ A.B.oneSet) ∧
  ∀ c : StrongBundleChart A.X.PObj A.P, A.B.IsTameChart c →
    ∀ (n : ℕ) (W : ScBanach) (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
      c.φ.model.C = T 0 ⁻¹' quadrant n W 0 →
      ∀ x ∈ U ∩ c.φ.source, ∀ i ∈ zeroSet T (c.φ x), ∀ j ∈ zeroSet T (c.φ x),
        FaceGermIn c T F (c.φ x) i → FaceGermIn c T F' (c.φ x) j →
          IsScPlusOnCornerNear T c.φ.model.C c.φ.model.O c.K (localRepOne c s) (c.φ x) i j

theorem IsCornerRelScPlusSectionOn.mono {F F' : Set A.Obj} {s : A.Obj → A.W}
    {U U' : Set A.Obj} (h : IsCornerRelScPlusSectionOn A F F' s U) (hU' : U' ⊆ U) :
    IsCornerRelScPlusSectionOn A F F' s U' :=
  ⟨fun x hx => h.1 x (hU' hx), fun c hc n W T hT x hx i hi j hj hg hg' =>
    h.2 c hc n W T hT x ⟨hU' hx.1, hx.2⟩ i hi j hj hg hg'⟩

/-- The corner notion is symmetric in the two faces. -/
theorem IsCornerRelScPlusSectionOn.symm {F F' : Set A.Obj} {s : A.Obj → A.W} {U : Set A.Obj}
    (h : IsCornerRelScPlusSectionOn A F F' s U) : IsCornerRelScPlusSectionOn A F' F s U :=
  ⟨h.1, fun c hc n W T hT x hx i hi j hj hg hg' =>
    (h.2 c hc n W T hT x hx j hj i hi hg' hg).symm⟩

/-- **sc⁺ relative to `F` gives sc⁺ on the corner `F ∩ F'`.** -/
theorem IsFaceRelScPlusSectionOn.isCornerRelScPlusSectionOn {F : Set A.Obj} (F' : Set A.Obj)
    {s : A.Obj → A.W} {U : Set A.Obj} (h : IsFaceRelScPlusSectionOn A F s U) :
    IsCornerRelScPlusSectionOn A F F' s U := by
  refine ⟨h.1, fun c hc n W T hT x hx i hi j hj hg _ => ?_⟩
  have hRO := c.base_retract
  have hR := hc.isTame n W T hT
  exact (h.2 c hc n W T hT x hx i hi hg).isScPlusOnCornerNear hRO hT hR
    (c.φ.mapsTo_model x hx.2) ((mem_zeroSet T).1 hi) ((mem_zeroSet T).1 hj)

/-- **sc⁺ relative to `F'` gives sc⁺ on the corner `F ∩ F'`.** -/
theorem IsFaceRelScPlusSectionOn.isCornerRelScPlusSectionOn' (F : Set A.Obj) {F' : Set A.Obj}
    {s : A.Obj → A.W} {U : Set A.Obj} (h : IsFaceRelScPlusSectionOn A F' s U) :
    IsCornerRelScPlusSectionOn A F F' s U :=
  (h.isCornerRelScPlusSectionOn F).symm

/-- The zero section is sc⁺ on every corner, on every `U ⊆ ∂X`. -/
theorem isCornerRelScPlusSectionOn_fiberZero {F F' U : Set A.Obj}
    (hU : U ⊆ A.X.PObj.boundary) : IsCornerRelScPlusSectionOn A F F' (fiberZero A.P) U :=
  (isFaceRelScPlusSectionOn_fiberZero (F := F) hU).isCornerRelScPlusSectionOn F'

namespace FaceStructuredTuple

variable {F : Set A.Obj} {ι : IndexFamily A}

/-- **Definition 14.6.1, regularity**: the sections of `Λ̃_F|F'` are sc⁺-sections of
`W|(F ∩ F')` on the neighbourhoods `U(x) ∩ F ∩ F'` of the restriction (gap F6-2). -/
theorem restrictFace_isCornerRelScPlus (T : FaceStructuredTuple A F ι) (F' : Set A.Obj)
    (x : ↥(F ∩ F')) (i : ι.I x) :
    IsCornerRelScPlusSectionOn A F F' ((T.restrictFace F').s x i) ((T.restrictFace F').U x) :=
  (T.restrictFace_isFaceRelScPlus F' x i).isCornerRelScPlusSectionOn F'

end FaceStructuredTuple

end SBLocalization

end Polyfold
