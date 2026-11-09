import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_4

/-! Round trip for V8_4 (Lemma 8.1.2 = 2017 Lemma 8.1: the composition of `T𝐗` is `Tm`).

`A` is the conjunction of the types of `EpGroupoid.lemma_8_1`, `tComp_eq_tangentMapOn`,
`tangentMapOn_srcInv_tSrc`, `mem_tangentPreimage_tgt` and (Chapter 7's) `isScSmoothCompSheet`,
universes at `0`.  The two sides state Lemma 8.1 in different forms:

* `A` (the form of the text's proof): for a sheet `s : W → V` with inverse `σ` and
  `g(φ') = m(σ(t φ'), φ')` (sc-smooth on `t⁻¹(V)`, condition (4) in sheet form), `k ∘ h = Tg(h)`
  for composable `k, h` with `k` over `W`; the project does not prove the identification
  `T(𝐗 ₛ×ₜ 𝐗) = T𝐗 _{Ts}×_{Tt} T𝐗`.
* `B` (the statement): that identification, `v ↦ (Tpr₁ v, Tpr₂ v)` being a bijection of
  `T(𝐗 ₛ×ₜ 𝐗)` (Part I's tangent of the fibred-product sub-M-polyfold) onto the composable pairs,
  and `Tm v = (Tpr₁ v) ∘ (Tpr₂ v)`.

The bridge between them is `tm_eq_tg`: on the open part `U = {(ψ, φ) | ψ ∈ W, t φ ∈ V}` of the
fibred product, `m = g ∘ pr₂` (since `ψ = σ(s ψ) = σ(t φ)`), so `Tm v = Tg(Tpr₂ v)` by the chain
rule on open sets (`tangentMapOn_tangentMap`, `tangentMapOn_congr`, `tangentMapOn_eq_tangentMap`).

* `A → B`: the witnesses are the project's (`isSubMPolyfold_fibredProduct`, the paracompactness
  instances, `isScSmoothComp` for `m`, `isScSmoothMap_fst/snd ∘ subPolyfold_inclusion` for the
  projections).  The bijection: maps-to is the chain rule for `s ∘ pr₁ = t ∘ pr₂`; injectivity is
  that `pr₂` is an sc-diffeomorphism near each point of the fibred product
  (`isScDiffeoOn_snd_fibredProduct`, whose tangent `IsScDiffeoOn.tangentMap` is injective there);
  surjectivity takes `v = (Tpr₂|TU)⁻¹(h)` (`h` over `t⁻¹(V)` by the hypothesis'
  `mem_tangentPreimage_tgt`) and gets `Tpr₁ v = k` from fibre injectivity `tangent_ext` (V8_1).
  `Tm v = (Tpr₁ v) ∘ (Tpr₂ v)` is `tm_eq_tg` followed by the hypothesis' `tComp_eq_tangentMapOn`
  (with the hypothesis' sheet form of (4) for `g`); the base point and `Ts` of `Tm v` are the chain
  rule.
* `B → A`: `tComp_eq_tangentMapOn` (and the second clause of `lemma_8_1`) from B: B's surjectivity
  gives `v` over the composable pair `(k, h)`, B gives `Tm v = k ∘ h`, and `tm_eq_tg` gives
  `Tm v = Tg(h)`.  The sheet form of (4) is B's sc-smoothness of `m` through Chapter 7's
  `isScSmoothComp_iff_sheet`.  `tangentMapOn_srcInv_tSrc` (`Tσ(Ts k) = k` on a sheet) and
  `mem_tangentPreimage_tgt` are statements about a sheet of `s` only, not consequences of B: they
  are re-proved outright (one line each, `IsScDiffeoOn.tangentMap`, `src_tBase_eq`); the other
  clauses of `lemma_8_1` are `tComp_spec` (V8_1).

**The no-peeking check.**  The banned `isScSmoothCompSheet` occurs inside the *statements* of
`lemma_8_1` and `tComp_eq_tangentMapOn` (as the proof argument of `tangentMapOn`), hence inside
the value of `A`, so `#rt_check` fails for every proof term that mentions `A` (`A_self` below).
Both directions are therefore proved through `A'`, which is `A` with that proof argument replaced
by `sheet'` (re-proved from the field `isScSmoothComp`); `A = A'` is `rfl` (proof irrelevance), and
`A_to_B := A'_to_B`, `B_to_A := B_to_A'` are stated point-free, so that no proof term contains
`isScSmoothCompSheet`.  Both then pass the official `#rt_check` with all five theorems.
-/

namespace RoundTrip.V8_4
open Polyfold Set

/-- The project's statement (universes at `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpGroupoid.lemma_8_1.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tComp_eq_tangentMapOn.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.tangentMapOn_srcInv_tSrc.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.mem_tangentPreimage_tgt.{0}) ∧
  (type_of% @Polyfold.EpGroupoid.isScSmoothCompSheet.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpGroupoid.lemma_8_1.{0}, @Polyfold.EpGroupoid.tComp_eq_tangentMapOn.{0},
    @Polyfold.EpGroupoid.tangentMapOn_srcInv_tSrc.{0},
    @Polyfold.EpGroupoid.mem_tangentPreimage_tgt.{0},
    @Polyfold.EpGroupoid.isScSmoothCompSheet.{0}⟩

section Glue

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-- Condition (4) in sheet form, re-proved from the field `isScSmoothComp` (Chapter 7's route);
used only as a proof term inside `A'`. -/
theorem sheet' : IsScSmoothCompSheet X.PObj X.PMor X.src X.tgt X.comp :=
  (isScSmoothComp_iff_sheet _ _).1 X.isScSmoothComp

/-- `IsScDiffeoOn.isScSmoothOn_inv`'s statement-level use, as in `A`. -/
theorem srcInv_tSrc' {σ : Obj → Mor} {W : Set Mor} {V : Set Obj}
    (hd : X.PMor.IsScDiffeoOn X.PObj X.src σ W V) {k : X.PMor.TangentSpace} (hk : X.tBase k ∈ W) :
    MPolyfold.tangentMapOn hd.isScSmoothOn_inv (X.tSrc k) = k :=
  (hd.tangentMap X.isScSmoothMap_src).left_inv k hk

variable [ParacompactSpace (Mor × Mor)]
  {hF : (X.PMor.prod X.PMor).IsSubMPolyfold (MPolyfold.fibredProduct X.src X.tgt)}
  [ParacompactSpace ↥(MPolyfold.fibredProduct X.src X.tgt)]

/-- **The bridge**: on the part of `𝐗 ₛ×ₜ 𝐗` over a sheet `W` of `s`, `Tm = Tg ∘ Tpr₂`,
`g(φ') = m(σ(t φ'), φ')`. -/
theorem tm_eq_tg
    (hm : ((X.PMor.prod X.PMor).subPolyfold hF).IsScSmoothMap X.PMor
      (fun p => X.comp p.1.1 p.1.2))
    (h₂ : ((X.PMor.prod X.PMor).subPolyfold hF).IsScSmoothMap X.PMor (fun p => p.1.2))
    {σ : Obj → Mor} {W : Set Mor} {V : Set Obj} (hd : X.PMor.IsScDiffeoOn X.PObj X.src σ W V)
    (hg : X.PMor.IsScSmoothOn X.PMor (fun ψ => X.comp (σ (X.tgt ψ)) ψ) (X.tgt ⁻¹' V))
    (v : ((X.PMor.prod X.PMor).subPolyfold hF).TangentSpace)
    (hv : (((X.PMor.prod X.PMor).subPolyfold hF).levelVal 1
      (((X.PMor.prod X.PMor).subPolyfold hF).tangentProj v)).1.1 ∈ W) :
    MPolyfold.tangentMap hm v = MPolyfold.tangentMapOn hg (MPolyfold.tangentMap h₂ v) := by
  set b := ((X.PMor.prod X.PMor).subPolyfold hF).levelVal 1
    (((X.PMor.prod X.PMor).subPolyfold hF).tangentProj v)
  let U' : Set ↥(MPolyfold.fibredProduct X.src X.tgt) := Subtype.val ⁻¹' (W ×ˢ (X.tgt ⁻¹' V))
  have hW : IsOpen W := hd.isScSmoothOn.isOpen
  have hV : IsOpen V := hd.isScSmoothOn_inv.isOpen
  have hU' : IsOpen U' := (hW.prod (hV.preimage X.continuous_tgt)).preimage continuous_subtype_val
  have hmaps : MapsTo (fun p : ↥(MPolyfold.fibredProduct X.src X.tgt) => p.1.2) U'
      (X.tgt ⁻¹' V) := fun p hp => hp.2
  have hvU : v ∈ ((X.PMor.prod X.PMor).subPolyfold hF).tangentPreimage U' := by
    refine ⟨hv, ?_⟩
    have hb2 : X.src b.1.1 = X.tgt b.1.2 := b.2
    change X.tgt b.1.2 ∈ V
    rw [← hb2]
    exact hd.mapsTo hv
  rw [MPolyfold.tangentMapOn_tangentMap hg h₂ hU' hmaps hvU]
  have hc := MPolyfold.tangentMapOn_congr (hg.comp (h₂.mono hU' (subset_univ _)) hmaps)
    (hm.mono hU' (subset_univ _)) hU' subset_rfl subset_rfl ?_ hvU
  · rw [hc, MPolyfold.tangentMapOn_eq_tangentMap hm _ hvU]
  · intro p hp
    have hp2 : X.src p.1.1 = X.tgt p.1.2 := p.2
    change X.comp (σ (X.tgt p.1.2)) p.1.2 = X.comp p.1.1 p.1.2
    rw [← hp2, hd.left_inv _ hp.1]

/-- The chain rule for `s ∘ pr₁ = t ∘ pr₂`: `(Tpr₁ v, Tpr₂ v)` is composable. -/
theorem composable_pr
    (h₁ : ((X.PMor.prod X.PMor).subPolyfold hF).IsScSmoothMap X.PMor (fun p => p.1.1))
    (h₂ : ((X.PMor.prod X.PMor).subPolyfold hF).IsScSmoothMap X.PMor (fun p => p.1.2))
    (v : ((X.PMor.prod X.PMor).subPolyfold hF).TangentSpace) :
    X.tSrc (MPolyfold.tangentMap h₁ v) = X.tTgt (MPolyfold.tangentMap h₂ v) :=
  MPolyfold.tangentMap_tangentMap_comm X.isScSmoothMap_src h₁ X.isScSmoothMap_tgt h₂
    (funext fun p => p.2) v

/-- The chain rule for `s ∘ m = s ∘ pr₂`. -/
theorem tSrc_tm
    (hm : ((X.PMor.prod X.PMor).subPolyfold hF).IsScSmoothMap X.PMor
      (fun p => X.comp p.1.1 p.1.2))
    (h₂ : ((X.PMor.prod X.PMor).subPolyfold hF).IsScSmoothMap X.PMor (fun p => p.1.2))
    (v : ((X.PMor.prod X.PMor).subPolyfold hF).TangentSpace) :
    X.tSrc (MPolyfold.tangentMap hm v) = X.tSrc (MPolyfold.tangentMap h₂ v) :=
  MPolyfold.tangentMap_tangentMap_comm X.isScSmoothMap_src hm X.isScSmoothMap_src h₂
    (funext fun p => X.src_comp _ _ p.2) v

theorem tBase_pr₁
    (h₁ : ((X.PMor.prod X.PMor).subPolyfold hF).IsScSmoothMap X.PMor (fun p => p.1.1))
    (v : ((X.PMor.prod X.PMor).subPolyfold hF).TangentSpace) :
    X.tBase (MPolyfold.tangentMap h₁ v) = (((X.PMor.prod X.PMor).subPolyfold hF).levelVal 1
      (((X.PMor.prod X.PMor).subPolyfold hF).tangentProj v)).1.1 :=
  X.tBase_tangentMap h₁ v

theorem tBase_pr₂
    (h₂ : ((X.PMor.prod X.PMor).subPolyfold hF).IsScSmoothMap X.PMor (fun p => p.1.2))
    (v : ((X.PMor.prod X.PMor).subPolyfold hF).TangentSpace) :
    X.tBase (MPolyfold.tangentMap h₂ v) = (((X.PMor.prod X.PMor).subPolyfold hF).levelVal 1
      (((X.PMor.prod X.PMor).subPolyfold hF).tangentProj v)).1.2 :=
  X.tBase_tangentMap h₂ v

end Glue

/-- `A` with the proof argument `isScSmoothCompSheet` of its statements replaced by `sheet'`. -/
def A' : Prop :=
  (∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    {σ : Obj → Mor} {W : Set Mor} {V : Set Obj} (hd : X.PMor.IsScDiffeoOn X.PObj X.src σ W V)
    {k h : X.PMor.TangentSpace}, X.tSrc k = X.tTgt h → X.tBase k ∈ W →
      MPolyfold.tangentMapOn hd.isScSmoothOn_inv (X.tTgt h) = k ∧
        X.tComp k h = MPolyfold.tangentMapOn (sheet' X σ W V hd) h ∧
          X.tBase (X.tComp k h) = X.comp (X.tBase k) (X.tBase h) ∧
            X.tSrc (X.tComp k h) = X.tSrc h) ∧
  (∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {σ : Obj → Mor} {W : Set Mor} {V : Set Obj} (hd : X.PMor.IsScDiffeoOn X.PObj X.src σ W V)
    {k h : X.PMor.TangentSpace}, X.tSrc k = X.tTgt h → X.tBase k ∈ W →
      X.tComp k h = MPolyfold.tangentMapOn (sheet' X σ W V hd) h) ∧
  (∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {σ : Obj → Mor} {W : Set Mor} {V : Set Obj} (hd : X.PMor.IsScDiffeoOn X.PObj X.src σ W V)
    {k : X.PMor.TangentSpace}, X.tBase k ∈ W →
      MPolyfold.tangentMapOn hd.isScSmoothOn_inv (X.tSrc k) = k) ∧
  (∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
    {σ : Obj → Mor} {W : Set Mor} {V : Set Obj}, X.PMor.IsScDiffeoOn X.PObj X.src σ W V →
      ∀ {k h : X.PMor.TangentSpace}, X.tSrc k = X.tTgt h → X.tBase k ∈ W →
        h ∈ X.PMor.tangentPreimage (X.tgt ⁻¹' V)) ∧
  (∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
      IsScSmoothCompSheet X.PObj X.PMor X.src X.tgt X.comp)

/-- `A` and `A'` are the same proposition (proof irrelevance). -/
theorem A_eq_A' : A = A' := rfl

/-! ### `A → B` -/

theorem A'_to_B (hA : A') : B := by
  obtain ⟨-, h2, -, h4, h5⟩ := hA
  intro Obj Mor _ _ _ _ _ _ X
  let i1 := MPolyfold.paracompactSpace_prod X.PMor X.PMor
  have hF := MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src X.isScSmoothMap_tgt
  let i2 := (X.PMor.prod X.PMor).paracompactSpace_subtype (MPolyfold.fibredProduct X.src X.tgt)
  have hval := MPolyfold.subPolyfold_inclusion_isScSmooth hF
  have h₁ : ((X.PMor.prod X.PMor).subPolyfold hF).IsScSmoothMap X.PMor (fun p => p.1.1) :=
    (MPolyfold.isScSmoothMap_fst X.PMor X.PMor).comp hval
  have h₂ : ((X.PMor.prod X.PMor).subPolyfold hF).IsScSmoothMap X.PMor (fun p => p.1.2) :=
    (MPolyfold.isScSmoothMap_snd X.PMor X.PMor).comp hval
  have hm : ((X.PMor.prod X.PMor).subPolyfold hF).IsScSmoothMap X.PMor
      (fun p => X.comp p.1.1 p.1.2) := X.isScSmoothComp
  refine ⟨X.isScSmoothMap_src, X.isScSmoothMap_tgt, i1, hF, i2, hm, h₁, h₂, ⟨?_, ?_, ?_⟩,
    fun v => ?_⟩
  · -- maps to the composable pairs
    exact fun v _ => composable_pr X h₁ h₂ v
  · -- injective: `Tpr₂` is injective near every point
    intro v _ w _ hvw
    have e1 : MPolyfold.tangentMap h₁ v = MPolyfold.tangentMap h₁ w := congrArg Prod.fst hvw
    have e2 : MPolyfold.tangentMap h₂ v = MPolyfold.tangentMap h₂ w := congrArg Prod.snd hvw
    set bv := ((X.PMor.prod X.PMor).subPolyfold hF).levelVal 1
      (((X.PMor.prod X.PMor).subPolyfold hF).tangentProj v)
    set bw := ((X.PMor.prod X.PMor).subPolyfold hF).levelVal 1
      (((X.PMor.prod X.PMor).subPolyfold hF).tangentProj w)
    have hb : bv = bw := by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · rw [← tBase_pr₁ X h₁ v, ← tBase_pr₁ X h₁ w, e1]
      · rw [← tBase_pr₂ X h₂ v, ← tBase_pr₂ X h₂ w, e2]
    obtain ⟨W, V, σ, hW, hd⟩ := X.isLocalScDiffeo_src bv.1.1
    have hT := (MPolyfold.isScDiffeoOn_snd_fibredProduct hF hd X.isScSmoothMap_tgt bv).tangentMap h₂
    have hbv2 : X.src bv.1.1 = X.tgt bv.1.2 := bv.2
    let U' : Set ↥(MPolyfold.fibredProduct X.src X.tgt) := Subtype.val ⁻¹' (W ×ˢ (X.tgt ⁻¹' V))
    have hvU : v ∈ ((X.PMor.prod X.PMor).subPolyfold hF).tangentPreimage U' := by
      refine ⟨hW, ?_⟩
      change X.tgt bv.1.2 ∈ V
      rw [← hbv2]
      exact hd.mapsTo hW
    have hwU : w ∈ ((X.PMor.prod X.PMor).subPolyfold hF).tangentPreimage U' := by
      change bw ∈ U'
      rw [← hb]
      exact hvU
    rw [← hT.left_inv v hvU, ← hT.left_inv w hwU]
    exact congrArg _ e2
  · -- surjective onto the composable pairs
    rintro ⟨k, h⟩ hkh
    change X.tSrc k = X.tTgt h at hkh
    obtain ⟨W, V, σ, hk, hd⟩ := X.isLocalScDiffeo_src (X.tBase k)
    let a₀ : ↥(MPolyfold.fibredProduct X.src X.tgt) := ⟨(X.tBase k, X.tBase h), X.src_tBase_eq hkh⟩
    have hT := (MPolyfold.isScDiffeoOn_snd_fibredProduct hF hd X.isScSmoothMap_tgt a₀).tangentMap h₂
    have hh : h ∈ X.PMor.tangentPreimage (X.tgt ⁻¹' V) := h4 hd hkh hk
    have hvU := hT.mapsTo_inv hh
    have h2v := hT.right_inv h hh
    set v := MPolyfold.tangentMapOn
      (MPolyfold.isScDiffeoOn_snd_fibredProduct hF hd X.isScSmoothMap_tgt a₀).isScSmoothOn_inv h
    refine ⟨v, mem_univ _, Prod.ext ?_ h2v⟩
    change MPolyfold.tangentMap h₁ v = k
    set bv := ((X.PMor.prod X.PMor).subPolyfold hF).levelVal 1
      (((X.PMor.prod X.PMor).subPolyfold hF).tangentProj v)
    have hbW : bv.1.1 ∈ W := hvU.1
    have hbv2 : X.src bv.1.1 = X.tgt bv.1.2 := bv.2
    have hb2 : bv.1.2 = X.tBase h := by
      rw [← tBase_pr₂ X h₂ v]
      exact congrArg X.tBase h2v
    refine X.tangent_ext ?_ ?_
    · rw [tBase_pr₁ X h₁ v, ← hd.left_inv _ hbW, ← hd.left_inv _ hk, hbv2, hb2,
        X.src_tBase_eq hkh]
    · rw [composable_pr X h₁ h₂ v, hkh]
      exact congrArg X.tTgt h2v
  · -- `Tm v = (Tpr₁ v) ∘ (Tpr₂ v)`, its base point and its `Ts`
    have hkh := composable_pr X h₁ h₂ v
    obtain ⟨W, V, σ, hk, hd⟩ := X.isLocalScDiffeo_src (X.tBase (MPolyfold.tangentMap h₁ v))
    have hv : (((X.PMor.prod X.PMor).subPolyfold hF).levelVal 1
        (((X.PMor.prod X.PMor).subPolyfold hF).tangentProj v)).1.1 ∈ W := by
      rw [← tBase_pr₁ X h₁ v]
      exact hk
    have e := tm_eq_tg X hm h₂ hd (h5 X σ W V hd) v hv
    have e2 : ∀ hg : X.PMor.IsScSmoothOn X.PMor (fun ψ => X.comp (σ (X.tgt ψ)) ψ) (X.tgt ⁻¹' V),
        X.tComp (MPolyfold.tangentMap h₁ v) (MPolyfold.tangentMap h₂ v) =
          MPolyfold.tangentMapOn hg (MPolyfold.tangentMap h₂ v) := fun _ => h2 hd hkh hk
    refine ⟨e.trans (e2 (h5 X σ W V hd)).symm, ?_, tSrc_tm X hm h₂ v⟩
    change X.tBase (MPolyfold.tangentMap hm v) =
      X.comp (X.tBase (MPolyfold.tangentMap h₁ v)) (X.tBase (MPolyfold.tangentMap h₂ v))
    rw [X.tBase_tangentMap hm, tBase_pr₁ X h₁ v, tBase_pr₂ X h₂ v]

theorem A_to_B : A → B := A'_to_B

/-! ### `B → A` -/

theorem B_to_A' (hB : B) : A' := by
  -- `tComp_eq_tangentMapOn`, from B
  have hcomp : ∀ {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
      [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
      {σ : Obj → Mor} {W : Set Mor} {V : Set Obj} (hd : X.PMor.IsScDiffeoOn X.PObj X.src σ W V)
      {k h : X.PMor.TangentSpace}, X.tSrc k = X.tTgt h → X.tBase k ∈ W →
        X.tComp k h = MPolyfold.tangentMapOn (sheet' X σ W V hd) h := by
    intro Obj Mor _ _ _ _ _ _ X σ W V hd k h hkh hk
    obtain ⟨hs, ht, i1, hF, i2, hm, h₁, h₂, hbij, hmain⟩ := hB Obj Mor X
    obtain ⟨v, -, hv⟩ := hbij.surjOn (show (k, h) ∈ {q : X.PMor.TangentSpace × X.PMor.TangentSpace |
      MPolyfold.tangentMap hs q.1 = MPolyfold.tangentMap ht q.2} from hkh)
    have e1 : MPolyfold.tangentMap h₁ v = k := congrArg Prod.fst hv
    have e2 : MPolyfold.tangentMap h₂ v = h := congrArg Prod.snd hv
    have hvW : (((X.PMor.prod X.PMor).subPolyfold hF).levelVal 1
        (((X.PMor.prod X.PMor).subPolyfold hF).tangentProj v)).1.1 ∈ W := by
      rw [← tBase_pr₁ X h₁ v, e1]
      exact hk
    have e := tm_eq_tg X hm h₂ hd (sheet' X σ W V hd) v hvW
    rw [e2] at e
    have hmv := (hmain v).1
    rw [e1, e2] at hmv
    exact hmv.symm.trans e
  refine ⟨fun X σ W V hd k h hkh hk => ⟨?_, hcomp hd hkh hk, X.tComp_spec hkh⟩, hcomp,
    fun hd k hk => srcInv_tSrc' _ hd hk, ?_, ?_⟩
  · -- `T(s|W)⁻¹(Tt h) = k`: a statement about a sheet of `s`, re-proved
    rw [← hkh]
    exact srcInv_tSrc' X hd hk
  · -- `mem_tangentPreimage_tgt`: a statement about a sheet of `s`, re-proved
    intro Obj Mor _ _ _ _ _ _ X σ W V hd k h hkh hk
    change X.tgt (X.tBase h) ∈ V
    rw [← X.src_tBase_eq hkh]
    exact hd.mapsTo hk
  · -- condition (4) in sheet form, from B's sc-smoothness of `m`
    intro Obj Mor _ _ _ _ _ _ X
    obtain ⟨_, _, _, _, _, hm, -⟩ := hB Obj Mor X
    exact (isScSmoothComp_iff_sheet X.isLocalScDiffeo_src X.isScSmoothMap_tgt).1 hm

theorem B_to_A : B → A := B_to_A'

/-! ### The checks -/

/-- `A → A`: the official checks fail on it, because the value of `A` contains
`isScSmoothCompSheet` (inside the statements of `lemma_8_1`, `tComp_eq_tangentMapOn`); this is why
the directions are proved through `A'` and stated point-free. -/
theorem A_self : A → A := id

/--
error: rt_check_soft FAIL: RoundTrip.V8_4.A_self uses [Polyfold.EpGroupoid.isScSmoothCompSheet]
-/
#guard_msgs in
#rt_check_soft RoundTrip.V8_4.A_self [Polyfold.EpGroupoid.lemma_8_1,
  Polyfold.EpGroupoid.tComp_eq_tangentMapOn, Polyfold.EpGroupoid.tangentMapOn_srcInv_tSrc,
  Polyfold.EpGroupoid.mem_tangentPreimage_tgt, Polyfold.EpGroupoid.isScSmoothCompSheet]

#rt_check RoundTrip.V8_4.A_to_B [Polyfold.EpGroupoid.lemma_8_1,
  Polyfold.EpGroupoid.tComp_eq_tangentMapOn, Polyfold.EpGroupoid.tangentMapOn_srcInv_tSrc,
  Polyfold.EpGroupoid.mem_tangentPreimage_tgt, Polyfold.EpGroupoid.isScSmoothCompSheet]
#rt_check RoundTrip.V8_4.B_to_A [Polyfold.EpGroupoid.lemma_8_1,
  Polyfold.EpGroupoid.tComp_eq_tangentMapOn, Polyfold.EpGroupoid.tangentMapOn_srcInv_tSrc,
  Polyfold.EpGroupoid.mem_tangentPreimage_tgt, Polyfold.EpGroupoid.isScSmoothCompSheet]
#rt_overlap RoundTrip.V8_4.B_to_A [Polyfold.EpGroupoid.lemma_8_1,
  Polyfold.EpGroupoid.tComp_eq_tangentMapOn, Polyfold.EpGroupoid.tangentMapOn_srcInv_tSrc,
  Polyfold.EpGroupoid.mem_tangentPreimage_tgt, Polyfold.EpGroupoid.isScSmoothCompSheet]

end RoundTrip.V8_4
