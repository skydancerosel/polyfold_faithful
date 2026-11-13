import Polyfold.Chapter15.BoundaryPerturbation
import Polyfold.Chapter15.ControllingPairs
import Polyfold.Chapter5.CylinderPerturbation2021

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.3, p. 693:
**Remark 15.3.6**, second sentence (2017: Remark 15.6).

# General position gives good position, branch by branch

## The text, paraphrased

(Remark 15.3.6) If `(f, Λ)` is in general position (Definition 15.3.5), then at every
`x ∈ supp(Λ ∘ f)` the linearization `T(f,Λ)(x)` is onto, and if `x ∈ ∂X`, `T(f,Λ)(x)` is in good
position, even in general position.

## What is formalized (namespace `Polyfold.SBLocalization`)

* `isGeneralPositionGerm_subRestrict` (the chart step): for a branch `s` of a local sc⁺-section
  structure on an open `O`, a tame chart `c` of `W` centred at `x` with domain in `O`, and
  `f(x) = s(x)`, if the intrinsic operator `(f − s)'(x)` of §15.1 is onto `W_x` already on the
  reduced tangent space `T^R_xX` (Definition 2.5.8, in the chart `c.φ`), then the section
  `(f − s)|O` of `W|O` is in general position at `x` in Part I's sense (Definition 5.3.9,
  `IsGeneralPositionGerm`).  Proof: in the transported chart of `W|O` the operator is
  `D((f̂ − ŝ) ∘ r)(0)` (`scDeriv_restrictTo_subRestrict`); onto on `T^R_0O` gives
  `ker Lin(0) + T^R_0O = T_0O`, and Part I's chart criterion `isGeneralPositionGerm_of_sup_eq`
  concludes (the argument of `isGeneralPositionGerm_of_restrict`).
* **`remark_15_3_6_goodPosition_hyp`**: if `(f, Λ)` is in general position, then at every
  `x ∈ supp(Λ ∘ f)` it is in good position (Definition 15.2.4, `IsGoodPositionAt`), and every
  branch `f − sᵢ` through `f(x)` of every local section structure is in general position in
  Part I's sense (`IsGeneralPositionGerm` of `(f − sᵢ)|O`); good position follows by Part I's
  Lemma 5.26 (`IsGeneralPositionGerm.isGoodPositionGermTame`).

## Reading

* "Good position" is L's Definition 15.2.4 (`IsGoodPositionAt`), and "even in general position"
  is Part I's Definition 5.3.9 for each branch `(f − sᵢ)|O`, the M-polyfold notion of which
  Definition 15.3.5 is "a natural extension".
* The statement holds at every point of the support, on the boundary or not.
* As in §15.2 the section has germ data in tame charts (`IsScFredholmSectionTame`, the inherited
  Part I hypothesis of Theorem 3.6.8); it supplies the tame chart centred at `x`.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15

variable {A : SEP.{u}}

/-! ### The chart step -/

/-- **The reduced operator in a chart**: if `toIntr c hx L` is onto `W_x` on `T^R_xX`, then every
`k` of the fibre `K` over `φ(x)` is `L w` for some `w ∈ T^R_zO ∩ T_zO`, `z` the level-`1` point
over `φ(x)`. -/
theorem exists_reduced_preimage {c : StrongBundleChart A.X.PObj A.P} {x : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source) {L : c.φ.model.E 0 →L[ℝ] c.F 0} {n : ℕ}
    {Wq : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hred : Surjective ((toIntr c hx L).domRestrict (reducedTangentFiber c.isChart hx T)))
    {k : c.F 0} (hk : (c.φ (A.X.PObj.levelVal 1 x), k) ∈ c.K) :
    ∃ w ∈ reducedTangentSpaceWith (c.isRetraction.baseRetraction c.relOpen) T
        (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)),
      w ∈ rangeS (scDeriv c.U (r c.R) (levelLift c.φ 1 (A.X.PObj.levelVal 1 x))) ∧ L w = k := by
  classical
  set R := c.isRetraction.baseRetraction c.relOpen with hR
  have hR' : R.retract = c.φ '' c.φ.source := by rw [c.base_retract, c.φ.image_source]
  obtain ⟨v, rfl⟩ := c.mem_range_fiberLin hx hk
  by_cases hrange : ∀ α, chartOp c hx L α ∈ LinearMap.range (c.fiberLin hx)
  · obtain ⟨⟨α, hα⟩, he⟩ := hred v
    have he' : toIntr c hx L α = v := he
    have h1 := fiberLin_toIntr c hx hrange α
    rw [he', chartOp_apply] at h1
    refine ⟨(tangentFiberEquiv c.isChart hx α : c.φ.model.E 0), ?_,
      (c.mem_tangentFiberModel_iff_rangeS hx _).1 (tangentFiberEquiv c.isChart hx α).2, h1.symm⟩
    have := (mem_reducedTangentFiber_iff c.isChart hx T subset_rfl c.φ.isOpen_source hx R hR').1
      hα
    rwa [fiberCoord_eq_coe] at this
  · have h0 : toIntr c hx L = 0 := by rw [toIntr, dif_neg hrange]
    obtain ⟨⟨α, _⟩, he⟩ := hred v
    have hv : v = 0 := by
      have he' : toIntr c hx L α = v := he
      rw [h0] at he'
      exact he'.symm
    subst hv
    exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, by rw [map_zero, map_zero]⟩

set_option maxHeartbeats 1600000 in
-- the assembly of Part I's chart criterion in the transported chart
/-- **The chart step of Remark 15.3.6**: a branch `s` (an sc⁺-section on the open `O`) through
`f(x)`, a tame chart `c` of `W` centred at `x` with domain in `O`, and the intrinsic operator
`(f − s)'(x) = toIntr c hx (D((f̂ − ŝ) ∘ r)(z))` onto `W_x` on `T^R_xX`: then `(f − s)|O` is in
general position at `x` (Part I's Definition 5.3.9 on `W|O`). -/
theorem isGeneralPositionGerm_subRestrict {f : A.Obj → A.W}
    (hft : A.B.IsScFredholmSectionTame f) {s : A.Obj → A.W} {O : Set A.Obj} (hO : IsOpen O)
    (hs : IsScPlusSectionOn A s O) {c : StrongBundleChart A.X.PObj A.P}
    (hc : A.B.IsTameChart c) (hsub : c.φ.source ⊆ O) {x : A.X.PObj.Level 1}
    (hx : A.X.PObj.levelVal 1 x ∈ c.φ.source) (hφ0 : c.φ (A.X.PObj.levelVal 1 x) = 0)
    (hfs : f (A.X.PObj.levelVal 1 x) = s (A.X.PObj.levelVal 1 x)) {n : ℕ} {Wq : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod Wq))
    (hT : c.φ.model.C = T 0 ⁻¹' quadrant n Wq 0)
    (hred : Surjective ((toIntr c hx (subDeriv c f s
      (levelLift c.φ 1 (A.X.PObj.levelVal 1 x)))).domRestrict (reducedTangentFiber c.isChart hx T)))
    [Nonempty O] [ParacompactSpace O]
    [ParacompactSpace (pullbackSpace A.P (Subtype.val : O → A.Obj))] :
    (A.B.restrictOpen hO).IsGeneralPositionGerm (subRestrict (O := O) f s hft.isScSmooth.1)
      ⟨A.X.PObj.levelVal 1 x, hsub hx⟩ := by
  classical
  set y := A.X.PObj.levelVal 1 x with hy
  set g := subRestrict (O := O) f s hft.isScSmooth.1 with hg
  have hgO := isScFredholmSectionTame_subRestrict hO hft hs
  set q₀ := g ⟨y, hsub hx⟩ with hq₀
  set c' := c.restrictTo A.B.continuous hO hsub q₀ with hc'
  have hc'T : (A.B.restrictOpen hO).IsTameChart c' :=
    ⟨restrictOpen_isChart_restrictTo hO hc.1 hsub q₀, hc.2⟩
  have hxc' : (⟨y, hsub hx⟩ : O) ∈ c'.φ.source := hx
  have hφ0' : c'.φ ⟨y, hsub hx⟩ = 0 := hφ0
  -- the level-`1` point over `φ(y)` is `0`
  have hz0 : levelLift c.φ 1 y = 0 := by
    apply c.φ.model.E.toBase_injective 1
    rw [A.X.PObj.toBase_levelLift c.isChart hx (levelVal_mem x), hφ0, map_zero]
  have hz : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) = c.φ y := by rw [map_zero, hφ0]
  have hzO : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ r c.R '' c.U := by
    rw [c.r_image, hz]; exact c.φ.mapsTo_model _ hx
  have hzU : c.φ.model.E.toBase 1 (0 : c.φ.model.E 1) ∈ c.U := mem_U_of_mem_O c.isRetraction hzO
  have hD : scDeriv c.U (c'.principal g ∘ r c.R) 0 = subDeriv c f s 0 :=
    scDeriv_restrictTo_subRestrict hO hft hs hc.1 hsub q₀ hzU
  set R' := c.isRetraction.baseRetraction c.relOpen with hR'
  -- `Lin(0)` is onto on `T^R_0O`
  have hkey : ∀ k, (c.φ y, k) ∈ c.K → ∃ w ∈ reducedTangentSpaceWith R' T 0,
      ∃ hw : w ∈ rangeS (scDeriv c.U (r c.R) 0),
        linAt c'.U c'.R (c'.principal g) 0 ⟨w, hw⟩ = k := by
    intro k hk
    obtain ⟨w, hwR, hw, hwk⟩ := exists_reduced_preimage hx T hred hk
    rw [hz0] at hwR hw hwk
    refine ⟨w, hwR, hw, ?_⟩
    rw [linAt_apply]
    exact (congrArg (fun L : c.φ.model.E 0 →L[ℝ] c.F 0 => L w) hD).trans hwk
  have hsurj : ∀ k, (c'.φ ⟨y, hsub hx⟩, k) ∈ c'.K →
      ∃ v, linAt c'.U c'.R (c'.principal g) 0 v = k := by
    intro k hk
    obtain ⟨w, -, hw, hwk⟩ := hkey k hk
    exact ⟨⟨w, hw⟩, hwk⟩
  -- `ker Lin(0) + T^R_0O = T_0O`
  have hy0 : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj)) g ⟨y, hsub hx⟩ := by
    rw [hg]
    unfold subRestrict
    rw [isZeroAt_restrictSection_iff]
    exact (isZeroAt_subSec_iff hft.isScSmooth.1 hs.1 (hsub hx)).2 hfs
  have hzO' : c'.φ.model.E.toBase 1 (0 : c'.φ.model.E 1) ∈ r c'.R '' c'.U := hzO
  have hsup : c'.linKer g 0 ⊔ reducedTangentSpaceWith R' T 0 =
      LinearMap.range (scDeriv R'.U R' 0 : c.φ.model.E 0 →ₗ[ℝ] c.φ.model.E 0) := by
    refine le_antisymm (sup_le (c'.linKer_le _ 0) inf_le_left) fun (v : c.φ.model.E 0) hv => ?_
    have hv' : v ∈ rangeS (scDeriv c.U (r c.R) 0) := hv
    set k := linAt c'.U c'.R (c'.principal g) 0 ⟨v, hv'⟩ with hkdef
    have hkρ : ρCLM c'.isRetraction hzU k = k :=
      rho_scDeriv_comp_r c'.relOpen c'.isRetraction
        (hgO.isScSmooth.isSc1_principal_comp_r hc'T.1)
        (fun x hx => c'.principal_mem_K hgO.isScSmooth.1 (c'.r_image ▸ hx)) hzO'
        (by rw [map_zero, ← hφ0']; exact (c'.isZeroAt_iff hgO.isScSmooth.1 hxc').1 hy0) v
    have hkK : (c.φ y, k) ∈ c.K := by
      have h1 := c.mem_K_ρ (c.φ.mapsTo_model _ hx) k
      have hkρ' : ρ c.R (c.φ.model.E.toBase 1 0) k = k := hkρ
      rw [hz] at hkρ'
      rwa [hkρ'] at h1
    obtain ⟨w, hwR, hw, hwk⟩ := hkey k hkK
    have hker : v - w ∈ c'.linKer g 0 := by
      refine (c'.mem_linKer_iff g 0 (v - w)).2 ⟨Submodule.sub_mem _ hv' hw, ?_⟩
      have := map_sub (linAt c'.U c'.R (c'.principal g) 0) ⟨v, hv'⟩ ⟨w, hw⟩
      rw [hwk, ← hkdef, sub_self] at this
      exact this
    have : v = (v - w) + w := by abel
    rw [this]
    exact Submodule.add_mem_sup hker hwR
  exact isGeneralPositionGerm_of_sup_eq hgO hy0 hc'T hxc' hφ0' T hT hsurj hsup

/-! ### Remark 15.3.6, second sentence -/

/-- **Every branch through `f(x)` is in general position** (Part I's Definition 5.3.9 for
`(f − sᵢ)|O`), at a point `x ∈ supp(Λ ∘ f)` where `(f, Λ)` is in general position
(Definition 15.3.5), for every local sc⁺-section structure `(sᵢ, σᵢ)` of `Λ` on an open `O ∋ x`.
`f` has germ data in tame charts (the inherited hypothesis of §15.2). -/
theorem isGeneralPositionGerm_branch {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ : A.W → ℚ≥0} (hgp : IsInGeneralPosition A f Λ)
    {O : Set A.Obj} (hO : IsOpen O) {k : ℕ} {s : Fin k → A.Obj → A.W} {σ : Fin k → ℚ≥0}
    (hrep : IsLocalRepOn A Λ O s σ) {x : A.Obj} (hxO : x ∈ O) (hpos : 0 < Λ (f x)) {i : Fin k}
    (hi : s i x = f x) [Nonempty O] [ParacompactSpace O]
    [ParacompactSpace (pullbackSpace A.P (Subtype.val : O → A.Obj))] :
    (A.B.restrictOpen hO).IsGeneralPositionGerm
      (subRestrict (O := O) f (s i) hft.isScSmooth.1) ⟨x, hxO⟩ := by
  classical
  have hxs : x ∈ A.X.PObj.smoothSet := mem_smoothSet_of_eq hft hO (hrep.2.1 i) hxO hi.symm
  have hx1 : x ∈ A.X.PObj.levelSet 1 := smoothSet_subset_levelSet 1 hxs
  set xl := A.X.PObj.levelMk 1 x hx1 with hxl
  have hxlv : A.X.PObj.levelVal 1 xl = x := A.X.PObj.levelVal_levelMk 1 x hx1
  obtain ⟨-, c₀, hc₀, hxc₀, hφ0, -⟩ := hft.germTame x hxs
  set c := c₀.restrictInter hO with hcdef
  have hc : A.B.IsTameChart c := hc₀.restrictInter hO
  have hsub : c.φ.source ⊆ O := c₀.restrictInter_source_subset hO
  have hxc : A.X.PObj.levelVal 1 xl ∈ c.φ.source := by rw [hxlv]; exact ⟨hxc₀, hxO⟩
  have hφ0c : c.φ (A.X.PObj.levelVal 1 xl) = 0 := by rw [hxlv]; exact hφ0
  obtain ⟨n, Wq, T, hT⟩ := c.φ.model.isPartialQuadrant
  let d : LocalLinData A Λ xl := ⟨O, hO, k, s, σ, hrep, c, hc.1, hsub, hxc⟩
  have hiv : s i (A.X.PObj.levelVal 1 xl) = f (A.X.PObj.levelVal 1 xl) := by rw [hxlv]; exact hi
  have hL : toIntr c hxc (subDeriv c f (s i) (levelLift c.φ 1 (A.X.PObj.levelVal 1 xl))) ∈
      (linearization f Λ xl).support := by
    rw [linearization_eq hf d]
    exact (mem_support_linSumIntr_iff hf.1.1.1 hrep.1 (fun j => (hrep.2.1 j).1) hsub hxc _).2
      ⟨i, hiv, rfl⟩
  have hposl : 0 < Λ (f (A.X.PObj.levelVal 1 xl)) := by rw [hxlv]; exact hpos
  have hred := hgp xl hposl _ hL c.φ c.isChart hxc n Wq T hT
  have h := isGeneralPositionGerm_subRestrict hft hO (hrep.2.1 i) hc hsub hxc hφ0c hiv.symm T hT
    hred
  exact h

/-- **Remark 15.3.6 (2017: Remark 15.6), p. 693, second sentence**, with the inherited
hypothesis that `f` has germ data in tame charts (`hft`, as in §15.2): if `(f, Λ)` is in general
position (Definition 15.3.5), then at every `x ∈ supp(Λ ∘ f)` it is in good position
(Definition 15.2.4), and, "even in general position", every branch `f − sᵢ` through `f(x)` of
every local sc⁺-section structure of `Λ` around `x` is in general position in Part I's sense
(Definition 5.3.9 for `(f − sᵢ)|O`).  The text states it for `x ∈ ∂X`; it holds at every point
of the support. -/
theorem remark_15_3_6_goodPosition_hyp {f : A.Obj → A.W} (hf : A.E.IsScFredholmSectionFunctor f)
    (hft : A.B.IsScFredholmSectionTame f) {Λ : A.W → ℚ≥0} (hΛ : IsScPlusMultisection A Λ)
    (hgp : IsInGeneralPosition A f Λ) {x : A.Obj} (hpos : 0 < Λ (f x)) :
    IsGoodPositionAt f Λ x ∧
      ∀ (O : Set A.Obj) (hO : IsOpen O) (hxO : x ∈ O) (k : ℕ) (s : Fin k → A.Obj → A.W)
        (σ : Fin k → ℚ≥0), IsLocalRepOn A Λ O s σ → ∀ i, s i x = f x →
        haveI : Nonempty O := ⟨⟨x, hxO⟩⟩
        haveI := A.X.PObj.paracompactSpace_subtype O
        haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
          (A.X.PObj.restrictOpen hO) A.B
        (A.B.restrictOpen hO).IsGeneralPositionGerm
          (subRestrict (O := O) f (s i) hft.isScSmooth.1) ⟨x, hxO⟩ := by
  have hall : ∀ (O : Set A.Obj) (hO : IsOpen O) (hxO : x ∈ O) (k : ℕ) (s : Fin k → A.Obj → A.W)
      (σ : Fin k → ℚ≥0), IsLocalRepOn A Λ O s σ → ∀ i, s i x = f x →
      haveI : Nonempty O := ⟨⟨x, hxO⟩⟩
      haveI := A.X.PObj.paracompactSpace_subtype O
      haveI := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
        (A.X.PObj.restrictOpen hO) A.B
      (A.B.restrictOpen hO).IsGeneralPositionGerm
        (subRestrict (O := O) f (s i) hft.isScSmooth.1) ⟨x, hxO⟩ := by
    intro O hO hxO k s σ hrep i hi
    have : Nonempty O := ⟨⟨x, hxO⟩⟩
    have := A.X.PObj.paracompactSpace_subtype O
    have := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
      (A.X.PObj.restrictOpen hO) A.B
    exact isGeneralPositionGerm_branch hf hft hgp hO hrep hxO hpos hi
  refine ⟨⟨hpos, ?_, ?_⟩, hall⟩
  · have hx1 := mem_levelSet_one_of_pos hf hΛ hpos
    refine ⟨hx1, fun L hL => hgp.surjective ?_ hL⟩
    rw [A.X.PObj.levelVal_levelMk]; exact hpos
  · obtain ⟨O, k, s, σ, hO, hxO, hrep⟩ := hΛ.exists_isLocalRepOn x
    refine ⟨O, hO, hxO, k, s, σ, hrep, fun i hi => ?_⟩
    have : Nonempty O := ⟨⟨x, hxO⟩⟩
    have := A.X.PObj.paracompactSpace_subtype O
    have := paracompactSpace_pullbackSpace (f := (Subtype.val : O → A.Obj))
      (A.X.PObj.restrictOpen hO) A.B
    have hg := hall O hO hxO k s σ hrep i hi
    have h0 : IsZeroAt (pullbackProj A.P (Subtype.val : O → A.Obj))
        (subRestrict (O := O) f (s i) hft.isScSmooth.1) ⟨x, hxO⟩ := by
      unfold subRestrict
      rw [isZeroAt_restrictSection_iff]
      exact (isZeroAt_subSec_iff hft.isScSmooth.1 (hrep.2.1 i).1 hxO).2 hi.symm
    exact ⟨hft.isScSmooth.1,
      hg.isGoodPositionGermTame (isScFredholmSectionTame_subRestrict hO hft (hrep.2.1 i)) h0⟩

end SBLocalization

end Polyfold
