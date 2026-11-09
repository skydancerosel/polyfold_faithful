import Polyfold.Chapter3.GermFilling
import Polyfold.Chapter3.StrongBundleSections
import Polyfold.Chapter3.FillerLinearization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
Definitions 3.1.6 and 3.1.11 (preprint 3.6 and 3.11): **the text's germ fillings against the project's filled versions** in a
strong bundle chart.

# Germ fillings and whole-chart filled versions

## What is formalized

* `Polyfold.IsFilledVersion.isFillingGerm`: a filled version (sc-smooth on the whole `U`) is a
  filling in the germ sense; `Polyfold.IsFillingGerm.isFilledVersion`: conversely when `g` is
  sc-smooth on the whole `U` (`Polyfold.fillDefect_isScSmooth`).
* `Polyfold.IsConjugateToBasicGerm.congr_nhds`: conjugation to a basic germ depends only on the
  germ at `0`.
* **Definition 3.1.11 (preprint 3.11) in the germ reading** (`Polyfold.StrongBundle.IsScFredholmGerm`), implied by
  the project's `IsScFredholmGermWholeChart` (`StrongBundle.IsScFredholmGermWholeChart.isScFredholmGerm`), and equal to
  it when `g`, `s` are sc-smooth on the whole `U` (`StrongBundle.isScFredholmGerm_iff_germG_wholeChart`).
* The trivial retraction `K = U ◁ F`: `Polyfold.isStrongBundleRetraction_id_of_relOpen`,
  `Polyfold.isFilledVersion_id`, `Polyfold.exists_wholeChart_filledVersion_of_id`.

Introduced in `Chapter3/GermVsChart.lean` (Findings, Chapter 3, items 262–263) and placed here,
just above `StrongBundleSections.lean`, so that the files of §3.1–§3.6 can use them.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

section GermReading

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

/-- **Project ⇒ text**: a filled version (Definition 3.1.6 (preprint 3.6) on the whole `U`) is a filling in the
text's germ sense, on the germ `ofSet U` (round-trip item V3.43, `proj_to_B`). -/
theorem IsFilledVersion.isFillingGerm (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) {fb g : E 0 → F 0}
    (h : IsFilledVersion hU hR h0 fb g) : IsFillingGerm hU hR h0 fb g := by
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  obtain ⟨Φ, hΦ⟩ := h.filler.linearization
  exact ⟨h.filler.eq_on, h.filler.mem_of_fixed, ScNbhdGerm.ofSet hU.relOpen h0, fun u hu => hu,
    h.isScSmooth.isScSmoothGerm hQ hU.relOpen h0, scDeriv U (fillDefect R g),
    h.filler.isSc1.isSc1GermWith_ofSet hU.relOpen h0, Φ, hΦ⟩

/-- `[1 − ρ(r(·))]g` is sc-smooth on `U` when `g` is (the chain rule; round-trip item V3.9). -/
theorem fillDefect_isScSmooth (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
    {g : E 0 → F 0} (hg : IsScSmooth U g) : IsScSmooth U (fillDefect R g) := by
  have hrs : IsScSmooth U (StrongRetr.r R) := StrongRetr.r_isScSmooth hU hR
  have hpair := hrs.scPair hU.isScDomain hg
  have hfib : IsScSmooth (U ×ˢ univ) fun p : (E.prod F) 0 => (R p).2 :=
    hR.isScSmooth_zero.snd (hU.prod_univ F).isScDomain
  have hcomp := IsScSmooth.comp hU.isScDomain (hU.prod_univ F).isScDomain hfib hpair
    fun y hy => ⟨StrongRetr.r_mem hR hy, mem_univ _⟩
  exact (hg.sub hU.isScDomain hcomp).congr hU.isScDomain fun y _ => rfl

/-- **Text ⇒ project when `g` is whole-chart**: a filling in the germ sense whose `g` is sc-smooth
on the whole `U` is a filled version: `[1 − ρ(r(·))]g` is sc¹ on `U` by the chain rule, and its
linearization at `0` is the germ's `Dk(0)` by uniqueness of the derivative at `0` (round-trip
item V3.43, `B_to_proj`). -/
theorem IsFillingGerm.isFilledVersion (hU : IsRelOpenInQuadrant E C U)
    (hR : IsStrongBundleRetraction U R) (h0 : (0 : E 0) ∈ U) {fb g : E 0 → F 0}
    (hg : IsScSmooth U g) (h : IsFillingGerm hU hR h0 fb g) : IsFilledVersion hU hR h0 fb g := by
  obtain ⟨G, hGU, -, Dk, hDk, Φ, hΦ⟩ := h.germ
  have hQ := hU.isPartialQuadrant.isQuadrantLike
  have hk : IsSc1 U (fillDefect R g) := (fillDefect_isScSmooth hU hR hg).isSc1
  have hsub : ∀ m, G.U m ⊆ (ScNbhdGerm.ofSet hU.relOpen h0).U m := fun m x hx => by
    rw [ScNbhdGerm.ofSet_U, ScBanach.mem_lvlSet]
    exact hGU (G.toBase_mem hx)
  have hDk' : IsSc1GermWith G (fillDefect R g) (scDeriv U (fillDefect R g)) :=
    (hk.isSc1GermWith_ofSet hU.relOpen h0).mono hsub
  have heq : Dk 0 = scDeriv U (fillDefect R g) 0 :=
    hDk.eq_of_uniqueDiffWithinAt hDk' (G.zero_mem 1) (G.uniqueDiffWithinAt hQ 1 (G.zero_mem 1))
  refine ⟨hg, h.eq_on, h.mem_of_fixed, hk, Φ, fun v => ?_⟩
  rw [hΦ v, heq]
  rfl

/-- Conjugation to a basic germ depends only on the values of `k` on `U` near `0`
(`IsConjugateToBasicGerm.congr` for an eventual equality). -/
theorem IsConjugateToBasicGerm.congr_nhds {k k' : E 0 → F 0} (h : IsConjugateToBasicGerm U k)
    (hkk' : ∀ᶠ u in 𝓝 (0 : E 0), u ∈ U → k u = k' u) : IsConjugateToBasicGerm U k' := by
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, hb, Bc, hCt, hU', hΨ, h0, hG, hh,
    hev⟩ := h
  refine ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, hb, Bc, hCt, hU', hΨ, h0, hG, hh, ?_⟩
  filter_upwards [hev, hkk'] with u hu hu' huU
  rw [← hu' huU]; exact hu huU

/-! ### The trivial retraction `K = U ◁ F`: the filled version is harmless -/

/-- The identity of `U ◁ F` is a strong bundle retraction, for every relatively open `U` in a
partial quadrant (`isStrongBundleRetraction_id` for `U = E`). -/
theorem isStrongBundleRetraction_id_of_relOpen (hU : IsRelOpenInQuadrant E C U) :
    IsStrongBundleRetraction (E := E) (F := F) U id where
  mapsTo := mapsTo_id _
  fst_independent _ _ _ _ := rfl
  fiber_linear _ _ := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  preserves_filtration _ _ _ _ _ hu _ hh := ⟨hu, hh⟩
  isScSmooth_zero := isScSmooth_id (hU.prod_univ F).isScDomain
  isScSmooth_one := by
    have : shiftFiber (id : E 0 × F 0 → E 0 × F 0) = id := by
      funext p
      exact Prod.ext rfl (Function.leftInverse_invFun (F.toBase_injective 1) p.2)
    rw [this]
    exact isScSmooth_id (hU.prod_univ F.shift).isScDomain
  idem _ _ := rfl

/-- **With the identity retraction (`K = U ◁ F`, `O = U`) a map sc-smooth on `U` is its own filled
version**: conditions (1) and (2) of Definition 3.1.4 (preprint 3.4) are trivial (`r = id`, `ρ = 1`),
`[1 − ρ(r(·))]g = 0`, and both kernels of condition (3) are `0`. -/
theorem isFilledVersion_id (hU : IsRelOpenInQuadrant E C U) (h0 : (0 : E 0) ∈ U) {g : E 0 → F 0}
    (hg : IsScSmooth U g) :
    IsFilledVersion hU (isStrongBundleRetraction_id_of_relOpen hU) h0 g g := by
  have hR := isStrongBundleRetraction_id_of_relOpen (F := F) hU
  have hr : ∀ y, StrongRetr.r (id : E 0 × F 0 → E 0 × F 0) y = y := fun _ => rfl
  have hρ : ∀ y h, StrongRetr.ρ (id : E 0 × F 0 → E 0 × F 0) y h = h := fun _ _ => rfl
  refine ⟨hg, ⟨Eventually.of_forall fun _ _ => rfl,
    Eventually.of_forall fun y hy _ => ⟨y, hy, hr y⟩, ?_, ?_⟩⟩
  · have : (fun y => g y - StrongRetr.ρ (id : E 0 × F 0 → E 0 × F 0)
        (StrongRetr.r (id : E 0 × F 0 → E 0 × F 0) y) (g y)) = fun y => g y - g y :=
      funext fun y => by rw [hρ]
    rw [this]; exact (hg.sub hU.isScDomain hg).isSc1
  · have hker1 : ∀ v ∈ LinearMap.ker ((scDeriv U (StrongRetr.r (id : E 0 × F 0 → E 0 × F 0))
        (0 : E 1) : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0), v = 0 := by
      intro v hv
      have hid : StrongRetr.r (id : E 0 × F 0 → E 0 × F 0) = (_root_.id : E 0 → E 0) := rfl
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hid] at hv
      have h1 : IsSc1With U (_root_.id : E 0 → E 0) fun _ => ContinuousLinearMap.id ℝ (E 0) :=
        isSc1With_id U
      have h0' : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
      rw [IsSc1.scDeriv_eqOn h1 (hU.isScDomain.uniqueDiffWithinAt 1) h0'] at hv
      exact hv
    have hker2 : ∀ v ∈ LinearMap.ker ((StrongRetr.ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0),
        v = 0 := fun v hv => hv
    have : Subsingleton (LinearMap.ker ((scDeriv U (StrongRetr.r (id : E 0 × F 0 → E 0 × F 0))
        (0 : E 1) : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0)) :=
      ⟨fun a b => Subtype.ext (by rw [hker1 a a.2, hker1 b b.2])⟩
    have : Subsingleton (LinearMap.ker ((StrongRetr.ρCLM hR h0 : F 0 →L[ℝ] F 0) :
        F 0 →ₗ[ℝ] F 0)) :=
      ⟨fun a b => Subtype.ext (by rw [hker2 a a.2, hker2 b b.2])⟩
    refine ⟨⟨LinearEquiv.ofSubsingleton _ _, continuous_of_const fun _ _ => Subsingleton.elim _ _,
      continuous_of_const fun _ _ => Subsingleton.elim _ _⟩, fun v => ?_⟩
    rw [Subsingleton.elim v 0, map_zero]
    simp

/-- **For a trivial retraction the filled version is harmless**: if `f̂` is sc-smooth on `U` (as
the principal part of a section sc-smooth on `X` is, in a chart with `K = U ◁ F`) and `g` is a
filling of `f̂` in the text's germ sense, then in the data of Definition 3.1.11 (preprint 3.11) `g` can be replaced
by the whole-chart `f̂` itself: same sc⁺-section `s`, same conjugation, because `f̂ = g` near `0`
by condition (1).  The germ reading and the project's reading then differ only in `s`. -/
theorem exists_wholeChart_filledVersion_of_id (hU : IsRelOpenInQuadrant E C U)
    (h0 : (0 : E 0) ∈ U) {fb g : E 0 → F 0} {s : E 0 → F 1} (hfb : IsScSmooth U fb)
    (hg : IsFillingGerm hU (isStrongBundleRetraction_id_of_relOpen hU) h0 fb g)
    (hs0 : F.toBase 1 (s 0) = g 0)
    (hconj : IsConjugateToBasicGerm U (fun u => g u - F.toBase 1 (s u))) :
    IsFilledVersion hU (isStrongBundleRetraction_id_of_relOpen hU) h0 fb fb ∧
      F.toBase 1 (s 0) = fb 0 ∧ IsConjugateToBasicGerm U (fun u => fb u - F.toBase 1 (s u)) := by
  have hr : ∀ y, StrongRetr.r (id : E 0 × F 0 → E 0 × F 0) y = y := fun _ => rfl
  have heq : ∀ᶠ u in 𝓝 (0 : E 0), u ∈ U → fb u = g u := by
    filter_upwards [hg.eq_on] with u hu huU
    exact hu ⟨u, huU, hr u⟩
  refine ⟨isFilledVersion_id hU h0 hfb, hs0.trans (heq.self_of_nhds h0).symm, ?_⟩
  exact hconj.congr_nhds (heq.mono fun u hu huU => by rw [hu huU])

end GermReading

/-! ### Definition 3.1.11 (preprint 3.11) in the germ reading, for sections of strong bundles -/

section FredholmSectionsGerm

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle PX P)
  {f : X → Y}

namespace StrongBundle

/-- **Definition 3.1.11 (preprint 3.11), the text's germ reading**: `(f, x₀)` is an sc-Fredholm germ at the smooth
point `x₀` if in some strong bundle chart of `P` centred at `x₀` the principal part `f̂` has a
filling `g` in the germ sense (`IsFillingGerm`: an sc-smooth germ on a germ of neighbourhoods
whose levels may shrink), and there is a local sc⁺-section `s` in the germ sense (`IsScPlusGerm`)
with `s(0) = g(0)` such that `g − s` is conjugated to a basic germ (`IsConjugateToBasicGerm`, with
the strong bundle isomorphism on the whole `U`; an isomorphism on a relatively open `U₀ ⊆ U` is
the same thing after restricting the chart on level `0`).  The project's `IsScFredholmGermWholeChart`
asks `g` and `s` to be sc-smooth on the whole `U ∩ E_m` for every `m`
(`isScFredholmGerm_iff_germG_wholeChart`). -/
def IsScFredholmGerm (f : X → Y) (x₀ : X) : Prop :=
  x₀ ∈ PX.smoothSet ∧
  ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
    IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g ∧
    IsScPlusGerm c.φ.model.C c.U s ∧ c.F.toBase 1 (s 0) = g 0 ∧
    IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u))

variable {B}

/-- **Project ⇒ text**: an sc-Fredholm germ in the project's sense is one in the text's germ sense
(round-trip item V3.13, `proj_to_parts`). -/
theorem IsScFredholmGermWholeChart.isScFredholmGerm {x₀ : X} (h : B.IsScFredholmGermWholeChart f x₀) :
    B.IsScFredholmGerm f x₀ := by
  obtain ⟨hx₀, c, hc, hx, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := h
  exact ⟨hx₀, c, hc, hx, hφ0, h0, g, s, hfill.isFillingGerm c.relOpen c.isRetraction h0,
    ⟨ScNbhdGerm.ofSet c.relOpen.relOpen h0, fun _ hu => hu,
      hs.isScSmoothGerm c.isQuadrantLike c.relOpen.relOpen h0⟩, hs0, hconj⟩

/-- **The reduction**: `(f, x₀)` is an sc-Fredholm germ in the project's sense if and only if it
is one in the text's germ sense **with the filling `g` and the sc⁺-section `s` sc-smooth on the
whole `U ∩ E_m` of the chart for every `m`**.  The two readings differ exactly in this regularity
of `g` and `s` away from the shrinking germ (Findings, Chapter 3, items 221 and 260). -/
theorem isScFredholmGerm_iff_germG_wholeChart {x₀ : X} : B.IsScFredholmGermWholeChart f x₀ ↔
    x₀ ∈ PX.smoothSet ∧
    ∃ (c : StrongBundleChart PX P) (_ : B.IsChart c) (_ : x₀ ∈ c.φ.source) (_ : c.φ x₀ = 0)
      (h0 : (0 : c.φ.model.E 0) ∈ c.U) (g : c.φ.model.E 0 → c.F 0) (s : c.φ.model.E 0 → c.F 1),
      (IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g ∧ IsScSmooth c.U g) ∧
      (IsScPlusGerm c.φ.model.C c.U s ∧ IsScSmooth (F := c.F.shift) c.U s) ∧
      c.F.toBase 1 (s 0) = g 0 ∧
      IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)) := by
  constructor
  · rintro ⟨hx₀, c, hc, hx, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩
    exact ⟨hx₀, c, hc, hx, hφ0, h0, g, s,
      ⟨hfill.isFillingGerm c.relOpen c.isRetraction h0, hfill.isScSmooth⟩,
      ⟨⟨ScNbhdGerm.ofSet c.relOpen.relOpen h0, fun _ hu => hu,
        hs.isScSmoothGerm c.isQuadrantLike c.relOpen.relOpen h0⟩, hs⟩, hs0, hconj⟩
  · rintro ⟨hx₀, c, hc, hx, hφ0, h0, g, s, ⟨hfill, hg⟩, ⟨-, hs⟩, hs0, hconj⟩
    exact ⟨hx₀, c, hc, hx, hφ0, h0, g, s, hfill.isFilledVersion c.relOpen c.isRetraction h0 hg,
      hs, hs0, hconj⟩

end StrongBundle

end FredholmSectionsGerm

end Polyfold
