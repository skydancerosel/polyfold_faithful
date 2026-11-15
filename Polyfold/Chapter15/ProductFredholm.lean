import Polyfold.Chapter15.ProductBasicGerm
import Polyfold.Chapter15.ProductMultisection
import Polyfold.Chapter3.TameGermsG
import Polyfold.Chapter12.CompactnessEp

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2021), §15.3, the products remark after
**Definition 15.3.3** (p. 692; 2017: after Definition 15.5): "take the product so that `f × f'`
is an sc-Fredholm section of `W × W' → X × X'`".

# The product of two sc-Fredholm sections is sc-Fredholm

## What is formalized

* `MPolyfold.mem_levelSet_prod`, `MPolyfold.mem_smoothSet_prod`: `(X × X')_m = X_m × X'_m`.
* `StrongBundle.IsChart.prod`, `StrongBundle.IsTameChart.prod`: products of (tame) strong
  bundle charts compatible with the atlases are (tame) charts compatible with the product atlas.
* `StrongBundle.IsScFredholmGerm.prod`, `StrongBundle.IsScFredholmGermTame.prod`
  (Definition 3.1.11, Definition 3.6.3): the germ data of `f × f'` at `(x, x')` in the product
  chart: the filling `g × g'` (`IsFillingGerm.prod`), the sc⁺-germ `s × s'`, and the conjugation
  of `(g − s) × (g' − s')` to the product basic germ (`IsConjugateToBasicGerm.prod`).
* `StrongBundle.regularizing_prodMap`: `f × f'` is regularizing.
* **`StrongBundle.IsScFredholmSection.prod`**, **`StrongBundle.IsScFredholmSectionTame.prod`**
  (Definition 3.1.16, Definition 3.6.4).
* **`EpStrongBundle.IsScFredholmSectionFunctor.prod`** (Definition 8.3.4 (3)): `f × f'` is an
  sc-Fredholm section functor of `(W × W', μ × μ')`; `hasCompactSolutionSetEp_prodMap`
  (`|S_{f × f'}|` is compact when `|S_f|` and `|S_{f'}|` are).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

universe u v u' v'

section Levels

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  [ParacompactSpace (X × X')]

/-- `(X × X')_m = X_m × X'_m`. -/
lemma MPolyfold.mem_levelSet_prod {m : ℕ} {z : X × X'} :
    z ∈ (PX.prod PX').levelSet m ↔ z.1 ∈ PX.levelSet m ∧ z.2 ∈ PX'.levelSet m := by
  obtain ⟨φ, hφ, hx⟩ := PX.exists_isChart_mem_source z.1
  obtain ⟨ψ, hψ, hy⟩ := PX'.exists_isChart_mem_source z.2
  rw [(PX.prod PX').mem_levelSet_iff (MPolyfold.IsChart.prod hφ hψ)
    (show z ∈ (φ.prod ψ).source from ⟨hx, hy⟩), PX.mem_levelSet_iff hφ hx,
    PX'.mem_levelSet_iff hψ hy]
  exact ScBanach.mem_range_prod_toBase (E := φ.model.E) (F := ψ.model.E)

/-- The smooth points of `X × X'` are the pairs of smooth points. -/
lemma MPolyfold.mem_smoothSet_prod {z : X × X'} :
    z ∈ (PX.prod PX').smoothSet ↔ z.1 ∈ PX.smoothSet ∧ z.2 ∈ PX'.smoothSet := by
  simp only [MPolyfold.smoothSet, mem_iInter, MPolyfold.mem_levelSet_prod, forall_and]

end Levels

section ProductFredholm

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  [ParacompactSpace (X × X')] [ParacompactSpace (Y × Y')]
  {B : StrongBundle PX P} {B' : StrongBundle PX' P'} {f : X → Y} {f' : X' → Y'}

namespace StrongBundle

/-- A product of strong bundle charts compatible with the two atlases is compatible with the
product atlas. -/
theorem IsChart.prod {c : StrongBundleChart PX P} {c' : StrongBundleChart PX' P'}
    (hc : B.IsChart c) (hc' : B'.IsChart c') : (B.prod B').IsChart (c.prod c') := by
  rintro _ ⟨d, hd, d', hd', rfl⟩
  exact (hc d hd).prod (hc' d' hd')

/-- A product of tame strong bundle charts is a tame strong bundle chart: the base retraction is
`r × r'` (`ScRetraction.IsTameWith.prod`). -/
theorem IsTameChart.prod {c : StrongBundleChart PX P} {c' : StrongBundleChart PX' P'}
    (hc : B.IsTameChart c) (hc' : B'.IsTameChart c') : (B.prod B').IsTameChart (c.prod c') := by
  refine ⟨hc.1.prod hc'.1, ?_⟩
  obtain ⟨n₁, W₁, T₁, hT₁⟩ := c.relOpen.isPartialQuadrant
  obtain ⟨n₂, W₂, T₂, hT₂⟩ := c'.relOpen.isPartialQuadrant
  have h := ScRetraction.IsTameWith.prod hT₁ hT₂ (hc.2 n₁ W₁ T₁ hT₁) (hc'.2 n₂ W₂ T₂ hT₂)
  exact h.isTame (prod_eq_prodPresentation T₁ T₂ hT₁ hT₂)

omit [T2Space Y] [ParacompactSpace Y] [T2Space Y'] [ParacompactSpace Y']
  [ParacompactSpace (Y × Y')] in
/-- The principal part of `f × f'` in the product chart is the product of the principal parts. -/
lemma principal_prod (c : StrongBundleChart PX P) (c' : StrongBundleChart PX' P') (f : X → Y)
    (f' : X' → Y') :
    (c.prod c').principal (Prod.map f f') = Prod.map (c.principal f) (c'.principal f') := rfl

omit [T2Space Y] [ParacompactSpace Y] [T2Space Y'] [ParacompactSpace Y']
  [ParacompactSpace (Y × Y')] in
/-- The germ data of `f × f'` at `(x, x')`, in a product chart `c × c'`. -/
theorem exists_germData_prod {c : StrongBundleChart PX P} {c' : StrongBundleChart PX' P'}
    (h0 : (0 : c.φ.model.E 0) ∈ c.U) (h0' : (0 : c'.φ.model.E 0) ∈ c'.U)
    {g : c.φ.model.E 0 → c.F 0} {s : c.φ.model.E 0 → c.F 1} {g' : c'.φ.model.E 0 → c'.F 0}
    {s' : c'.φ.model.E 0 → c'.F 1}
    (hfill : IsFillingGerm c.relOpen c.isRetraction h0 (c.principal f) g)
    (hs : IsScPlusGerm c.φ.model.C c.U s) (hs0 : c.F.toBase 1 (s 0) = g 0)
    (hconj : IsConjugateToBasicGerm c.U (fun u => g u - c.F.toBase 1 (s u)))
    (hfill' : IsFillingGerm c'.relOpen c'.isRetraction h0' (c'.principal f') g')
    (hs' : IsScPlusGerm c'.φ.model.C c'.U s') (hs0' : c'.F.toBase 1 (s' 0) = g' 0)
    (hconj' : IsConjugateToBasicGerm c'.U (fun u => g' u - c'.F.toBase 1 (s' u))) :
    ∃ (h0'' : (0 : (c.prod c').φ.model.E 0) ∈ (c.prod c').U)
      (g'' : (c.prod c').φ.model.E 0 → (c.prod c').F 0)
      (s'' : (c.prod c').φ.model.E 0 → (c.prod c').F 1),
      IsFillingGerm (c.prod c').relOpen (c.prod c').isRetraction h0''
        ((c.prod c').principal (Prod.map f f')) g'' ∧
      IsScPlusGerm (c.prod c').φ.model.C (c.prod c').U s'' ∧
      (c.prod c').F.toBase 1 (s'' 0) = g'' 0 ∧
      IsConjugateToBasicGerm (c.prod c').U (fun u => g'' u - (c.prod c').F.toBase 1 (s'' u)) := by
  refine ⟨⟨h0, h0'⟩, Prod.map g g', Prod.map s s', ?_, ?_, ?_, ?_⟩
  · exact IsFillingGerm.prod c.relOpen c'.relOpen c.isRetraction c'.isRetraction h0 h0' hfill
      hfill'
  · exact IsScPlusGerm.prodMap c.isQuadrantLike c'.isQuadrantLike hs hs'
  · exact (ScBanach.prod_toBase c.F c'.F 1 _).trans (Prod.ext hs0 hs0')
  · refine (IsConjugateToBasicGerm.prod c.relOpen c'.relOpen hconj hconj').congr fun u _ => ?_
    change (g u.1 - c.F.toBase 1 (s u.1), g' u.2 - c'.F.toBase 1 (s' u.2)) =
      (g u.1, g' u.2) - (c.F.prod c'.F).toBase 1 (s u.1, s' u.2)
    rw [ScBanach.prod_toBase]
    rfl

/-- **Products of sc-Fredholm germs** (Definition 3.1.11, germ reading). -/
theorem IsScFredholmGerm.prod {x : X} {x' : X'} (h : B.IsScFredholmGerm f x)
    (h' : B'.IsScFredholmGerm f' x') :
    (B.prod B').IsScFredholmGerm (Prod.map f f') (x, x') := by
  obtain ⟨hxs, c, hc, hxV, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := h
  obtain ⟨hxs', c', hc', hxV', hφ0', h0', g', s', hfill', hs', hs0', hconj'⟩ := h'
  obtain ⟨h0'', g'', s'', H⟩ := exists_germData_prod h0 h0' hfill hs hs0 hconj hfill' hs' hs0'
    hconj'
  exact ⟨MPolyfold.mem_smoothSet_prod.2 ⟨hxs, hxs'⟩, c.prod c', hc.prod hc', ⟨hxV, hxV'⟩,
    Prod.ext hφ0 hφ0', h0'', g'', s'', H⟩

/-- **Products of sc-Fredholm germs with tame germ data** (Definition 3.6.3, germ reading). -/
theorem IsScFredholmGermTame.prod {x : X} {x' : X'} (h : B.IsScFredholmGermTame f x)
    (h' : B'.IsScFredholmGermTame f' x') :
    (B.prod B').IsScFredholmGermTame (Prod.map f f') (x, x') := by
  obtain ⟨hxs, c, hc, hxV, hφ0, h0, g, s, hfill, hs, hs0, hconj⟩ := h
  obtain ⟨hxs', c', hc', hxV', hφ0', h0', g', s', hfill', hs', hs0', hconj'⟩ := h'
  obtain ⟨h0'', g'', s'', H⟩ := exists_germData_prod h0 h0' hfill hs hs0 hconj hfill' hs' hs0'
    hconj'
  exact ⟨MPolyfold.mem_smoothSet_prod.2 ⟨hxs, hxs'⟩, c.prod c', hc.prod hc', ⟨hxV, hxV'⟩,
    Prod.ext hφ0 hφ0', h0'', g'', s'', H⟩

/-- `f × f'` is regularizing when `f` and `f'` are. -/
theorem regularizing_prodMap (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f') :
    ∀ m, ∀ z ∈ (PX.prod PX').levelSet m,
      Prod.map f f' z ∈ (B.prod B').doubleLevel m (m + 1) →
      z ∈ (PX.prod PX').levelSet (m + 1) := by
  intro m z hz hdl
  rw [MPolyfold.mem_levelSet_prod] at hz ⊢
  constructor
  · refine hf.regularizing m z.1 hz.1 fun c hc hmem => ?_
    obtain ⟨c', hc', hmem'⟩ := B'.atlas.cover (f' z.2)
    have h1 := hdl (c.prod c') (prod_mem_charts B B' hc hc') ⟨hmem, hmem'⟩
    exact ⟨((ScBanach.mem_range_prod_toBase (E := c.φ.model.E) (F := c'.φ.model.E)).1 h1.1).1,
      ((ScBanach.mem_range_prod_toBase (E := c.F) (F := c'.F)).1 h1.2).1⟩
  · refine hf'.regularizing m z.2 hz.2 fun c' hc' hmem' => ?_
    obtain ⟨c, hc, hmem⟩ := B.atlas.cover (f z.1)
    have h1 := hdl (c.prod c') (prod_mem_charts B B' hc hc') ⟨hmem, hmem'⟩
    exact ⟨((ScBanach.mem_range_prod_toBase (E := c.φ.model.E) (F := c'.φ.model.E)).1 h1.1).2,
      ((ScBanach.mem_range_prod_toBase (E := c.F) (F := c'.F)).1 h1.2).2⟩

/-- **The product of two sc-Fredholm sections is an sc-Fredholm section** of the product strong
bundle (Definition 3.1.16; the text's "`f × f'` is an sc-Fredholm section of
`W × W' → X × X'`", p. 692). -/
theorem IsScFredholmSection.prod (hf : B.IsScFredholmSection f)
    (hf' : B'.IsScFredholmSection f') : (B.prod B').IsScFredholmSection (Prod.map f f') where
  isScSmooth := hf.isScSmooth.prod hf'.isScSmooth
  regularizing := regularizing_prodMap hf hf'
  germ z hz := (hf.germ z.1 (MPolyfold.mem_smoothSet_prod.1 hz).1).prod
    (hf'.germ z.2 (MPolyfold.mem_smoothSet_prod.1 hz).2)

/-- **The product of two sc-Fredholm sections with tame germ data** has tame germ data
(Definition 3.6.4). -/
theorem IsScFredholmSectionTame.prod (hf : B.IsScFredholmSectionTame f)
    (hf' : B'.IsScFredholmSectionTame f') :
    (B.prod B').IsScFredholmSectionTame (Prod.map f f') where
  toIsScFredholmSection := hf.toIsScFredholmSection.prod hf'.toIsScFredholmSection
  germTame z hz := (hf.germTame z.1 (MPolyfold.mem_smoothSet_prod.1 hz).1).prod
    (hf'.germTame z.2 (MPolyfold.mem_smoothSet_prod.1 hz).2)

end StrongBundle

end ProductFredholm

section EpLevel

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {Obj' Mor' : Type u'} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  [ParacompactSpace (Obj × Obj')] [ParacompactSpace (Mor × Mor')]
  {W : Type v} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  {W' : Type v'} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})]
  [ParacompactSpace (W × W')]
  {B : StrongBundle X.PObj P} {B' : StrongBundle X'.PObj P'}
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'}

/-- **`f × f'` is an sc-Fredholm section functor** of `(W × W', μ × μ')` (Definition 8.3.4 (3);
the products remark after Definition 15.3.3, p. 692). -/
theorem EpStrongBundle.IsScFredholmSectionFunctor.prod {f : Obj → W} {f' : Obj' → W'}
    (h : E.IsScFredholmSectionFunctor f) (h' : E'.IsScFredholmSectionFunctor f') :
    (E.prod E').IsScFredholmSectionFunctor (Prod.map f f') :=
  ⟨h.1.prod h'.1, h.2.prod h'.2⟩

end EpLevel

namespace SBLocalization

variable {A A' : SEP.{u}}

/-- `|S_{f × f'}|` is compact when `|S_f|` and `|S_{f'}|` are (Definition 12.4.1 (1) for the
product data). -/
theorem hasCompactSolutionSetEp_prodMap {f : A.Obj → A.W} {f' : A'.Obj → A'.W}
    (h : A.E.HasCompactSolutionSetEp f) (h' : A'.E.HasCompactSolutionSetEp f') :
    (A.prod A').E.HasCompactSolutionSetEp (Prod.map f f') := by
  have hq : IsQuotientMap (Prod.map A.X.π A'.X.π) :=
    (A.X.proposition_7_1_8.prodMap A'.X.proposition_7_1_8).isQuotientMap
      (A.X.continuous_π.prodMap A'.X.continuous_π)
      (Quotient.mk_surjective.prodMap Quotient.mk_surjective)
  set j : A.X.OrbitSpace × A'.X.OrbitSpace → (A.prod A').X.OrbitSpace := fun z =>
    (A.prod A').X.π (Quotient.out z.1, Quotient.out z.2) with hj
  have hjπ : ∀ x : (A.prod A').Obj, j (A.X.π x.1, A'.X.π x.2) = (A.prod A').X.π x := fun x =>
    (EpGroupoid.prod_π_eq_π_iff A.X A'.X _ _).2 ⟨Quotient.out_eq _, Quotient.out_eq _⟩
  have hjc : Continuous j := by
    rw [hq.continuous_iff]
    exact (A.prod A').X.continuous_π.congr fun x => (hjπ x).symm
  have hcomp : IsCompact (j '' ((A.X.π '' solutionSet A.P f) ×ˢ
      (A'.X.π '' solutionSet A'.P f'))) := (IsCompact.prod h h').image hjc
  have heq : (A.prod A').X.π '' solutionSet (A.prod A').P (Prod.map f f') =
      j '' ((A.X.π '' solutionSet A.P f) ×ˢ (A'.X.π '' solutionSet A'.P f')) := by
    rw [solutionSet_prodMap]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(A.X.π x.1, A'.X.π x.2), ⟨⟨x.1, hx.1, rfl⟩, ⟨x.2, hx.2, rfl⟩⟩, hjπ x⟩
    · rintro ⟨⟨_, _⟩, ⟨⟨x, hx, rfl⟩, ⟨x', hx', rfl⟩⟩, rfl⟩
      exact ⟨(x, x'), ⟨hx, hx'⟩, (hjπ (x, x')).symm⟩
  change IsCompact ((A.prod A').X.π '' solutionSet (A.prod A').P (Prod.map f f'))
  rw [heq]
  exact hcomp

/-- **The product data of §15.3** (p. 692): for sc-Fredholm section functors `f`, `f'` with tame
germ data, `f × f'` is an sc-Fredholm section functor of `W × W' → X × X'` with tame germ
data. -/
theorem isScFredholmSectionFunctor_prodMap {f : A.Obj → A.W} {f' : A'.Obj → A'.W}
    (hf : A.E.IsScFredholmSectionFunctor f) (hft : A.B.IsScFredholmSectionTame f)
    (hf' : A'.E.IsScFredholmSectionFunctor f') (hft' : A'.B.IsScFredholmSectionTame f') :
    (A.prod A').E.IsScFredholmSectionFunctor (Prod.map f f') ∧
      (A.prod A').B.IsScFredholmSectionTame (Prod.map f f') :=
  ⟨hf.prod hf', hft.prod hft'⟩

end SBLocalization

end Polyfold
