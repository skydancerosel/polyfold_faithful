import Polyfold.Chapter6.OrientationSpace
import Polyfold.Chapter6.SolutionOrientationCharts
import Polyfold.Chapter2.SmoothPaths
import Polyfold.Chapter7.LocConnected

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, pp. 273–276:
**Theorem 6.6.13** (preprint Theorem 6.37, p. 226), **Definition 6.6.16** (preprint
Definition 6.40), **Theorem 6.6.17** (new in 2021) and **Theorem 6.6.18** (preprint
Theorem 6.41, p. 229), stated with the hypotheses of the text only.

# The orientation theorems of §6.6 without auxiliary hypotheses

## The text, paraphrased

(Theorem 6.6.13) For an sc-Fredholm section `f` of a strong bundle over a tame M-polyfold there is
a unique functor `Γ_f : PX → Or_f` with property (∗).  (Definition 6.6.16) An orientation of `f`
assigns to every smooth `y` an orientation of `DET(f, y)` which is one of the two continuous
orientations over every orientable neighbourhood.  (Theorem 6.6.17) `O_f` carries exactly one
Hausdorff topology with properties (1)–(3).  (Theorem 6.6.18) For `f` proper, in general position
at every zero, and an orientation `o` of `f`, `S = f⁻¹(0)` is a smooth compact manifold with
boundary with corners with a natural orientation.

## What is formalized

* Witnesses for the instance hypotheses of Chapter 6: `paracompactSpace_rn_prod`,
  `paracompactSpace_rn_pullback`, `paracompactSpace_rn_rn_prod`, `paracompactSpace_rn_rn_pullback`
  (`ℝⁿ × X`, `ℝᵏ × (ℝⁿ × X)` and the pull-back spaces are paracompact: Theorem 2.3.10 (2021;
  preprint Theorem 2.16), `MPolyfold.paracompactSpace_prod`, `paracompactSpace_pullbackSpace`).
* `theorem_6_6_13`: Theorem 6.6.13 (`theorem_6_37`) without the hypothesis
  `B.HasScPlusSectionsThrough` (it follows from the bump functions,
  `MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough`) and without instance arguments.
* `theorem_6_6_17`: Theorem 6.6.17 (`theorem_6_6_17_2021`) likewise, and without
  `HasConnectedSmoothNbhds`: `MPolyfold.hasConnectedSmoothNbhds` proves it for every M-polyfold
  (gap G.90).
* `SectionOrientation`: Definition 6.6.16, the orientations of `f` (`IsSectionOrientation`).
* `IsNaturalSolutionOrientation`: what "`S` has the natural orientation given by `o`" means:
  the orientations `tangentOr(o_x)` of `T_xS = ker f'(x)` read in charts (1) agree in any two
  charts through the tangent map of the transition (gap G.68, `tangentOrAt_toChartOr`) and
  (2) form an orientation of the kernel line bundle along every sc-smooth path of zeros in an
  orientable neighbourhood (`theorem_6_41`).
* `theorem_6_6_18`: **Theorem 6.6.18 in the book's shape**: `SolutionSetInGeneralPosition`
  (compact manifold with boundary with corners in general position) and
  `IsNaturalSolutionOrientation`.

## What this makes unnecessary

* The hypothesis `hsec : B.HasScPlusSectionsThrough` of `theorem_6_37`, `theorem_6_6_17_2021`
  (and of the sections `Transport` of `OrientationFunctor.lean` and `Existence` of
  `OrientationSpace.lean`): discharged by
  `MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump`.
* The instance arguments `[∀ n, ParacompactSpace ((Fin n → ℝ) × X)]`,
  `[∀ n, ParacompactSpace (pullbackSpace P Prod.snd)]` and their two-parameter versions:
  discharged by the four witnesses above.
* Gap G.68 in the statement of Theorem 6.6.18 (`IsNaturalSolutionOrientation.chart_indep`).
-/

open Module Bundle Topology Set CategoryTheory

noncomputable section

namespace Polyfold

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-! ### The paracompactness instances of Chapter 6 hold -/

/-- **`ℝⁿ × X` is paracompact** for an M-polyfold `X` (Theorem 2.3.10, 2021; preprint
Theorem 2.16: metrizable). -/
theorem paracompactSpace_rn_prod (PX : MPolyfold X) : ∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X) :=
  fun n => MPolyfold.paracompactSpace_prod (rnPolyfold n) PX

/-- **The pull-back `π*Y` over `ℝⁿ × X` is paracompact** (`paracompactSpace_pullbackSpace`). -/
theorem paracompactSpace_rn_pullback (B : StrongBundle PX P) :
    haveI := paracompactSpace_rn_prod PX
    ∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X)) :=
  have := paracompactSpace_rn_prod PX
  fun n => paracompactSpace_pullbackSpace (f := (Prod.snd : (Fin n → ℝ) × X → X))
    ((rnPolyfold n).prod PX) B

/-- **`ℝᵏ × (ℝⁿ × X)` is paracompact**. -/
theorem paracompactSpace_rn_rn_prod (PX : MPolyfold X) :
    ∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X)) :=
  have := paracompactSpace_rn_prod PX
  fun k n => MPolyfold.paracompactSpace_prod (rnPolyfold k) ((rnPolyfold n).prod PX)

/-- **The pull-back over `ℝᵏ × (ℝⁿ × X)` of `π*Y` is paracompact**. -/
theorem paracompactSpace_rn_rn_pullback (B : StrongBundle PX P) :
    haveI := paracompactSpace_rn_prod PX
    haveI := paracompactSpace_rn_pullback B
    haveI := paracompactSpace_rn_rn_prod PX
    ∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X)) :=
  have := paracompactSpace_rn_prod PX
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_rn_prod PX
  fun k n => paracompactSpace_pullbackSpace
    (f := (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))
    ((rnPolyfold k).prod ((rnPolyfold n).prod PX))
    (B.pullback (MPolyfold.isScSmoothMap_snd (rnPolyfold n) PX))

/-! ### Connected smooth parts (the hypothesis of property (2) of Theorem 6.6.17) -/

namespace MPolyfold

/-- **Connected smooth parts of small neighbourhoods (gap G.90)**: every M-polyfold satisfies
`MPolyfold.HasConnectedSmoothNbhds`, the hypothesis of property (2) of 2021 Theorem 6.6.17: the
connected component of `x` in `W` is open (Proposition 2.3.7) and its smooth part is connected
(`MPolyfold.isPreconnected_smoothVal_preimage`). -/
theorem hasConnectedSmoothNbhds (P : MPolyfold X) : P.HasConnectedSmoothNbhds := by
  intro x W hW hxW
  exact ⟨connectedComponentIn W (P.smoothVal x), P.isOpen_connectedComponentIn hW _,
    mem_connectedComponentIn hxW, connectedComponentIn_subset _ _,
    P.isPreconnected_smoothVal_preimage (P.isOpen_connectedComponentIn hW _)
      (isConnected_connectedComponentIn_iff.2 hxW)⟩

end MPolyfold

/-! ### Theorems 6.6.13 and 6.6.17 -/

/-- **Theorem 6.6.13** (2021, p. 273; preprint Theorem 6.37): for an sc-Fredholm section `f` (with
tame germ data) of a strong bundle over a tame M-polyfold with bump functions, there is a unique
family of maps `Γ_f([φ]) : Or_x^f ≃ Or_y^f` on the morphisms `[φ] : x ⟶ y` of `PX` which is a
functor and has property (∗).  `theorem_6_37` without `B.HasScPlusSectionsThrough` and without
instance arguments. -/
theorem theorem_6_6_13 (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) :
    haveI := paracompactSpace_rn_prod PX
    haveI := paracompactSpace_rn_pullback B
    ∃! G : ∀ x y : PathCat PX, (x ⟶ y) →
        (Orx f hf.toIsScFredholmSection x.pt x.smooth ≃
          Orx f hf.toIsScFredholmSection y.pt y.smooth),
      (∀ x, G x x (𝟙 x) = Equiv.refl _) ∧
      (∀ (x y z : PathCat PX) (a : x ⟶ y) (b : y ⟶ z),
        G x z (a ≫ b) = (G x y a).trans (G y z b)) ∧
      IsStarProperty f hf.toIsScFredholmSection G := by
  have := paracompactSpace_rn_prod PX
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_rn_prod PX
  have := paracompactSpace_rn_rn_pullback B
  exact theorem_6_37 hX hbump hf (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump)

/-- **Theorem 6.6.17** (2021, p. 275, new in 2021): there is exactly one topology on `O_f` which
is Hausdorff and has properties (1), (2) and (3).  `theorem_6_6_17_2021` without
`B.HasScPlusSectionsThrough`, without `HasConnectedSmoothNbhds` (it holds for every M-polyfold,
`MPolyfold.hasConnectedSmoothNbhds`) and without instance arguments. -/
theorem theorem_6_6_17 (hX : PX.IsTame) (hbump : PX.AdmitsBumpFunctions)
    (hf : B.IsScFredholmSectionTame f) :
    haveI := paracompactSpace_rn_prod PX
    haveI := paracompactSpace_rn_pullback B
    ∃! t : TopologicalSpace (OrSpace f hf.toIsScFredholmSection),
      IsOrientationTopology f hf.toIsScFredholmSection t := by
  have := paracompactSpace_rn_prod PX
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_rn_prod PX
  have := paracompactSpace_rn_rn_pullback B
  exact theorem_6_6_17_2021 hX hbump hf (MPolyfold.AdmitsBumpFunctions.hasScPlusSectionsThrough hbump)
    PX.hasConnectedSmoothNbhds

/-! ### Definition 6.6.16 and Theorem 6.6.18 -/

variable (f) in
/-- **Definition 6.6.16** (2021, p. 274; preprint Definition 6.40): **an orientation of `f`**, a
map `y ↦ o_y ∈ Or_y^f` on the smooth points which is one of the two continuous orientations over
every orientable neighbourhood of every smooth point (`IsSectionOrientation`). -/
def SectionOrientation (hf : B.IsScFredholmSection f) : Type _ :=
  {o : ∀ y (hy : y ∈ PX.smoothSet), Orx f hf y hy //
    haveI := paracompactSpace_rn_prod PX
    haveI := paracompactSpace_rn_pullback B
    IsSectionOrientation f hf o}

variable (f) in
/-- **The natural orientation of `S = f⁻¹(0)` given by an orientation `o` of `f`** (2021
Theorem 6.6.18): at every zero `x`, `o_x` orients `T_xS = ker f'(x)` (`tangentOr`, `f'(x)` being
onto), and
(1) **chart independence**: read in two charts `c`, `c'` at `x`, the two orientations of
`ker f'(x)` correspond under the tangent map `D(τ ∘ r)(z)` of the transition
(`tangentKerEquiv`, `coe_tangentKerEquiv`);
(2) **continuity**: along every sc-smooth path `γ` of zeros in an orientable neighbourhood
`V ⊆ U` of a smooth point, in its chart `c`, the orientations form an orientation of the line
bundle `λ(Λ)` of the kernels `Λ_q = ker f'(γ_q)` (`tangentFamily`). -/
structure IsNaturalSolutionOrientation (hf : B.IsScFredholmSectionTame f)
    (hgp : ∀ x, IsZeroAt P f x → B.IsGeneralPositionGerm f x)
    (o : SectionOrientation f hf.toIsScFredholmSection) : Prop where
  chart_indep : ∀ (x : X) (hs : x ∈ PX.smoothSet) (hx0 : IsZeroAt P f x)
    (c c' : StrongBundleChart PX P) (hc : B.IsChart c) (hc' : B.IsChart c')
    (hxc : x ∈ c.φ.source) (hxc' : x ∈ c'.φ.source),
    (chartPtOf c' hc' hxc' hs).tangentOr hf.toIsScFredholmSection hx0 (hgp x hx0).isLinSurjAt
        (toChartOr hf.toIsScFredholmSection hs c' hc' hxc' (o.1 x hs)) =
      Module.Ray.map (maxPowEquiv ((chartPtOf c hc hxc hs).tangentKerEquiv
          (chartPtOf c' hc' hxc' hs) hf.toIsScFredholmSection hx0))
        ((chartPtOf c hc hxc hs).tangentOr hf.toIsScFredholmSection hx0 (hgp x hx0).isLinSurjAt
          (toChartOr hf.toIsScFredholmSection hs c hc hxc (o.1 x hs)))
  continuous :
    haveI := paracompactSpace_rn_prod PX
    haveI := paracompactSpace_rn_pullback B
    ∀ x₀ ∈ PX.smoothSet, ∀ (c : StrongBundleChart PX P) (hc : B.IsChart c) (U V : Set X)
      (hN : IsOrientableNbhd f hf.toIsScFredholmSection c hc U V x₀)
      (γ : (Fin 1 → ℝ) → X) (hγs : (rnPolyfold 1).IsScSmoothMap PX γ)
      (hγV : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ V)
      (hγ0 : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, IsZeroAt P f (γ q)),
      IsLineOrientation (tangentFamily hf hc hγs
          (fun q hq => hN.hasLocalPropagation.subset (hN.subset (hγV q hq))) hγ0
          (fun q hq => hgp (γ q) (hγ0 q hq))).det
        fun q => tangentOrAt f hf.toIsScFredholmSection c hc
          (hN.hasLocalPropagation.subset (hN.subset (hγV q q.2)))
          (hf.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2)) (hγ0 q q.2)
          (hgp (γ q) (hγ0 q q.2)).isLinSurjAt
          (restrictOr o.1 hN (γ q) (hγV q q.2)
            (hf.toIsScFredholmSection.mem_smoothSet_of_isZeroAt (hγ0 q q.2)))

/-- **Theorem 6.6.18** (2021, p. 275; preprint Theorem 6.41): let `P : Y → X` be a strong bundle
over a tame M-polyfold, `f` a proper sc-Fredholm section (with tame germ data) such that `(f, x)`
is in general position at every zero `x`, and `o` an orientation of `f` (Definition 6.6.16).  Then
`S = f⁻¹(0)` is a smooth compact manifold with boundary with corners
(`SolutionSetInGeneralPosition`) with the natural orientation given by `o`
(`IsNaturalSolutionOrientation`). -/
theorem theorem_6_6_18 (hX : PX.IsTame) (hf : B.IsScFredholmSectionTame f) (hP : B.IsProper f)
    (hgp : ∀ x, IsZeroAt P f x → B.IsGeneralPositionGerm f x)
    (o : SectionOrientation f hf.toIsScFredholmSection) :
    B.SolutionSetInGeneralPosition f ∧ IsNaturalSolutionOrientation f hf hgp o := by
  have := paracompactSpace_rn_prod PX
  have := paracompactSpace_rn_pullback B
  obtain ⟨h1, h2⟩ := theorem_6_41 hX hf hP hgp o.2
  exact ⟨h1, fun x hs hx0 c c' hc hc' hxc hxc' =>
    tangentOrAt_toChartOr hf.toIsScFredholmSection hs hx0 _ (o.1 x hs) hc hc' hxc hxc', h2⟩

end Polyfold
