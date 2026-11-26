import GWMemoir.CauchyRiemannFredholm
import Polyfold.Chapter16.InvariantUnconditional
import Polyfold.Chapter16.FormsPullback

/-!
Hofer–Wysocki–Zehnder, *Applications of Polyfold Theory I: The Polyfolds of Gromov–Witten
Theory*, Memoirs AMS 248 (2017), **Theorem 1.12** (p. 9), primary form, compared with the book
(*Polyfold and Fredholm Theory*, Springer 2021): Theorem 16.6.6 (p. 739), Theorem 16.6.4,
Proposition 16.3.10, the pull-back of sc-differential forms (p. 721).

## The memoir, paraphrased

(Theorem 1.12) For a closed symplectic manifold `(Q, ω)`, `A ∈ H₂(Q)` and `2g + m ≥ 3`, there is
a multilinear map `Ψ^Q_{A,g,m}`, given for a compatible `J` and a small generic perturbation by an
sc⁺-multisection `λ` by `∫_{(S(∂̄_J, λ), ϑ)} γ^*(PD τ) ∧ ev₁^*α₁ ∧ … ∧ ev_m^*α_m`.  (p. 9) By
Gromov compactness the solution set on `Z_{A,g,m}` is compact; the perturbed solution set is a
compact branched oriented suborbifold of dimension `Ind(∂̄_J)`.

## What is formalized (namespace `GWMemoir`)

* `invariant_wellDefined`: for an sc-Fredholm section `s` of a strong polyfold bundle over a
  polyfold without boundary admitting sc-smooth bump functions, with compact solution set and an
  orientation of index `m + 1` with tame germs, and an sc-smooth map `ev : Z → W'` to a polyfold
  class: there are an auxiliary norm `n` and an open `U` controlling compactness (Proposition
  16.3.10, Theorem 16.6.4), admissible perturbations exist, and for two admissible perturbations
  `∫ ev^*(τ + dη) = ∫ ev^*τ` for every closed `τ` and every `η` (Theorem 16.6.6, Stokes).
* **`memoir_theorem_1_12`**: the same for `∂̄_J` of `memoir_theorem_1_11`, with the named
  propositions: Gromov compactness (`GromovCompactness`), the orientation of Theorem 4.6 on the
  model functor (`OrientationRep` with `o.a` the model representative), the index formula
  (`Index_4_6`), bump functions and `∂Z = ∅` for `Z`.  Tameness is proved
  (`memoir_theorem_1_11`).

## Readings

* The integrand `γ^*(PD τ) ∧ ev^*α` is one closed sc-form `ev^*τ` for the map
  `(γ, ev₁, …, ev_m) : Z → M_{g,m} × Q^m`; the target is taken as a polyfold class `W'`, and
  `τ` as a closed sc-form on it.  The passage from the manifold `M_{g,m} × Q^m` and its
  de Rham forms to a finite-dimensional polyfold and `ScForm` is not formalized here.
* The component `Z_{A,g,m}` enters through the groupoidal category `C` with its label
  (`StableMapLabel`); a component is a full subcategory of stable maps closed under isomorphism
  (for instance of a given class `A`, hence of the energy `ω(A)`).
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Filter
open scoped Manifold ContDiff

noncomputable section

namespace GWMemoir

open Polyfold Polyfold.StrongPolyfoldBundle Polyfold.PolyfoldClass Polyfold.SBLocalization

/-! ### The invariant for a strong polyfold bundle -/

section Abstract

universe u

variable {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z] {p : Y → Z}
  {c : StrongPolyfoldBundle p} {W' : Type u} [TopologicalSpace W'] {d : PolyfoldClass W'}

/-- The pull-back of a closed form is closed (`d ∘ f^* = f^* ∘ d`, 2021 p. 721). -/
theorem d_pullback_eq_zero (ev : ScMap c.polyfold d) {k : ℕ} {τ : ScForm d k}
    (hτ : ScForm.d τ = 0) : ScForm.d (ScMap.pullback ev k τ) = 0 := by
  have h := LinearMap.congr_fun (ScMap.d_comp_pullback ev k) τ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hτ, map_zero] at h
  exact h

/-- **The invariant of Theorem 16.6.6 for `ev^*τ`** (2021 Theorem 16.6.6, p. 739, with
Proposition 16.3.10 and Theorem 16.6.4 for the controlling pair `(n, U)`): admissible
perturbations inheriting the orientation `o` exist, and `∫ ev^*τ` over the perturbed solution
set is the same for any two of them and depends only on `τ` up to an exact form. -/
theorem invariant_wellDefined (hbump : c.polyfold.AdmitsBumpFunctions)
    (hbd : c.polyfold.boundary = ∅) {s : FredholmSection c} (hcs : s.1.HasCompactSolutionSet)
    {m : ℕ} {o : OrientationRep s} (H : CanonicalInput_all o (m + 1)) (ev : ScMap c.polyfold d) :
    ∃ (n : Y → ℝ) (U : Set Z), s.1.ControlsCompactness n U ∧
      (∃ P : OrientedPerturbation s.1 m, P.IsAdmissible n U ∧
        IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o P) ∧
      ∀ P₀ P₁ : OrientedPerturbation s.1 m, P₀.IsAdmissible n U →
        IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o P₀ →
        P₁.IsAdmissible n U →
        IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o P₁ →
        ∀ τ : ScForm d (m + 1), ScForm.d τ = 0 → ∀ η : ScForm d m,
          P₀.integral (ScMap.pullback ev (m + 1) (τ + ScForm.d η)) =
            P₁.integral (ScMap.pullback ev (m + 1) τ) := by
  obtain ⟨n, hn⟩ := proposition_16_3_10 (c := c)
  have hprop : s.1.IsProper := ((theorem_16_6_4 s).out 0 1).1 hcs
  obtain ⟨U, hU, hsU, hcpt⟩ := hprop.2 n hn
  have hcc : s.1.ControlsCompactness n U := ⟨hn, hU, hsU, hcpt⟩
  obtain ⟨hex, hind⟩ := theorem_16_6_6_canonical_wellDefined_all hbump hbd hcs hn hU hcc H
  refine ⟨n, U, hcc, hex, fun P₀ P₁ h₀ i₀ h₁ i₁ τ hτ η => ?_⟩
  have hpull : ScMap.pullback ev (m + 1) (τ + ScForm.d η) =
      ScMap.pullback ev (m + 1) τ + ScForm.d (ScMap.pullback ev m η) := by
    rw [map_add]
    congr 1
    have h := LinearMap.congr_fun (ScMap.d_comp_pullback ev m) η
    rw [LinearMap.comp_apply, LinearMap.comp_apply] at h
    exact h.symm
  rw [hpull]
  have hstokes : P₀.integral (ScMap.pullback ev (m + 1) τ + ScForm.d (ScMap.pullback ev m η)) =
      P₀.integral (ScMap.pullback ev (m + 1) τ) :=
    OrientedSuborbifold.integral_add_d_all hbd _ _ _ _ _
  rw [hstokes]
  exact (hind P₀ P₁ h₀ i₀ h₁ i₁ _ (d_pullback_eq_zero ev hτ)).1

end Abstract

/-! ### Memoir Theorem 1.12 -/

section GW

open GroupoidalCategory GroupoidalCategory.BasicConstruction
  GCT.VectorBundle.StrongPolyfoldBundleConstruction

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]
  {om : SymplecticForm E Q} {m k : ℕ} {δ : ℝ} {J : AlmostComplexStructure E Q} {k' : ℕ} {δ' : ℝ}

variable {C : GroupoidalCategory.{1}} {U : C.UniformizerConstruction} {CS : CSPred U}
  {h310 : U.HasClassUniformizers} {H : Theorem_3_13 U CS} {hCS : CSClosed U CS}
  {hPF : PointFinite U}
  {h322 : Theorem_3_22 U (gwTransitionData H hCS hPF)}
  {h16 : Theorem_1_6_sc U (gwTransitionData H hCS hPF) h310}
  {hTF : ∀ (α : C.Obj), ∀ Ψ ∈ U.F α, ∀ y : Ψ.P.SmoothLevel, IsTangentFaithfulAt Ψ y}
  {hLF : ∀ (α : C.Obj), ∀ Ψ ∈ U.F α, IsLocallyFaithful Ψ}
  {V : (gwGCT h310 H hCS hPF h322 h16).VectorBundle}
  {Fb : V.StrongBundleUniformizerConstruction (gwPolyfoldConstruction h310 H hCS hPF h322 h16)}
  {h339 : Proposition_3_39 Fb} {L : StableMapLabel om m k δ C}
  {ιV : FibreIdentification L V.toBanachFunctor J k' δ'}
  {c : (ofProposition_3_39 Fb h339).BundleCoveringFamily}

variable (hTF hLF Fb h339 ιV c) in
/-- **Gromov compactness** (memoir p. 9, Remark 4.10): the solution set of `∂̄_J` on the
component is compact. -/
def GromovCompactness (h : CRProps Fb h339 ιV c) : Prop :=
  (dbarSection hTF hLF Fb h339 ιV c h).1.HasCompactSolutionSet

/-- **The index formula of Memoir Theorem 4.6** (p. 101, Riemann–Roch): the Fredholm index of
the representative of the orientation is `d` at every smooth point, `d = 2n(1 − g) + 2c₁(A) +
6g − 6 + 2k` on `Z_{g,k,A}`. -/
def Index_4_6 {h : CRProps Fb h339 ιV c} (o : OrientationRep (dbarSection hTF hLF Fb h339 ιV c h))
    (d : ℕ) : Prop :=
  ∀ x ∈ o.a.S.A.X.PObj.smoothSet, o.a.S.A.B.IsIndexAt o.a.F x (d : ℤ)

/-- **Memoir Theorem 1.12, primary form, from the named propositions** (p. 9; 2021 Theorem
16.6.6): with the hypotheses of `memoir_theorem_1_11`, Gromov compactness, the orientation of
Theorem 4.6 on the model functor with index `m' + 1`, sc-smooth bump functions and `∂Z = ∅`,
and an sc-smooth map `ev : Z → W'`: admissible perturbations of `∂̄_J` exist, and
`∫_{S(∂̄_J, λ)} ev^*τ` is the same for any two of them and depends only on the class of the
closed form `τ`. -/
theorem memoir_theorem_1_12 (h : CRProps Fb h339 ιV c)
    (hbump : (gwBundle hTF hLF Fb h339 c).polyfold.AdmitsBumpFunctions)
    (hbd : (gwBundle hTF hLF Fb h339 c).polyfold.boundary = ∅)
    (hcs : GromovCompactness hTF hLF Fb h339 ιV c h)
    {m' : ℕ} (o : OrientationRep (dbarSection hTF hLF Fb h339 ιV c h))
    (ho : o.a = sectionRepOfFunctor (gwStructure hTF hLF Fb h339 c) rfl _
      (dbarFunctor_mem_fredholm h).1)
    (hidx : Index_4_6 o (m' + 1))
    {W' : Type 1} [TopologicalSpace W'] {d : PolyfoldClass W'}
    (ev : ScMap (gwBundle hTF hLF Fb h339 c).polyfold d) :
    ∃ (n : V.groupoid.OrbitSpace → ℝ) (U' : Set C.OrbitSpace),
      (dbarSection hTF hLF Fb h339 ιV c h).1.ControlsCompactness n U' ∧
      (∃ P : OrientedPerturbation (dbarSection hTF hLF Fb h339 ιV c h).1 m', P.IsAdmissible n U' ∧
        IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o P) ∧
      ∀ P₀ P₁ : OrientedPerturbation (dbarSection hTF hLF Fb h339 ιV c h).1 m',
        P₀.IsAdmissible n U' →
        IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o P₀ →
        P₁.IsAdmissible n U' →
        IsInheritedFrom (fun o P => IsCanonicalPerturbation o.hF.2 o.hsec o.o P) o P₁ →
        ∀ τ : ScForm d (m' + 1), ScForm.d τ = 0 → ∀ η : ScForm d m',
          P₀.integral (ScMap.pullback ev (m' + 1) (τ + ScForm.d η)) =
            P₁.integral (ScMap.pullback ev (m' + 1) τ) := by
  have htame : o.a.S.A.B.IsScFredholmSectionTame o.a.F := by
    rw [ho]
    exact (memoir_theorem_1_11 hTF hLF Fb h339 ιV c h).1
  exact invariant_wellDefined hbump hbd hcs ⟨htame, hidx⟩ ev

end GW

end GWMemoir
