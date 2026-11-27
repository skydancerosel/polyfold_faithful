import Polyfold.Chapter19.PolyfoldStructureGCT
import Polyfold.Chapter19.BasicRegularity
import Polyfold.Chapter17.ModelProperties
import Polyfold.Chapter1.CylinderScBanach
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
The abstract skeleton of HWZ, *Applications of Polyfold Theory I* (Memoirs AMS 248, no. 1179):
definitions of the concrete objects that Mathlib and the project can already express (the target
(Q, ω, J), nodal surfaces, stable maps, the sc-scale of the model spaces), the memoir's key analytic
results as named `Prop`-valued statements about them, and the first reductions to the book.
-/

set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff
open Set Function

noncomputable section

namespace GWMemoir

/-! ## 1. The target: `(Q, ω, J)` -/

section Target

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

variable (E M) in
/-- A smooth almost complex structure: a smooth field `J` of endomorphisms of `TM`, `J² = -1`.
Smoothness is read in tangent coordinates, as in Mathlib's `ContMDiffAt.mfderiv`. -/
structure AlmostComplexStructure where
  J : M → E →L[ℝ] E
  sq : ∀ x, (J x).comp (J x) = -ContinuousLinearMap.id ℝ _
  smooth : ∀ x₀ : M, ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E →L[ℝ] E) ∞
    (inTangentCoordinates 𝓘(ℝ, E) 𝓘(ℝ, E) id id J x₀) x₀

/-- A field of bilinear forms on `TM` read in the chart at `x₀`. -/
def inChart (σ : M → E →L[ℝ] E →L[ℝ] ℝ)
    (x₀ : M) : E → E →L[ℝ] E →L[ℝ] ℝ := fun y =>
  let x := (extChartAt 𝓘(ℝ, E) x₀).symm y
  (σ x).bilinearComp (tangentCoordChange 𝓘(ℝ, E) x₀ x x) (tangentCoordChange 𝓘(ℝ, E) x₀ x x)

variable (E M) in
/-- A symplectic form: smooth, antisymmetric, non-degenerate, closed.  `dω = 0` is the cyclic
identity for the chart expression (Mathlib has no exterior derivative on manifolds). -/
structure SymplecticForm where
  form : M → E →L[ℝ] E →L[ℝ] ℝ
  antisymm : ∀ x v w, form x v w = -form x w v
  nondeg : ∀ x v, (∀ w, form x v w = 0) → v = 0
  smooth : ∀ x₀ : M, ContDiffOn ℝ ∞ (inChart form x₀) (extChartAt 𝓘(ℝ, E) x₀).target
  closed : ∀ x₀ : M, ∀ y ∈ (extChartAt 𝓘(ℝ, E) x₀).target, ∀ a b c : E,
    fderiv ℝ (inChart form x₀) y a b c + fderiv ℝ (inChart form x₀) y b c a +
      fderiv ℝ (inChart form x₀) y c a b = 0

/-- `J` is `ω`-compatible: `ω(J·, J·) = ω` and `ω(v, Jv) > 0` for `v ≠ 0`. -/
def IsCompatible (om : SymplecticForm E M) (J : AlmostComplexStructure E M) : Prop :=
  (∀ x v w, om.form x (J.J x v) (J.J x w) = om.form x v w) ∧ ∀ x v, v ≠ 0 → 0 < om.form x v (J.J x v)

end Target

/-! ## 2. Noded Riemann surfaces (Memoir Definitions 1.2, 1.3) -/

/-- The model of a real surface. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- **Memoir Definition 1.2**: a noded Riemann surface `(S, j, M, D)` with `m` ordered marked
points: a closed smooth surface with an almost complex structure `j`, marked points, and a finite
set of unordered nodal pairs, connected after identifying nodal pairs. -/
structure NodalSurface (m : ℕ) where
  S : Type
  [top : TopologicalSpace S]
  [t2 : T2Space S]
  [cpt : CompactSpace S]
  [cs : ChartedSpace E2 S]
  [mf : IsManifold 𝓘(ℝ, E2) ∞ S]
  j : AlmostComplexStructure E2 S
  marked : Fin m ↪ S
  nodes : Set (Sym2 S)
  finite_nodes : nodes.Finite
  not_diag : ∀ p ∈ nodes, ¬ p.IsDiag
  disjoint : ∀ p ∈ nodes, ∀ q ∈ nodes, ∀ x, x ∈ p → x ∈ q → p = q
  marked_not_nodal : ∀ i, ∀ p ∈ nodes, marked i ∉ p
  connected : ConnectedSpace (Quot fun x y : S => s(x, y) ∈ nodes)

attribute [instance] NodalSurface.top NodalSurface.t2 NodalSurface.cpt NodalSurface.cs
  NodalSurface.mf

namespace NodalSurface

variable {m : ℕ}

/-- An isomorphism of noded Riemann surfaces: a diffeomorphism with `Tφ ∘ j = j' ∘ Tφ`,
preserving the ordered marked points and the nodal pairs. -/
structure Iso (X₁ X₂ : NodalSurface m) where
  φ : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) X₁.S X₂.S ∞
  holo : ∀ x, (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) φ x).comp (X₁.j.J x) =
    (X₂.j.J (φ x)).comp (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E2) φ x)
  marked : ∀ i, φ (X₁.marked i) = X₂.marked i
  nodes : Sym2.map φ '' X₁.nodes = X₂.nodes

/-- **Memoir Definition 1.3**: stable means a finite automorphism group. -/
def IsStable (X : NodalSurface m) : Prop := Finite (Iso X X)

variable (X : NodalSurface m)

/-- The special points `M ∪ |D|`. -/
def special : Set X.S := range X.marked ∪ {x | ∃ p ∈ X.nodes, x ∈ p}

/-- The genus of a closed connected surface, `rank H₁ / 2` with `H₁ = π₁^{ab}`. -/
def genusOf (C : Type) [TopologicalSpace C] (y : C) : ℕ :=
  Module.finrank ℤ (Additive (Abelianization (FundamentalGroup C y))) / 2

/-- The domain component through `x` is **not stable**, `2 g(C) + #Σ_C ≤ 2`, read without the
genus as a number: a sphere (simply connected) with at most two special points, or a torus
(abelian `π₁`) with none. -/
def IsUnstableComponent (x : X.S) : Prop :=
  (SimplyConnectedSpace (connectedComponent x) ∧
      (X.special ∩ connectedComponent x).ncard ≤ 2) ∨
    ((∀ (y : connectedComponent x) (a b : FundamentalGroup (connectedComponent x) y),
        a * b = b * a) ∧ X.special ∩ connectedComponent x = ∅)

/-- The arithmetic genus `g_a = 1 + #D + Σ_C (g(C) - 1)`. -/
def arithGenus : ℤ :=
  1 + X.nodes.ncard +
    ∑ᶠ C : ConnectedComponents X.S,
      ((genusOf (connectedComponent C.out) ⟨C.out, mem_connectedComponent⟩ : ℤ) - 1)

end NodalSurface

/-! ## 3. Maps of class `(k, δ)` (Memoir Definitions 1.1, 1.4, 1.5) -/

section StableMaps

open Polyfold.CylinderSobolev

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Q : Type} [TopologicalSpace Q] [ChartedSpace E Q] [IsManifold 𝓘(ℝ, E) ∞ Q]

/-- The exponential coordinate `e^{-2π(s + it)}` of positive polar coordinates. -/
def expPolar (p : ℝ × ℝ) : ℂ := Complex.exp (-2 * Real.pi * ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))

lemma continuous_expPolar : Continuous expPolar := by
  unfold expPolar; fun_prop

lemma expPolar_add_one (s t : ℝ) : expPolar (s, t + 1) = expPolar (s, t) := by
  simp only [expPolar]
  have : -2 * Real.pi * ((s : ℂ) + ((t + 1 : ℝ) : ℂ) * Complex.I) =
      -2 * Real.pi * ((s : ℂ) + (t : ℂ) * Complex.I) + (-1 : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

namespace NodalSurface

variable {m : ℕ} (X : NodalSurface m)

/-- A `j`-holomorphic chart centred at `x`. -/
def IsHolChart (φ : OpenPartialHomeomorph X.S ℂ) (x : X.S) : Prop :=
  x ∈ φ.source ∧ φ x = 0 ∧ ∀ y ∈ φ.source, MDifferentiableAt 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) φ y ∧
    ∀ v, (show ℂ from mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) φ y (X.j.J y v)) =
      Complex.I * (show ℂ from mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, ℂ) φ y v)

/-- Positive holomorphic polar coordinates `σ(s, t) = φ⁻¹(e^{-2π(s + it)})`. -/
def polar (φ : OpenPartialHomeomorph X.S ℂ) : ℝ × ℝ → X.S := fun p =>
  φ.symm (Complex.exp (-2 * Real.pi * ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)))

lemma polar_eq (φ : OpenPartialHomeomorph X.S ℂ) (p : ℝ × ℝ) :
    X.polar φ p = φ.symm (expPolar p) := rfl

lemma polar_mem_source {φ : OpenPartialHomeomorph X.S ℂ} {p : ℝ × ℝ}
    (hp : expPolar p ∈ φ.target) : X.polar φ p ∈ φ.source :=
  φ.map_target hp

lemma polar_add_one (φ : OpenPartialHomeomorph X.S ℂ) (s t : ℝ) :
    X.polar φ (s, t + 1) = X.polar φ (s, t) := by
  rw [polar_eq, polar_eq, expPolar_add_one]

/-- Honest polar coordinates are continuous: if `e^{-2π(s+it)} ∈ φ.target` for `s ≥ s₀`, then
`σ` is continuous on `s ≥ s₀`. -/
lemma continuousOn_polar {φ : OpenPartialHomeomorph X.S ℂ} {s₀ : ℝ}
    (h : ∀ p : ℝ × ℝ, s₀ ≤ p.1 → expPolar p ∈ φ.target) :
    ContinuousOn (X.polar φ) {p | s₀ ≤ p.1} :=
  φ.continuousOn_symm.comp continuous_expPolar.continuousOn fun p hp => h p hp

/-- **Memoir Definition 1.1**: `u` is of class `(k, δ)` near `x`: in polar coordinates at `x`
and the chart of `Q` at `u(x)` (centred), `e^{δs}`-weighted weak derivatives up to order `k` are
`L²` on `[s₀, ∞) × S¹`; written with the project's `H^{k,δ}(ℝ × S¹)` and a cut-off.  The polar
coordinates are honest ones: `e^{-2π(s+it)}` lies in the image of the chart for `s ≥ s₀`, so `σ`
is continuous there (`continuousOn_polar`) and `σ(s, t) → x` as `s → ∞`. -/
def IsClassNear (k : ℕ) (δ : ℝ) (u : X.S → Q) (x : X.S) : Prop :=
  ∃ φ, X.IsHolChart φ x ∧ ∃ s₀ : ℝ,
    (∀ p : ℝ × ℝ, s₀ ≤ p.1 → expPolar p ∈ φ.target ∧
      u (X.polar φ p) ∈ (extChartAt 𝓘(ℝ, E) (u x)).source) ∧
    ∀ ℓ : E →L[ℝ] ℝ, MemH k δ fun p => Real.smoothTransition (p.1 - s₀) *
      ℓ (extChartAt 𝓘(ℝ, E) (u x) (u (X.polar φ p)) - extChartAt 𝓘(ℝ, E) (u x) (u x))

/-- The square-to-chart placement `p ↦ κ(x) + ε (s, t - 1/2)` used for local `H^k`. -/
def place (x : X.S) (ε : ℝ) (p : ℝ × ℝ) : E2 :=
  extChartAt 𝓘(ℝ, E2) x x + ε • (EuclideanSpace.single 0 p.1 + EuclideanSpace.single 1 (p.2 - 1/2))

/-- `u` is of class `H^k_loc` near `x`: a cut-off of its chart expression, placed in the strip
`ℝ × (0, 1)`, lies in `H^{k,0}(ℝ × S¹)`. -/
def IsHlocNear (k : ℕ) (u : X.S → Q) (x : X.S) : Prop :=
  ∃ ε > 0, (∀ p : ℝ × ℝ, p.1 ^ 2 + (p.2 - 1/2) ^ 2 < 1/8 →
      X.place x ε p ∈ (extChartAt 𝓘(ℝ, E2) x).target ∧
      u ((extChartAt 𝓘(ℝ, E2) x).symm (X.place x ε p)) ∈ (extChartAt 𝓘(ℝ, E) (u x)).source) ∧
    ∀ ℓ : E →L[ℝ] ℝ, MemH k 0 fun p => Real.smoothTransition (2 - 16 * (p.1 ^ 2 + (p.2 - 1/2) ^ 2)) *
      ℓ (extChartAt 𝓘(ℝ, E) (u x) (u ((extChartAt 𝓘(ℝ, E2) x).symm (X.place x ε p))))

/-- The integral of a field of bilinear forms over the chart at `x₀`, with the orientation of
`j` (the sign of the `e₁`-component of `j e₀`). -/
def chartIntegral (x₀ : X.S) (σ : X.S → E2 →L[ℝ] E2 →L[ℝ] ℝ) : ℝ :=
  ∫ y in (extChartAt 𝓘(ℝ, E2) x₀).target,
    let x := (extChartAt 𝓘(ℝ, E2) x₀).symm y
    let T := tangentCoordChange 𝓘(ℝ, E2) x₀ x x
    let Ti := tangentCoordChange 𝓘(ℝ, E2) x x₀ x
    (SignType.sign ((Ti (X.j.J x (T (EuclideanSpace.single 0 1)))) 1) : ℝ) *
      σ x (T (EuclideanSpace.single 0 1)) (T (EuclideanSpace.single 1 1))

/-- `∫_S σ` through a smooth partition of unity subordinate to the charts. -/
def surfaceIntegral (σ : X.S → E2 →L[ℝ] E2 →L[ℝ] ℝ) : ℝ :=
  let ρ := (SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source 𝓘(ℝ, E2) X.S).choose
  ∑ᶠ i : X.S, X.chartIntegral i fun y => ρ i y • σ y

/-- `∫_C u*ω` over the domain component `C` through `x`. -/
def area (om : SymplecticForm E Q) (u : X.S → Q) (x : X.S) : ℝ :=
  X.surfaceIntegral fun y => (connectedComponent x).indicator
    (fun y => (om.form (u y)).bilinearComp (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) u y)
      (mfderiv 𝓘(ℝ, E2) 𝓘(ℝ, E) u y)) y

end NodalSurface

variable (om : SymplecticForm E Q)

/-- **Memoir Definition 1.4**: a stable map `(S, j, M, D, u)` of class `(k, δ)`. -/
structure StableMap (m k : ℕ) (δ : ℝ) where
  dom : NodalSurface m
  u : dom.S → Q
  continuous : Continuous u
  nodal : ∀ p ∈ dom.nodes, ∀ x ∈ p, dom.IsClassNear (E := E) k δ u x
  regular : ∀ x, (∀ p ∈ dom.nodes, x ∉ p) → dom.IsHlocNear (E := E) k u x
  matching : ∀ x y, s(x, y) ∈ dom.nodes → u x = u y
  area_nonneg : ∀ x, 0 ≤ dom.area om u x
  stable : ∀ x, dom.IsUnstableComponent x → 0 < dom.area om u x

variable {om}

/-- An isomorphism of stable maps: `φ : (S, j, M, D) → (S', j', M', D')` with `u' ∘ φ = u`. -/
structure StableMap.Iso {m k : ℕ} {δ : ℝ} (α β : StableMap om m k δ) where
  φ : α.dom.Iso β.dom
  comm : ∀ x, β.u (φ.φ x) = α.u x

variable (om) in
/-- The finiteness of isomorphism sets (Definition 19.1.1 (2) for the category of stable maps):
the classical input that a stable map has finitely many automorphisms. -/
def FiniteIsos (m : ℕ) (δ₀ : ℝ) : Prop :=
  ∀ α β : StableMap om m 3 δ₀, Finite (StableMap.Iso α β)

end StableMaps

/-! ## 4. The sc-scale `H^{3+m, δ_m}(ℝ × S¹)` with `δ₀ > 0` -/

section Scale

open Polyfold Polyfold.CylinderSobolev

/-- The scale `E_m = H^{3+m, δ_m}(ℝ × S¹)` of the memoir (`δ₀ ≥ 0`, `δ` strictly increasing),
from the project's cylinder spaces. -/
def scaleGW (δ : ℕ → ℝ) (h0 : 0 ≤ δ 0) (hmono : StrictMono δ) : ScScale where
  lvl m := H (3 + m) (h0.trans (hmono.monotone (Nat.zero_le m)))
  incl m := inclH _ _ (Nat.le_succ (3 + m)) (hmono (Nat.lt_succ_self m)).le
  incl_injective _ := inclH_injective _ _ _ _
  incl_isCompactOperator m := isCompactOperator_inclH _ _ (hmono (Nat.lt_succ_self m))

end Scale

/-! ## 5. The named propositions, through the book's Part IV

`C` will be the category of stable maps of class `(3, δ₀)` (objects `StableMap om m 3 δ₀`,
morphisms `Σ α β, StableMap.Iso α β`, finiteness from `FiniteIsos`) and `U` the uniformizer
construction of good uniformizing families (Memoir Definition 3.9).  Here both are variables, to
check that the statements and the reduction typecheck against Chapters 17 and 19. -/

section PartIV

open Polyfold Polyfold.GroupoidalCategory TopologicalSpace

variable {C : GroupoidalCategory.{1}} (U : C.UniformizerConstruction)

/-- `Φ : V → M(Ψ, Ψ')` is a transition germ at `h`: `Φ(s h) = h`, `s ∘ Φ = id` on `V`, and
`t ∘ Φ` an sc-diffeomorphism onto an open set; `CS` is core-smoothness of `q ↦ φ_q`. -/
def IsTransGerm (CS : ∀ Ψ Ψ' : U.Unif, (Ψ.1.O → Ψ.1.Trans Ψ'.1) → Set Ψ.1.O → Prop)
    (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1) (V : Set Ψ.1.O) (Φ : Ψ.1.O → Ψ.1.Trans Ψ'.1) : Prop :=
  IsOpen V ∧ h.src ∈ V ∧ Φ h.src = h ∧ (∀ q ∈ V, (Φ q).src = q) ∧
    (∃ g, Ψ.1.P.IsScDiffeoOn Ψ'.1.P (fun q => (Φ q).tgt) g V ((fun q => (Φ q).tgt) '' V)) ∧
    CS Ψ Ψ' Φ V

/-- **Memoir Theorem 3.13**: every morphism `φ₀ : α_{q₀} → α'_{q₀'}` extends to a transition
germ, and the germ is unique. -/
def Theorem_3_13 (CS : ∀ Ψ Ψ' : U.Unif, (Ψ.1.O → Ψ.1.Trans Ψ'.1) → Set Ψ.1.O → Prop) : Prop :=
  ∀ (Ψ Ψ' : U.Unif) (h : Ψ.1.Trans Ψ'.1),
    (∃ V Φ, IsTransGerm U CS Ψ Ψ' h V Φ) ∧
    ∀ V₁ Φ₁ V₂ Φ₂, IsTransGerm U CS Ψ Ψ' h V₁ Φ₁ → IsTransGerm U CS Ψ Ψ' h V₂ Φ₂ →
      ∃ W : Set Ψ.1.O, IsOpen W ∧ h.src ∈ W ∧ W ⊆ V₁ ∩ V₂ ∧ EqOn Φ₁ Φ₂ W

/-- The reduction to be proved first (abstract): Theorem 3.13 gives transition data, (A)–(F) of
the Properties (19.3). -/
def Reduction_3_13 (CS : ∀ Ψ Ψ' : U.Unif, (Ψ.1.O → Ψ.1.Trans Ψ'.1) → Set Ψ.1.O → Prop) :
    Prop :=
  Theorem_3_13 U CS → Nonempty U.TransitionData

/-- The basic construction `(F, [T])`. -/
def basicOf (T : U.TransitionData) : C.BasicConstruction := ⟨U, ⟦T⟧⟩

/-- **Memoir Theorem 3.22** is the properness condition (v1) of Definition 19.4.1. -/
def Theorem_3_22 (T : U.TransitionData) : Prop := (basicOf U T).PropernessV1

/-- **Memoir Theorem 1.6**, the second countability part (Lemmas 3.32–3.34). -/
def Theorem_1_6_sc (T : U.TransitionData) (hB : U.HasClassUniformizers) : Prop :=
  @SecondCountableTopology _ ((basicOf U T).natTop hB)

/-- Proved reduction: Theorems 3.22 and 1.6 (second countable) give a metrizable `Z`
(Proposition 19.4.2, Theorem 19.5.3 (1)). -/
theorem metrizable_of_theorem_3_22 (T : U.TransitionData) (hB : U.HasClassUniformizers)
    (h322 : Theorem_3_22 U T) (h16 : Theorem_1_6_sc U T hB) :
    @MetrizableSpace C.OrbitSpace ((basicOf U T).natTop hB) :=
  (basicOf U T).theorem_19_5_3_one hB
    (((basicOf U T).proposition_19_4_2_one_iff_two hB).1 h322) (Or.inl h16)

/-- Proved reduction: with (ZHOU) for the basic construction (Definition 19.5.6), the polyfold
class on `Z` (Theorem 19.5.3 (2), Proposition 19.5.7, Theorem 17.1.26). -/
def gwPolyfoldClass (T : U.TransitionData) (hB : U.HasClassUniformizers)
    (hm : @MetrizableSpace C.OrbitSpace ((basicOf U T).natTop hB))
    (hz : (basicOf U T).IsZhou) :
    PolyfoldClass ((basicOf U T).toGCTOfMetrizable hB hm).toGroupoidStr.OrbitSpace :=
  (BasicConstruction.toPolyfoldConstruction hm).polyfoldClass
    (BasicConstruction.proposition_19_5_7 hm hz)

end PartIV

end GWMemoir
