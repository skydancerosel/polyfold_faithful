import Polyfold
/-! Blind formalization of V8_26 (the text's Part II, §8.3, Definition 8.3.4 = 2017 Definition
8.7, pp. 379 ff. / 2017 pp. 274–275).

Text: for a strong bundle `(P : W → X, μ)` over the ep-groupoid `X`: (1) an sc-smooth section
functor is an sc-smooth section `f : X → W` of `P` with `f(y) = μ(φ, f(x))` for morphisms
`φ : x → y`; `Γ(P, μ)` is the vector space of these.  (2) An sc⁺-section functor is an
`f ∈ Γ(P, μ)` with `f(x) ∈ W_{0,1}` for all `x` which, as a section of `W[1] → X`, is sc-smooth;
`Γ⁺(P, μ) ⊆ Γ(P, μ)` is the vector subspace of these.  (3) An sc-Fredholm section functor is an
`f ∈ Γ(P, μ)` which, as a section of `W → X`, is sc-Fredholm; `Fred(P, μ)` is their collection.

Choices:
- This item is a definition (three notions, three sets) plus the presupposition that `Γ` and
  `Γ⁺` are vector spaces.  Setting as in my `RoundTrip/Blind/V8_20.lean`: `X : EpGroupoid Obj Mor`,
  `W : Type`, `B : StrongBundle X.PObj P`, `E : EpStrongBundle X B` (V8_20), `μ = E.μ`.
- (1) "sc-smooth section of `P`": `P ∘ f = id` and `f` sc-smooth `X → W[0]` (`B.toMPolyfold0`;
  Definition 2.52 as read in `RoundTrip/Blind/V2_59.lean`).  The functorial condition for every
  morphism `φ` with `s φ = x`, `t φ = y`, with the membership `(φ, f(x)) ∈ 𝐗 ₛ×_P W` as a
  hypothesis (it holds for a section).
- (2) `W_{0,1}` is the project's `B.oneSet` (identified with the text's `Y_{0,1}` in V2_58);
  "sc-smooth as a section of `W[1] → X`": the corestriction to `W[1]` (`B.One`, inclusion
  `B.oneVal`) is sc-smooth into `B.toMPolyfold1`, as in V2_59.
- (3) "sc-Fredholm section of `W → X`": the project's Part I notion
  `StrongBundle.IsScFredholmSection` (Definition 3.14 in the germ reading); I trust it as the
  text's notion.
- "vector space", "vector subspace": the operations are the fibrewise ones, `(f + g)(x) =
  f(x) + g(x)`, `(c f)(x) = c · f(x)` in `W_x`, zero `x ↦ 0_x` (my `addB`, `smulB`, `zeroB`,
  defined for sections, the section property passed as an argument).  B asserts that `Γ` and `Γ⁺`
  contain the zero section and are closed under these operations, and `Γ⁺ ⊆ Γ` (the vector-space
  axioms then hold fibrewise).
- B also says that the project's `IsScSmoothSectionFunctor`, `IsScPlusSectionFunctor`,
  `IsScFredholmSectionFunctor` and `sectionFunctors`, `plusSectionFunctors`,
  `fredholmSectionFunctors` are these notions and sets.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_26
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

/-- `f` is a section of `P`. -/
def IsSectionB (P : W → Obj) (f : Obj → W) : Prop :=
  ∀ x : Obj, P (f x) = x

/-- The zero section `x ↦ 0_x`. -/
def zeroB (P : W → Obj) [∀ x, AddCommGroup (P ⁻¹' {x})] : Obj → W :=
  fun x => ((0 : P ⁻¹' {x}) : W)

/-- The fibrewise sum `(f + g)(x) = f(x) + g(x)` of two sections. -/
def addB (P : W → Obj) [∀ x, AddCommGroup (P ⁻¹' {x})] (f g : Obj → W) (hf : IsSectionB P f)
    (hg : IsSectionB P g) : Obj → W :=
  fun x => (((⟨f x, hf x⟩ : P ⁻¹' {x}) + ⟨g x, hg x⟩ : P ⁻¹' {x}) : W)

/-- The fibrewise multiple `(c f)(x) = c · f(x)` of a section. -/
def smulB (P : W → Obj) [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (c : ℝ)
    (f : Obj → W) (hf : IsSectionB P f) : Obj → W :=
  fun x => ((c • (⟨f x, hf x⟩ : P ⁻¹' {x}) : P ⁻¹' {x}) : W)

/-- **Definition 8.3.4 (1)**: an sc-smooth section functor. -/
def IsScSmoothSectionFunctorB (E : EpStrongBundle X B) (f : Obj → W) : Prop :=
  IsSectionB P f ∧ X.PObj.IsScSmoothMap B.toMPolyfold0 f ∧
  ∀ (φ : Mor) (x y : Obj), X.src φ = x → X.tgt φ = y →
    ∀ h : P (f x) = X.src φ, f y = E.μ ⟨(φ, f x), h⟩

/-- `Γ(P, μ)`. -/
def GammaB (E : EpStrongBundle X B) : Set (Obj → W) :=
  {f | IsScSmoothSectionFunctorB E f}

/-- **Definition 8.3.4 (2)**: an sc⁺-section functor. -/
def IsScPlusSectionFunctorB (E : EpStrongBundle X B) (f : Obj → W) : Prop :=
  f ∈ GammaB E ∧ (∀ x : Obj, f x ∈ B.oneSet) ∧
  ∃ g : Obj → B.One, (∀ x : Obj, B.oneVal (g x) = f x) ∧ X.PObj.IsScSmoothMap B.toMPolyfold1 g

/-- `Γ⁺(P, μ)`. -/
def GammaPlusB (E : EpStrongBundle X B) : Set (Obj → W) :=
  {f | IsScPlusSectionFunctorB E f}

/-- **Definition 8.3.4 (3)**: an sc-Fredholm section functor. -/
def IsScFredholmSectionFunctorB (E : EpStrongBundle X B) (f : Obj → W) : Prop :=
  f ∈ GammaB E ∧ B.IsScFredholmSection f

/-- `Fred(P, μ)`. -/
def FredB (E : EpStrongBundle X B) : Set (Obj → W) :=
  {f | IsScFredholmSectionFunctorB E f}

/-- `S` contains the zero section and is closed under the fibrewise linear operations. -/
def IsSectionSubspaceB (P : W → Obj) [∀ x, AddCommGroup (P ⁻¹' {x})]
    [∀ x, Module ℝ (P ⁻¹' {x})] (S : Set (Obj → W)) : Prop :=
  zeroB P ∈ S ∧
  (∀ (f g : Obj → W) (hf : IsSectionB P f) (hg : IsSectionB P g), f ∈ S → g ∈ S →
    addB P f g hf hg ∈ S) ∧
  (∀ (c : ℝ) (f : Obj → W) (hf : IsSectionB P f), f ∈ S → smulB P c f hf ∈ S)

end

/-- Definition 8.3.4: the project's section functors are the text's, and `Γ(P, μ)`,
`Γ⁺(P, μ) ⊆ Γ(P, μ)` are vector spaces of sections. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    (E : EpStrongBundle X B),
    -- (1) sc-smooth section functors and `Γ(P, μ)`, a vector space
    (∀ f : Obj → W, E.IsScSmoothSectionFunctor f ↔ IsScSmoothSectionFunctorB E f) ∧
    E.sectionFunctors = GammaB E ∧
    IsSectionSubspaceB P (GammaB E) ∧
    -- (2) sc⁺-section functors and `Γ⁺(P, μ)`, a vector subspace of `Γ(P, μ)`
    (∀ f : Obj → W, E.IsScPlusSectionFunctor f ↔ IsScPlusSectionFunctorB E f) ∧
    E.plusSectionFunctors = GammaPlusB E ∧
    GammaPlusB E ⊆ GammaB E ∧
    IsSectionSubspaceB P (GammaPlusB E) ∧
    -- (3) sc-Fredholm section functors and `Fred(P, μ)`
    (∀ f : Obj → W, E.IsScFredholmSectionFunctor f ↔ IsScFredholmSectionFunctorB E f) ∧
    E.fredholmSectionFunctors = FredB E

end RoundTrip.V8_26
