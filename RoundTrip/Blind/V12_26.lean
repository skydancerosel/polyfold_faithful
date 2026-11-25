import Polyfold
/-! Blind formalization of V12_26 (the text's Part II, §12.5, Proposition 12.5.6, p. 595 of the
Springer 2021 book; 2017: Proposition 12.4).

Text: `f` is orientable if and only if `|σ| : |O_f| → |X_∞|` is two-to-one and has a global
continuous section.

Choices:
- Setting, `O_f`, `σ` and the topology of `O_f` as in `RoundTrip/Blind/V12_24.lean` (the §12.5
  setting: a strong bundle over a tame ep-groupoid, `f` an sc-Fredholm section functor; Part I's
  topology `orTopology (orLocalTransport …)`, which in the project needs the extra hypotheses
  bump functions, `IsScFredholmSectionTame f`, `HasScPlusSectionsThrough` and paracompactness
  instances; B quantifies over them).
- `|O_f|`: the quotient of `O_f` by `(x, o) ~ (x', φ_* o)` for morphisms `φ : x → x'` between
  smooth objects, the project's `Quot (E.OrRel hF hsec)` (read with `#print`; `φ_*` is
  `EpStrongBundle.orMor`, trusted from its docstring, p. 593), with the quotient topology;
  `|X_∞| = Quot X.SmoothRel` (smooth objects modulo morphisms, read with `#print`) with the
  quotient topology of `X_∞ ⊆ X`; `|σ|` the induced map `E.orbitProj` (read with `#print`:
  `Quot.map orProj`).
- "orientable": `f` admits an orientation (Definition 12.5.4): a section `x ↦ o_x ∈ Or_x^f` of
  `σ` over all of `X_∞`, continuous `X_∞ → O_f`, with `φ_* o_x = o_{x'}` for every morphism
  `φ : x → x'` between smooth objects.  (Written out myself; it agrees with the project's
  `definition_12_5_4` as printed.)
- "two-to-one": every point of `|X_∞|` has exactly two preimages under `|σ|`.  "global
  continuous section": a continuous `g : |X_∞| → |O_f|` with `|σ| ∘ g = id`.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V12_26
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × (Fin n → ℝ) × Obj)]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]
  {f : Obj → W}

/-- Part I's topology on `O_f` (Theorem 6.6.17), for the object bundle `W → X`. -/
noncomputable abbrev topO (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions)
    (hfT : B.IsScFredholmSectionTame f) (hsec : B.HasScPlusSectionsThrough)
    (hf : B.IsScFredholmSection f) : TopologicalSpace (OrSpace f hf) :=
  orTopology (hf := hf) (orLocalTransport hX hbump hfT hsec)

end

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)] {f : Obj → W}

/-- **An orientation of `f`** (Definition 12.5.4) for a topology `t` on `O_f`: a global section
`x ↦ o_x` of `σ`, continuous `X_∞ → O_f`, invariant under the morphisms. -/
def IsOrientationB (E : EpStrongBundle X B) (hF : E.IsScFredholmSectionFunctor f)
    (hsec : B.HasScPlusSectionsThrough) (t : TopologicalSpace (OrSpace f hF.2))
    (o : (x : Obj) → (hs : x ∈ X.PObj.smoothSet) → Orx f hF.2 x hs) : Prop :=
  @Continuous X.PObj.SmoothLevel (OrSpace f hF.2) _ t
      (fun y => (Sigma.mk y (o y.1 y.2) : OrSpace f hF.2)) ∧
    ∀ (φ : Mor) {x x' : Obj} (hx : X.src φ = x) (hx' : X.tgt φ = x')
      (hs : x ∈ X.PObj.smoothSet) (hs' : x' ∈ X.PObj.smoothSet),
      E.orMor hF hsec φ hx hx' hs hs' (o x hs) = o x' hs'

/-- `|σ|` is two-to-one: every point of `|X_∞|` has exactly two preimages. -/
def IsTwoToOneB (E : EpStrongBundle X B) (hF : E.IsScFredholmSectionFunctor f)
    (hsec : B.HasScPlusSectionsThrough) : Prop :=
  ∀ c : Quot X.SmoothRel, ∃ d₁ d₂ : Quot (E.OrRel hF hsec), d₁ ≠ d₂ ∧
    E.orbitProj hF hsec ⁻¹' {c} = {d₁, d₂}

end

/-- **Proposition 12.5.6**: `f` is orientable iff `|σ|` is two-to-one with a global continuous
section. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    [ParacompactSpace (pullbackSpace P X.src)] (E : EpStrongBundle X B)
    [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
    [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
    [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × (Fin n → ℝ) × Obj)]
    [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
      (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]
    (hX : X.IsTame) (hbump : X.PObj.AdmitsBumpFunctions) (f : Obj → W)
    (hF : E.IsScFredholmSectionFunctor f) (hfT : B.IsScFredholmSectionTame f)
    (hsec : B.HasScPlusSectionsThrough),
    letI : TopologicalSpace (OrSpace f hF.2) := topO hX hbump hfT hsec hF.2
    (∃ o : (x : Obj) → (hs : x ∈ X.PObj.smoothSet) → Orx f hF.2 x hs,
        IsOrientationB E hF hsec inferInstance o) ↔
      (IsTwoToOneB E hF hsec ∧
        ∃ g : Quot X.SmoothRel → Quot (E.OrRel hF hsec),
          Continuous g ∧ ∀ c, E.orbitProj hF hsec (g c) = c)

end RoundTrip.V12_26
