import Polyfold
/-! Blind formalization of V10_61 (the Springer 2021 book, Part II, §10.5, Proposition 10.5.6,
p. 508; new in the 2021 edition), which the text reduces to Proposition 10.4.6.

Text: if `[D] : (P, μ) → (P', μ')` is a generalized strong bundle isomorphism and one of the
strong bundles has the local regularity property, so has the other.

Choices:
- Setting: universe 0 (all spaces in `Type`), the strong bundles over ep-groupoids are objects
  `A, A'` of the project's bundled `SEP.{0}` (read with `#print`: an ep-groupoid `X`, a total space
  `W` with `P : W → Obj`, linear fibres, Part I's strong bundle `B` and the structure map
  `E : EpStrongBundle X B`, 2021 Definition 8.3.1).
- "generalized strong bundle map `[D]`": the project's `GenSBMap A A'` (read with `#print`: the
  `Quot` of the project's diagrams `W ←Φ W'' →Ψ W'`, `Φ` a strong bundle equivalence, `Ψ` a strong
  bundle functor, by "have a common refinement"; 2021 p. 504).  "generalized strong bundle
  isomorphism": the project's `GenSBMap.IsGeneralizedIso` (read with `#print`: the class of a
  diagram whose `Ψ` is a strong bundle equivalence too, its `Φ` being one by definition of a
  diagram), which is 2021 Definition 10.5.2 verbatim.  Strong bundle equivalences are the
  project's `SEP.equivalences` (2021 Definition 10.4.1), trusted.
- "(LR)" of a strong bundle (2021 Definition 8.4.2): my `IsLRB`, copied from
  `RoundTrip/Blind/V8_48.lean` (inside every open `O ∋ x` a natural representation `U(x) ⊆ O` such
  that every strong bundle isomorphism of `W|U(x)` covering some `β` with `|Φ(w)| = |w|` in the
  orbit space of `(W, 𝐖)` is the natural lift `w ↦ g ∗ w` of some `g ∈ G_x`).  NOT the project's
  `EpStrongBundle.IsLR`, which (read with `#print`) only tests strong bundle maps defined on all
  of `W` (`IsStrongBundleMap`, with `IsStrongBundleIsoOn` over `U(x)`); a strong bundle
  isomorphism of `W|U(x)` need not extend, so that notion may be weaker than the text's.
- "if one has (LR), so has the other": `IsLRB A.E ↔ IsLRB A'.E`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_61
open Polyfold Polyfold.SBLocalization

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

/-- The fibre map `Φ : P⁻¹(x) → P⁻¹(β x)` over `x ∈ U` of a map covering `β` over `U`. -/
def fibreMapB {U : Set Obj} {β : Obj → Obj} {Φ : W → W}
    (hcov : ∀ w, P w ∈ U → P (Φ w) = β (P w)) (x : Obj) (hx : x ∈ U) :
    P ⁻¹' {x} → P ⁻¹' {β x} :=
  fun a => ⟨Φ a.1, by
    have ha : P a.1 = x := a.2
    have hU : P a.1 ∈ U := by rw [ha]; exact hx
    change P (Φ a.1) = β x
    rw [hcov a.1 hU, ha]⟩

open Classical in
/-- The map `W_{0,1} → W_{0,1}` induced by `Φ` over `U` (the identity off `P⁻¹(U)`, a junk
value). -/
noncomputable def oneMapB (B : StrongBundle X.PObj P) {U : Set Obj} {Φ : W → W}
    (hone : ∀ w : B.One, P (B.oneVal w) ∈ U → Φ (B.oneVal w) ∈ B.oneSet) : B.One → B.One :=
  fun w => if h : P (B.oneVal w) ∈ U then B.oneMk (Φ (B.oneVal w)) (hone w h) else w

/-- `Φ` (covering `β`) is a strong bundle isomorphism `W|U → W|U`. -/
def IsSBIsoOnB (B : StrongBundle X.PObj P) (U : Set Obj) (β : Obj → Obj) (Φ : W → W) : Prop :=
  (∃ β' : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj β β' U U) ∧
  ∃ hcov : ∀ w, P w ∈ U → P (Φ w) = β (P w),
    (∀ (x : Obj) (hx : x ∈ U), IsLinearMap ℝ (fibreMapB hcov x hx)) ∧
    (∃ Ψ : W → W, B.toMPolyfold0.IsScDiffeoOn B.toMPolyfold0 Φ Ψ (P ⁻¹' U) (P ⁻¹' U)) ∧
    ∃ hone : ∀ w : B.One, P (B.oneVal w) ∈ U → Φ (B.oneVal w) ∈ B.oneSet,
      ∃ Ψ₁ : B.One → B.One,
        B.toMPolyfold1.IsScDiffeoOn B.toMPolyfold1 (oneMapB B hone) Ψ₁
          {w | P (B.oneVal w) ∈ U} {w | P (B.oneVal w) ∈ U}

/-- `w` and `w'` are isomorphic in `(W, 𝐖)`: `w' = μ(φ, w)` for some `φ` with `s(φ) = P(w)`. -/
def IsoW (E : EpStrongBundle X B) (w w' : W) : Prop :=
  ∃ (φ : Mor) (h : P w = X.src φ), E.μ ⟨(φ, w), h⟩ = w'

/-- The natural lift `g ∗ w = μ(Γ(g, P(w)), w)` of the `G_x`-action to `W|U(x)`. -/
def natLiftB (E : EpStrongBundle X B) {x : Obj} (R : X.NaturalRep x) (g : X.Isotropy x)
    (w : W) (hw : P w ∈ R.U) : W :=
  E.μ ⟨(R.Γ g (P w), w), (R.src_Γ g (P w) hw).symm⟩

/-- **Definition 8.4.2**: the local regularity property of the strong bundle. -/
def IsLRB (E : EpStrongBundle X B) : Prop :=
  ∀ (x : Obj) (O : Set Obj), IsOpen O → x ∈ O →
    ∃ R : X.NaturalRep x, R.U ⊆ O ∧
      ∀ (β : Obj → Obj) (Φ : W → W), IsSBIsoOnB B R.U β Φ →
        (∀ w, P w ∈ R.U → IsoW E w (Φ w)) →
        ∃ g : X.Isotropy x, ∀ (w : W) (hw : P w ∈ R.U), Φ w = natLiftB E R g w hw

end

/-- **Proposition 10.5.6**: a generalized strong bundle isomorphism transports (LR) both ways. -/
def B : Prop :=
  ∀ (A A' : SEP.{0}) (f : GenSBMap A A'), f.IsGeneralizedIso → (IsLRB A.E ↔ IsLRB A'.E)

end RoundTrip.V10_61
