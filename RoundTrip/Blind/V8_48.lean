import Polyfold
/-! Blind formalization of V8_48 (the 2021 book, Part II, §8.4, Definition 8.4.2 and
Proposition 8.4.3, p. 382).

Text: with the natural lift of the `G_x`-action to `W|U(x)`, the strong bundle `P : W → X` has
the local regularity property if every `x` has arbitrarily small `U(x)` such that every strong
bundle isomorphism `B : W|U(x) → W|U(x)` with `|B(w)| = |w|` is of the form `w ↦ g ∗ w` for
some `g ∈ G_x`.  Proposition 8.4.3: for effective `X` with (LR) the strong bundle has it.

Choices:
- B is the conjunction of (i) the definition (the project's `EpStrongBundle.IsLR` is the text's
  notion `IsLRB` below) and (ii) Proposition 8.4.3 stated with `IsLRB`.
- Setting: `Obj Mor : Type` (universe 0) with the instances of the project's `EpGroupoid`,
  `X : EpGroupoid Obj Mor`; `W : Type` with its topology, `P : W → Obj` with the linear
  structures on the fibres, `B : StrongBundle X.PObj P` (Part I) and `E : EpStrongBundle X B`
  (the structure map `μ`, 2017 Definition 8.4, read with `#print`).
- `U(x)` with the `G_x`-action: a natural representation `R : X.NaturalRep x` (the data of
  2017 Theorem 7.1 / 2021 Theorem 7.1.13: open connected `U ∋ x`, `Φ : G_x → Diff_sc(U)`,
  `Γ : G_x × U → 𝐗`).  "arbitrarily small": inside every open `O ∋ x` there is such an `R` with
  `R.U ⊆ O`.
- The natural lift: `g ∗ w = μ(Γ(g, P(w)), w)` for `P(w) ∈ U(x)` (my `natLiftB`; `Γ(g, P w)` is
  a morphism `P w → Φ(g)(P w)`).
- `|B(w)| = |w|`: `B(w)` and `w` are isomorphic in the groupoid `(W, 𝐖)`, i.e. `B(w) = μ(φ, w)`
  for some morphism `φ` with `s(φ) = P(w)` (my `IsoW`).
- "strong bundle isomorphism `W|U → W|U`" (my `IsSBIsoOnB`): written by me because the project's
  local notion `IsStrongBundleIsoOn` needs a strong bundle map defined on all of `W`, and a
  strong bundle isomorphism of `W|U` need not extend to `W`.  `Φ : W → W` (only its values over
  `U` matter) covers some `β : Obj → Obj` with `β : U → U` an sc-diffeomorphism; `P(Φ w) =
  β(P w)` over `U`; `Φ` is linear on every fibre over `U`; `Φ : P⁻¹(U) → P⁻¹(U)` is an
  sc-diffeomorphism of `W[0]`; `Φ` maps `W_{0,1} ∩ P⁻¹(U)` into `W_{0,1}` and the induced map
  (my `oneMapB`, junk off `P⁻¹(U)`) is an sc-diffeomorphism of `(P⁻¹(U))_{0,1}` in `W[1]`.
  (The inverse is then a strong bundle map as well.)  `IsScDiffeoOn` is the project's
  (sc-smooth both ways, mutually inverse, read with `#print`).
- "is of the form `w ↦ g ∗ w`": some `g ∈ G_x` with `Φ w = g ∗ w` for all `w` over `U(x)`.
- Proposition 8.4.3: "effective" is the project's `EpGroupoid.IsEffective` (2017 Definition
  7.11, read with `#print`), "(LR)" of `X` the project's `EpGroupoid.IsLR` (2021 Definition
  7.4.19, read with `#print`: inside every open `O ∋ x` a natural representation `U(x)` such
  that every sc-diffeomorphism `β : U(x) → U(x)` with `|β(y)| = |y|` is some `Φ(g)`).
- Nothing looks false to me.
-/
namespace RoundTrip.V8_48
open Polyfold

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

/-- Definition 8.4.2 (the project's (LR) for strong bundles is the text's) and Proposition 8.4.3
(effective `X` with (LR): the strong bundle has (LR)). -/
def B : Prop :=
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    (E : EpStrongBundle X B),
    E.IsLR ↔ IsLRB E) ∧
  (∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    (E : EpStrongBundle X B),
    X.IsEffective → X.IsLR → IsLRB E)

end RoundTrip.V8_48
