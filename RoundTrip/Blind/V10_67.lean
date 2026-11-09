import Polyfold
/-! Blind formalization of V10_67 (the Springer 2021 book, Part II, §10.5, Theorem 10.5.7, p. 508;
2017: Theorem 10.10, p. 367), stated literally.

Text: if both strong bundles have the local regularity property and `[D], [D'] : W → W'` are
generalized strong bundle isomorphisms with `|[D]| = |[D']|`, then `[D] = [D']`.  (2017: without
the (LR) hypothesis.)

Choices:
- Setting and notions as in `RoundTrip/Blind/V10_61.lean`: universe 0, strong bundles over
  ep-groupoids `A, A' : SEP.{0}`, generalized strong bundle maps the project's `GenSBMap A A'`
  (classes of diagrams), "generalized strong bundle isomorphism" the project's
  `GenSBMap.IsGeneralizedIso` (2021 Definition 10.5.2: both legs strong bundle equivalences),
  "(LR)" my `IsLRB` (2021 Definition 8.4.2, copied from `RoundTrip/Blind/V8_48.lean`; not the
  project's `EpStrongBundle.IsLR`, see V10_61), for BOTH bundles as the text says.
- `|[D]| : |W| → |W'|`: the project's `GenSBMap.orbitMap` (read with `#print`: `Quot.lift` of the
  orbit map `|Ψ| ∘ |Φ|⁻¹` of the total-space diagram `(W, 𝐖) ← (W'', 𝐖'') → (W', 𝐖')`, 2021
  p. 504, where `|[D]|` is a map of the orbit spaces of the total spaces).  `|[D]| = |[D']|` is
  equality of these functions; `[D] = [D']` equality in `GenSBMap A A'`.
- DOUBT (formalized literally anyway): as I read it the claim fails as in the ep-groupoid case
  (V10_65): over `X = ℤ/3 × ℝ ⇉ ℝ` (trivial action) the trivial bundle `ℝ × ℝᵏ` with `ℤ/3` acting
  trivially on the fibres has (LR) (a strong bundle isomorphism with `|Φ(w)| = |w|` is the
  identity, which is `g ∗ ·` for every `g`), and `[1]`, `[W ←1 W →Inv W]` (`Inv` covering
  `(g, x) ↦ (g⁻¹, x)`) are generalized strong bundle isomorphisms with equal `|·|` but, I expect,
  different classes (no natural transformation `1 ⇒ Inv` in the abelian `ℤ/3`).
-/
namespace RoundTrip.V10_67
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

/-- **Theorem 10.5.7** (literal): between strong bundles with (LR), generalized strong bundle
isomorphisms with the same orbit map are equal. -/
def B : Prop :=
  ∀ (A A' : SEP.{0}), IsLRB A.E → IsLRB A'.E →
    ∀ f f' : GenSBMap A A', f.IsGeneralizedIso → f'.IsGeneralizedIso →
      f.orbitMap = f'.orbitMap → f = f'

end RoundTrip.V10_67
