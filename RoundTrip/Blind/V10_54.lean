import Polyfold
/-! Blind formalization of V10_54 (the text's Part II, §10.5, the homomorphism `γ`, p. 505 of the
Springer 2021 book; 2017 p. 365).

Text: for `|[d]|(|x|) = |x'|` there are `x''`, `a : φ(x'') → x` and `b : ψ(x'') → x'`, and
`γ(g) = b ∘ ψ(φ⁻¹(a⁻¹ ∘ g ∘ a)) ∘ b⁻¹` is a group homomorphism `G_x → G'_{x'}`; a germ `q` with
`q(g ∗ z) = γ(g) ∗ q(z)` and its lift `Q` (10.25).

Choices:
- Setting: universe 0; a diagram `D : W ←Φ W'' →Ψ W'` of strong bundles over ep-groupoids (the
  project's `SEP.{0}`, `SDiagram`, as in V10_51), covering the diagram `d : X ←φ X'' →ψ X'` of the
  bases (`baseDiagB`, mine, as in V10_52).  `|[d]|` is the project's `Diagram.orbitMap d`
  (`|ψ| ∘ |φ|⁻¹`, 2021 p. 487), `|[D]|` the project's `GenSBMap.orbitMap [D]` (compared in V10_52).
- Groupoid notation: morphisms of `X` with the project's `src`, `tgt`, `comp` (`comp f g = f ∘ g`),
  `inv`; `G_x` the project's `Isotropy x` with its group structure (`g * h = g ∘ h`, checked by
  `rfl`); `φ : G_{x''} → G_{φ(x'')}` the project's `EpFunctor.isotropyHom`.
- (i): the existence of `x''`, `a`, `b`.  (ii), for every such choice: `φ : G_{x''} → G_{φ(x'')}`
  is bijective (so that `φ⁻¹` makes sense), and there is a homomorphism `γ` with
  `γ(g) = b ∘ ψ(k) ∘ b⁻¹` whenever `φ(k) = a⁻¹ ∘ g ∘ a`.
- (iii), for the same choice: "`g ∗ z`", "`γ(g) ∗ q(z)`" are the natural actions of `G_x`, `G'_{x'}`
  near `x`, `x'` (natural representations `R`, `R'`, the project's `NaturalRep`, 2021 Theorem
  7.1.13: `g ∗ z = Φ(g)(z)`); on the bundles the natural lifts `g ∗ w = μ(Γ(g, P(w)), w)` (the
  project's `EpStrongBundle.natLift`).  "A germ `q`": an open `O ∋ x` inside `U(x)` and
  `q : X → X'`, sc-smooth on `O`, `q(x) = x'`, `q(O) ⊆ U(x')`; I read `q` as representing `|[d]|`
  near `x` (`|q(z)| = |[d]|(|z|)` on `O`; without this, the constant germ `q ≡ x'` would do);
  `q(g ∗ z) = γ(g) ∗ q(z)` for `z`, `g ∗ z ∈ O`.  "its lift `Q`" (`IsSBMapOverB`, mine): a strong
  bundle map `W|O → W'` covering `q` (fibrewise linear, sc-smooth on `P⁻¹(O)` for `W[0] → W'[0]`,
  mapping `W_{0,1}` to `W'_{0,1}` and sc-smooth there for `W[1] → W'[1]`; Part I's notion, junk off
  `P⁻¹(O)`), representing `|[D]|` over `O`, and equivariant, `Q(g ∗ w) = γ(g) ∗ Q(w)`.  The
  equivariance of `Q` is my reading of "(10.25)"; I have only the item's summary of the text.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_54
open Polyfold CategoryTheory

/-- The diagram `d : X ←φ X'' →ψ X'` of the base ep-groupoids covered by
`D : W ←Φ W'' →Ψ W'`. -/
def baseDiagB {A A' : SEP.{0}} (D : SBLocalization.SDiagram A A') :
    EPLocalization.Diagram A.baseEP A'.baseEP :=
  ⟨D.B.baseEP, D.Φ.ϕ,
    EpStrongBundle.IsStrongBundleEquivalence.isEquivalence_base D.isEquivalence_Φ, D.Ψ.ϕ⟩

/-- The fibre map `Q : P⁻¹(z) → P'⁻¹(q z)` over `z ∈ O` of a map covering `q` over `O`. -/
def fibreMapB {A A' : SEP.{0}} {O : Set A.Obj} {q : A.Obj → A'.Obj} {Q : A.W → A'.W}
    (hcov : ∀ w, A.P w ∈ O → A'.P (Q w) = q (A.P w)) (z : A.Obj) (hz : z ∈ O) :
    A.P ⁻¹' {z} → A'.P ⁻¹' {q z} :=
  fun e => ⟨Q e.1, by
    have he : A.P e.1 = z := e.2
    have hO : A.P e.1 ∈ O := by rw [he]; exact hz
    change A'.P (Q e.1) = q z
    rw [hcov e.1 hO, he]⟩

/-- `Q : W → W'` is, over the open set `O`, a strong bundle map `W|O → W'` covering `q`. -/
def IsSBMapOverB (A A' : SEP.{0}) (O : Set A.Obj) (q : A.Obj → A'.Obj) (Q : A.W → A'.W) :
    Prop :=
  ∃ hcov : ∀ w, A.P w ∈ O → A'.P (Q w) = q (A.P w),
    (∀ (z : A.Obj) (hz : z ∈ O), IsLinearMap ℝ (fibreMapB hcov z hz)) ∧
    A.B.toMPolyfold0.IsScSmoothOn A'.B.toMPolyfold0 Q (A.P ⁻¹' O) ∧
    (∀ w ∈ A.B.oneSet, A.P w ∈ O → Q w ∈ A'.B.oneSet) ∧
    ∃ Q₁ : A.B.One → A'.B.One,
      (∀ w : A.B.One, A.P (A.B.oneVal w) ∈ O → A'.B.oneVal (Q₁ w) = Q (A.B.oneVal w)) ∧
      A.B.toMPolyfold1.IsScSmoothOn A'.B.toMPolyfold1 Q₁ {w | A.P (A.B.oneVal w) ∈ O}

/-- The homomorphism `γ : G_x → G'_{x'}` of a diagram, and the equivariant germ `q` with its
equivariant lift `Q`. -/
def B : Prop :=
  ∀ (A A' : SEP.{0}) (D : SBLocalization.SDiagram A A') (x : A.Obj) (x' : A'.Obj),
    (baseDiagB D).orbitMap (A.X.π x) = A'.X.π x' →
    -- (i) `x''`, `a : φ(x'') → x`, `b : ψ(x'') → x'`
    (∃ (x'' : D.B.Obj) (a : A.Mor) (b : A'.Mor),
      A.X.src a = D.Φ.ϕ.obj x'' ∧ A.X.tgt a = x ∧
      A'.X.src b = D.Ψ.ϕ.obj x'' ∧ A'.X.tgt b = x') ∧
    ∀ (x'' : D.B.Obj) (a : A.Mor) (b : A'.Mor),
      A.X.src a = D.Φ.ϕ.obj x'' → A.X.tgt a = x →
      A'.X.src b = D.Ψ.ϕ.obj x'' → A'.X.tgt b = x' →
      -- (ii) `φ⁻¹` on `G_{φ(x'')}` and the homomorphism `γ`
      Function.Bijective (D.Φ.ϕ.isotropyHom x'') ∧
      ∃ γ : A.X.Isotropy x →* A'.X.Isotropy x',
        (∀ (g : A.X.Isotropy x) (k : D.B.X.Isotropy x''),
          D.Φ.ϕ.mor k.val = A.X.comp (A.X.inv a) (A.X.comp g.val a) →
          (γ g).val = A'.X.comp b (A'.X.comp (D.Ψ.ϕ.mor k.val) (A'.X.inv b))) ∧
        -- (iii) the germ `q` and its lift `Q`
        ∃ (R : A.X.NaturalRep x) (R' : A'.X.NaturalRep x') (O : Set A.Obj)
          (q : A.Obj → A'.Obj) (Q : A.W → A'.W),
          IsOpen O ∧ x ∈ O ∧ O ⊆ R.U ∧ q x = x' ∧ (∀ z ∈ O, q z ∈ R'.U) ∧
          A.X.PObj.IsScSmoothOn A'.X.PObj q O ∧
          (∀ z ∈ O, (baseDiagB D).orbitMap (A.X.π z) = A'.X.π (q z)) ∧
          (∀ (g : A.X.Isotropy x) (z : A.Obj), z ∈ O → R.Φ g z ∈ O →
            q (R.Φ g z) = R'.Φ (γ g) (q z)) ∧
          IsSBMapOverB A A' O q Q ∧
          (∀ w : A.W, A.P w ∈ O →
            D.cls.orbitMap (A.E.toEpGroupoid.π w) = A'.E.toEpGroupoid.π (Q w)) ∧
          (∀ (g : A.X.Isotropy x) (w : A.W) (hw : A.P w ∈ R.U) (hw' : A'.P (Q w) ∈ R'.U),
            A.P w ∈ O → R.Φ g (A.P w) ∈ O →
            Q (A.E.natLift R g w hw) = A'.E.natLift R' (γ g) (Q w) hw')

end RoundTrip.V10_54
