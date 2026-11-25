import Polyfold
/-! Blind formalization of V18_40 (the text's §18.4, the construction on p. 854 and
Proposition 18.4.3, pp. 854–855 of the Springer 2021 book; 2017: Proposition 18.1).

Text: with sc-smooth bump functions, a local sc⁺-section near `q₀` and a bump function give an
sc⁺-multisection functor `Λ`, independent of the choice of `φ`, with `Λ(e) > 0`, atomic in the
model and structurable.

Choices:
- Setting: universe `0`: a GCT `C : GCT.{0}` with a polyfold structure `S`, a vector bundle GCT
  `V` (`P : E → C`) and a strong polyfold bundle construction `Q` over `S` (vocabulary).
  Standing hypothesis: `Q.HasStrongBundleUniformizers` (`F̄(α) ≠ ∅` for every `α`; the text's
  strong bundle uniformizers cover).  "With sc-smooth bump functions" = the vocabulary's
  `S.AdmitsModelBumpFunctions` (Definition 18.4.1).
- The data of the construction: an object `α`, a strong bundle uniformizer `Ψ̄ ∈ F̄(α)`
  (`Ψ̄ : G ⋉ K → E` over `Ψ : G ⋉ O → C`), a point `q₀ ∈ O` with `Ψ(q₀) = α`, and a local
  sc⁺-section `s` of `K → O` on an open `V ∋ q₀` (the vocabulary's
  `StrongBundle.IsScPlusSectionOn`; `s` is taken as a section `O → K` everywhere, only its values
  on `V` matter).  The element is `e = Ψ̄(s(q₀)) ∈ E_α`.
- The bump function: the text says only "a bump function"; I read it as an sc-smooth
  `β : O → [0, 1]` with `β(q₀) = 1` whose support lies in a sufficiently small neighbourhood of
  `q₀`: the statement is "there is an open `W ∋ q₀` such that every such `β` with
  `tsupport β ⊆ W` gives ...".  `βs` is `β·s` (zero off `V`).
- The construction, as I read it: `s_g(q) = g ∗ (βs)(g⁻¹ ∗ q)`; for `e' ∈ E` over `α'` and a
  morphism `φ : Ψ(q) → α'`,
  `Λ_φ(e') = |G|⁻¹ · #{g ∈ G | μ(φ)(Ψ̄(s_g(q))) = e'}`.  Since
  `Ψ̄(g ∗ k) = μ(Ψ(g, p k))(Ψ̄(k))`, this is
  `#{g | μ(φ ∘ Ψ(g, g⁻¹ q))(Ψ(g⁻¹ q), β(g⁻¹ q)·s(g⁻¹ q)) = e'} / |G|` (`phiValue`).  If no
  `φ : Ψ(q) → α'` exists, `Λ(e') = 1` for `e' = 0` and `0` otherwise.  `Λ` uses some choice of
  `(q, φ)`; "independent of the choice of `φ`" is the first conjunct (all `(q, φ)` give the same
  value).
- "atomic in the model": for EVERY bundle covering family `c`, the pull-back `Γ̄^*Λ = Λ ∘ Γ̄` to
  the model of `c ⊔ {Ψ̄}` (the vocabulary's `c.withUnif Ψ̄`, `bundlePull`, `modelSEP`) is atomic
  (Definition 13.5.1, the vocabulary's `SBLocalization.IsAtomic`).  The text does not say which
  model; I take the models containing `Ψ̄` (in a model not containing it the support need not lie
  in one `U(x)`).
- "sc⁺-multisection functor" = `Q.IsScPlusMultisectionFunctor` (Definition 18.3.1);
  "structurable" = `Q.IsStructurableFunctor` (Definition 18.3.3).
- The "easy proof left to the reader" is not part of the claim.  Nothing looks doubtful to me.
-/
namespace RoundTrip.V18_40
open Polyfold

variable {C : GCT.{0}} {V : C.VectorBundle}

/-- `Ψ̄(β(r)·s(r)) ∈ E` over `Ψ(r)`, as an object of `E`. -/
noncomputable def cutSec (Ψb : V.StrongBundleUniformizer) (s : Ψb.base.O → Ψb.K)
    (hs : ∀ q, Ψb.p (s q) = q) (β : Ψb.base.O → ℝ) (r : Ψb.base.O) : V.EObj :=
  V.objMk (Ψb.base.obj r) (β r • Ψb.fiber r ⟨s r, hs r⟩)

/-- `Λ_φ(e')` for `φ : Ψ(q) → α'`: `|G|⁻¹ · #{g | μ(φ ∘ Ψ(g, g⁻¹ q))(Ψ̄((βs)(g⁻¹ q))) = e'}`. -/
noncomputable def phiValue (Ψb : V.StrongBundleUniformizer) (s : Ψb.base.O → Ψb.K)
    (hs : ∀ q, Ψb.p (s q) = q) (β : Ψb.base.O → ℝ) (q : Ψb.base.O) (φ : C.Mor)
    (e' : V.EObj) : ℚ≥0 :=
  (Nat.card {g : Ψb.base.G //
      ∃ hh, V.act (C.toGroupoidStr.comp φ (Ψb.base.mor (g, g⁻¹ • q)))
        (cutSec Ψb s hs β (g⁻¹ • q)) hh = e'} : ℚ≥0) / (Nat.card Ψb.base.G : ℚ≥0)

/-- `φ : Ψ(q) → base(e')`. -/
def IsLift (Ψb : V.StrongBundleUniformizer) (e' : V.EObj) (p : Ψb.base.O × C.Mor) : Prop :=
  C.toGroupoidStr.src p.2 = Ψb.base.obj p.1 ∧ C.toGroupoidStr.tgt p.2 = e'.1

open Classical in
/-- The functor `Λ` of the construction on p. 854. -/
noncomputable def lam (Ψb : V.StrongBundleUniformizer) (s : Ψb.base.O → Ψb.K)
    (hs : ∀ q, Ψb.p (s q) = q) (β : Ψb.base.O → ℝ) (e' : V.EObj) : ℚ≥0 :=
  if h : ∃ p, IsLift Ψb e' p then phiValue Ψb s hs β h.choose.1 h.choose.2 e'
  else if e'.2 = 0 then 1 else 0

/-- Construction on p. 854 and Proposition 18.4.3. -/
def B : Prop :=
  ∀ (C : GCT.{0}) (S : C.PolyfoldConstruction) (V : C.VectorBundle)
    (Q : V.StrongPolyfoldBundleConstruction S),
    Q.HasStrongBundleUniformizers → S.AdmitsModelBumpFunctions →
    ∀ (α : C.Obj) (Ψb : V.StrongBundleUniformizer) (hΨb : Ψb ∈ Q.F α) (q₀ : Ψb.base.O),
      Ψb.base.obj q₀ = α →
    ∀ (s : Ψb.base.O → Ψb.K) (hs : ∀ q, Ψb.p (s q) = q) (Vs : Set Ψb.base.O),
      IsOpen Vs → q₀ ∈ Vs → Ψb.B.IsScPlusSectionOn s Vs →
    ∃ W : Set Ψb.base.O, IsOpen W ∧ q₀ ∈ W ∧
      ∀ β : Ψb.base.O → ℝ, Ψb.base.P.IsScSmoothMap realPolyfold β →
        (∀ r, 0 ≤ β r ∧ β r ≤ 1) → tsupport β ⊆ W → β q₀ = 1 →
        -- independent of the choice of `φ`
        (∀ (e' : V.EObj) (p p' : Ψb.base.O × C.Mor), IsLift Ψb e' p → IsLift Ψb e' p' →
          phiValue Ψb s hs β p.1 p.2 e' = phiValue Ψb s hs β p'.1 p'.2 e') ∧
        -- an sc⁺-multisection functor
        Q.IsScPlusMultisectionFunctor (lam Ψb s hs β) ∧
        -- `Λ(e) > 0`
        0 < lam Ψb s hs β (V.objMk (Ψb.base.obj q₀) (Ψb.fiber q₀ ⟨s q₀, hs q₀⟩)) ∧
        -- atomic in the model
        (∀ c : Q.BundleCoveringFamily,
          SBLocalization.IsAtomic (Q.modelSEP (c.withUnif ⟨Ψb, α, hΨb⟩).Ψ)
            (Q.bundlePull (c.withUnif ⟨Ψb, α, hΨb⟩).Ψ (lam Ψb s hs β))) ∧
        -- structurable
        Q.IsStructurableFunctor (lam Ψb s hs β)

end RoundTrip.V18_40
