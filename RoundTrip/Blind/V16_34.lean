import Polyfold
/-! Blind formalization of V16_34 (the text's Part II, §16.2, Theorem 16.2.4, p. 719 of the
Springer 2021 book; 2017: Theorem 16.1).

Text: on `P` there is a natural functor `T`: `(Z, c) ↦ T(Z, c)` and `f̂ ↦ T f̂ = [(Tf, T𝔣)]`,
where `Tf` is given by `|k| = |T𝔣|(|h|)`.

Choices:
- Setting: `Z W V : Type` (universe `0`); polyfolds `c, d, e` (`PolyfoldClass`); sc-smooth maps
  `f̂ : (Z, c) → (W, d)` are the project's `ScMap c d` (Definition 16.1.8: classes of morphisms
  `(f, 𝔣) : (X, α) → (Y, β)` of `PS`, `PSHom`, with `(X, α) ∈ c`, `(Y, β) ∈ d`), the class of a
  representative is `ScMap.mk`.
- On objects `T(Z, c)` is the project's tangent polyfold `c.tangent` on `c.TangentSpace`
  (Definition 16.2.3, item V16_18), and the representative structure `(TX, Tα)` of `(X, α) ∈ c`
  is the project's `PolyfoldClass.tangentStructure q hq` (`#print`ed: `TX = q.X.tangentAny`,
  `β = Tα`).
- On a representative `(f, 𝔣) : (X, α) → (Y, β)`: `T𝔣` is `EPLoc.tangentHom 𝔣` (the tangent of
  a generalized map, 2021 p. 715), and `Tf : T(Z, c) → T(W, d)` is defined by
  `Tf(Tα(|h|)) = Tβ(|T𝔣|(|h|))`, i.e. `Tf = Tβ ∘ |T𝔣| ∘ (Tα)⁻¹`; this is `PSHom.ofGen' (T𝔣)`
  (`#print`ed: `f := β' ∘ |g| ∘ α'⁻¹`).  My `TRep`.
- The claim "there is a functor `T`" is formalized as the conjunction of
  (0) every `(TX, Tα)`, `(X, α) ∈ c`, lies in `Tc` (needed to form `[(Tf, T𝔣)]`);
  (1) well-definedness: two representatives of one `f̂` have tangent representatives of one
      class, so `T f̂ := [(Tf, T𝔣)]` is defined;
  (2) identities: `T` of the identity representative `(Id, 1_X)` is the identity of `T(Z, c)`
      (`ScMap.id`);
  (3) composition, on composable representatives `(f, 𝔣) : (X, α) → (Y, β)`,
      `(g, 𝔤) : (Y, β) → (U, γ)`: `[T(g ∘ f, 𝔤 ∘ 𝔣)] = [T(g, 𝔤) ∘ T(f, 𝔣)]`.
  I state (3) on representatives with a common middle structure (which is how the composition of
  Definition 16.1.10 is formed) rather than through the project's `ScMap.comp` (which needs an
  effective middle polyfold).  The proof terms of (0) are quantified in (1)–(3); (0) makes those
  quantifiers non-vacuous.
- "natural" is not formalized beyond functoriality.  I do not use the project's
  `ScMap.tangent`, `MapRep.tangent` or `PSCat.tangentFunctor`.
- Nothing looks doubtful to me as a claim about classes; note only that (3) presupposes the text's
  composition of sc-smooth maps.
-/
namespace RoundTrip.V16_34
open Polyfold

/-- The structure `(TX, Tα)` on `T(Z, c)`. -/
noncomputable abbrev TS {Z : Type} [TopologicalSpace Z] {c : PolyfoldClass Z}
    (p : PolyfoldStructure Z) (hp : ⟦p⟧ = c) : PolyfoldStructure c.TangentSpace :=
  PolyfoldClass.tangentStructure p hp

/-- The tangent representative `(Tf, T𝔣) : (TX, Tα) → (TY, Tβ)`, `Tf = Tβ ∘ |T𝔣| ∘ (Tα)⁻¹`. -/
noncomputable def TRep {Z W : Type} [TopologicalSpace Z] [TopologicalSpace W]
    {c : PolyfoldClass Z} {d : PolyfoldClass W}
    {p : PolyfoldStructure Z} (hp : ⟦p⟧ = c) {q : PolyfoldStructure W} (hq : ⟦q⟧ = d)
    (φ : PSHom p q) : PSHom (TS p hp) (TS q hq) :=
  PSHom.ofGen' (EPLocalization.EPLoc.tangentHom φ.gen)

/-- Theorem 16.2.4: `T` is a well-defined functor on polyfolds and sc-smooth maps. -/
def B : Prop :=
  -- (0) every `(TX, Tα)` belongs to `Tc`
  (∀ (Z : Type) [TopologicalSpace Z] (c : PolyfoldClass Z) (p : PolyfoldStructure Z)
      (hp : ⟦p⟧ = c), (⟦TS p hp⟧ : PolyfoldClass c.TangentSpace) = c.tangent) ∧
  -- (1) `T f̂ = [(Tf, T𝔣)]` does not depend on the representative of `f̂`
  (∀ (Z W : Type) [TopologicalSpace Z] [TopologicalSpace W]
      (c : PolyfoldClass Z) (d : PolyfoldClass W)
      (p : PolyfoldStructure Z) (hp : ⟦p⟧ = c) (q : PolyfoldStructure W) (hq : ⟦q⟧ = d)
      (φ : PSHom p q)
      (p' : PolyfoldStructure Z) (hp' : ⟦p'⟧ = c) (q' : PolyfoldStructure W) (hq' : ⟦q'⟧ = d)
      (φ' : PSHom p' q'),
      PolyfoldClass.ScMap.mk p hp q hq φ = PolyfoldClass.ScMap.mk p' hp' q' hq' φ' →
      ∀ (htp : ⟦TS p hp⟧ = c.tangent) (htq : ⟦TS q hq⟧ = d.tangent)
        (htp' : ⟦TS p' hp'⟧ = c.tangent) (htq' : ⟦TS q' hq'⟧ = d.tangent),
        PolyfoldClass.ScMap.mk (TS p hp) htp (TS q hq) htq (TRep hp hq φ) =
          PolyfoldClass.ScMap.mk (TS p' hp') htp' (TS q' hq') htq' (TRep hp' hq' φ')) ∧
  -- (2) identities
  (∀ (Z : Type) [TopologicalSpace Z] (c : PolyfoldClass Z) (p : PolyfoldStructure Z)
      (hp : ⟦p⟧ = c) (htp : ⟦TS p hp⟧ = c.tangent),
      PolyfoldClass.ScMap.mk (TS p hp) htp (TS p hp) htp (TRep hp hp (PSHom.id p)) =
        PolyfoldClass.ScMap.id c.tangent) ∧
  -- (3) composition
  (∀ (Z W V : Type) [TopologicalSpace Z] [TopologicalSpace W] [TopologicalSpace V]
      (c : PolyfoldClass Z) (d : PolyfoldClass W) (e : PolyfoldClass V)
      (p : PolyfoldStructure Z) (hp : ⟦p⟧ = c) (q : PolyfoldStructure W) (hq : ⟦q⟧ = d)
      (r : PolyfoldStructure V) (hr : ⟦r⟧ = e) (φ : PSHom p q) (ψ : PSHom q r)
      (htp : ⟦TS p hp⟧ = c.tangent) (htr : ⟦TS r hr⟧ = e.tangent),
      PolyfoldClass.ScMap.mk (TS p hp) htp (TS r hr) htr (TRep hp hr (φ.comp ψ)) =
        PolyfoldClass.ScMap.mk (TS p hp) htp (TS r hr) htr
          ((TRep hp hq φ).comp (TRep hq hr ψ)))

end RoundTrip.V16_34
