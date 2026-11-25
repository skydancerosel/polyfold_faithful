import Polyfold
/-! Blind formalization of V17_142 (the text's Part II, §17.8, Proposition 17.8.16, pp. 839–840
of the Springer 2021 book; 2017: Proposition 17.13).

Text: for a proper polyfold covering functor `P : A → B` and a branched ep⁺-subcategory `Θ` of
`B`, `P^*Θ` is branched; (1) manifold-type, (2) orbifold-type, (3) tameness and (4) compactness
are preserved.

Choices:
- Setting: universe `0`; `A B : GCT.{0}` and a proper polyfold covering functor
  `Pc : ProperPolyfoldCoveringFunctor A B` (Definition 17.8.13; `#print`ed: the functor `Pc.P`,
  the proof that it is a proper covering functor of GCTs (Definition 17.8.1) and a proper polyfold
  covering structure `Pc.S` = a proper covering uniformizer construction `F = Pc.S.toC`, the
  polyfold structure `Pc.S.SB` of `B` on the uniformizers `Ψ` of `F`, and the M-polyfold
  structures on the `M(Ψ̂, Ψ̂')`).  `A` is a polyfold through the uniformizers `Ψ̂ : E → A` of
  the pairs `(Ψ̂, Ψ) ∈ F(β)`.
- `P^*Θ = Θ ∘ P` on objects, written out.
- "branched ep⁺-subcategory" (Definition 17.5.1) of `B`: the project's `F.IsBranchedBase Θ`
  (`#print`ed: `Θ ≥ 0`, constant along morphisms, `Θ ∘ Ψ` a branched ep⁺-subgroupoid of
  `G ⋉ O_β` for every `(Ψ̂, Ψ) ∈ F(β)`; the uniformizers of `Pc.S.SB` are exactly these `Ψ`, so
  this is `Pc.S.SB.IsBranchedSubcategory Θ`).  Of `A`: `F.IsBranchedHat` (`#print`ed: the same
  with `Θ' ∘ Ψ̂` a branched ep⁺-subgroupoid of `E`, the structure of `A` given by the `Ψ̂`).
- (1), (2): `GCT.IsManifoldTypeBranched`, `GCT.IsOrbifoldTypeBranched` (Definition 17.5.4 (1),
  (2), `#print`ed: values in `{0, 1}`, and at most one morphism between objects of the support).
  (4) compact: `GCT.IsCompactBranched` (Definition 17.5.3 (1): `|supp Θ|` compact).
- (3) tame: the text has two notions (Definition 17.5.3 (2), "`Γ^*Θ` tame for a suitable
  covering family", and Definition 17.5.4 (3), "`Θ ∘ Ψ` tame for `α ∈ supp Θ`, `Ψ ∈ F(α)`").
  Since (1), (2) are the other items of Definition 17.5.4, I read (3) with Definition 17.5.4 (3):
  the project's `F.IsTameBase` (`#print`ed: for `Θ(β) > 0` and `(Ψ̂, Ψ) ∈ F(β)`, `Θ ∘ Ψ` tame) and
  `F.IsTameHat` (`#print`ed: for `β` with some `α ∈ P⁻¹(β)` in `supp Θ'` and `(Ψ̂, Ψ) ∈ F(β)`,
  `Θ' ∘ Ψ̂` tame on `E`).
- B is the conjunction of "branched" and (1)–(4), each as an implication.
- Nothing looks doubtful to me.
-/
namespace RoundTrip.V17_142
open Polyfold

/-- Proposition 17.8.16: the pull-back `P^*Θ = Θ ∘ P` of a branched ep⁺-subcategory along a
proper polyfold covering functor is branched, and inherits manifold-type, orbifold-type,
tameness and compactness. -/
def B : Prop :=
  ∀ (A B : GCT.{0}) (Pc : ProperPolyfoldCoveringFunctor A B) (Θ : B.Obj → ℚ),
    Pc.S.toC.IsBranchedBase Θ →
      Pc.S.toC.IsBranchedHat (fun α => Θ (Pc.P.obj α)) ∧
      (B.IsManifoldTypeBranched Θ → A.IsManifoldTypeBranched (fun α => Θ (Pc.P.obj α))) ∧
      (B.IsOrbifoldTypeBranched Θ → A.IsOrbifoldTypeBranched (fun α => Θ (Pc.P.obj α))) ∧
      (Pc.S.toC.IsTameBase Θ → Pc.S.toC.IsTameHat (fun α => Θ (Pc.P.obj α))) ∧
      (B.IsCompactBranched Θ → A.IsCompactBranched (fun α => Θ (Pc.P.obj α)))

end RoundTrip.V17_142
