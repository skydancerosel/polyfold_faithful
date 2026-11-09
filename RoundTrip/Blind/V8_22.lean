import Polyfold
/-! Blind formalization of V8_22 (the text's Part II, §8.3, after Definition 8.3.1 = 2017
Definition 8.4, pp. 375–377 / 2017 pp. 271–272).

Text: with `𝐖 = 𝐗 ₛ×_P W` one defines the ep-groupoid `𝒲 = (W, 𝐖)`: `s_𝐖(ψ, w) = w`,
`t_𝐖(ψ, w) = μ(ψ, w)` (fibrewise linear local sc-diffeomorphisms covering `s_X`, `t_X`), units
`(1_x, w)` for `w ∈ W_x`, inverses `(ψ⁻¹, μ(ψ, w))`, and `(ψ, w') ∘ (γ, w) = (ψ ∘ γ, w)` for
`w' = μ(γ, w)`.  `P : W → X` and `𝐏 = π₁ : 𝐖 → 𝐗` form an sc-smooth functor
`(P, 𝐏) : (W, 𝐖) → (X, 𝐗)`; since the orbit of `w` covers the orbit of `P(w)`, `P` induces a
surjective continuous `|P| : |W| → |X|`.

Choices:
- Setting as in my `RoundTrip/Blind/V8_20.lean`: `X : EpGroupoid Obj Mor`, `W : Type`,
  `B : StrongBundle X.PObj P`, `E : EpStrongBundle X B` (V8_20: the text's strong bundle over `X`),
  `μ = E.μ`; `𝐖 = pullbackSpace P X.src` with the M-polyfold structure of the pull-back strong
  bundle `(B.pullback hs)[0]`, `W` with `B[0]` (the text's M-polyfolds `𝐖`, `W`).  Hypotheses
  (true, satisfiable, as in V8_20): paracompactness of `𝐖` and the sc-smoothness `hs` of `s`.
- "one defines the ep-groupoid `(W, 𝐖)`": the project's `E.toEpGroupoid` (needs the paracompact
  instance); B (a) says it is an ep-groupoid (by its type) with the M-polyfolds `W[0]`, `𝐖[0]` and
  exactly the text's structure maps (the composition only on composable pairs, i.e.
  `s_𝐖(ψ, w') = t_𝐖(γ, w)`, i.e. `w' = μ(γ, w)`; off them the project's total `comp` is junk).
  Points of `𝐖` are compared through their underlying pairs.
- "fibrewise linear local sc-diffeomorphisms covering `s_X`, `t_X`" (b): `P ∘ s_𝐖 = s_X ∘ π₁`,
  `P ∘ t_𝐖 = t_X ∘ π₁`; local sc-diffeomorphisms `𝐖[0] → W[0]`; linear on the fibres of
  `𝐖 → 𝐗` (the project's fibre linear structure of the pull-back, through `fiberRestrict`).
- (c) the functor: ∃ an `EpFunctor` `(W, 𝐖) → (X, 𝐗)` with object map `P` and morphism map
  `(ψ, w) ↦ ψ`.
- (d) "the orbit of `w` covers the orbit of `P(w)`": `P` maps the orbit `{w' | ∃ φ : w → w'}` onto
  the orbit of `P w`; (e) there is `|P| : |W| → |X|` with `|P|(|w|) = |P(w)|`, surjective and
  continuous for the quotient topologies (written out as `coinduced π`).
- Nothing looks false to me.
-/
namespace RoundTrip.V8_22
open Polyfold

/-- The orbit `{y | ∃ φ : x → y}` of `x` in the groupoid `G`. -/
def orbitB {Obj Mor : Type} (G : GroupoidStr Obj Mor) (x : Obj) : Set Obj :=
  {y | ∃ φ : Mor, G.src φ = x ∧ G.tgt φ = y}

/-- The functorial picture of a strong bundle over an ep-groupoid. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → Obj)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] (B : StrongBundle X.PObj P)
    [ParacompactSpace (pullbackSpace P X.src)] (hs : X.PMor.IsScSmoothMap X.PObj X.src)
    (E : EpStrongBundle X B),
    -- (a) `(W, 𝐖)` is an ep-groupoid with the M-polyfolds `W`, `𝐖` and the text's structure maps
    (E.toEpGroupoid.PObj = B.toMPolyfold0 ∧
      E.toEpGroupoid.PMor = (B.pullback hs).toMPolyfold0 ∧
      (∀ p : pullbackSpace P X.src, E.toEpGroupoid.src p = p.1.2) ∧
      (∀ p : pullbackSpace P X.src, E.toEpGroupoid.tgt p = E.μ p) ∧
      (∀ w : W, (E.toEpGroupoid.unit w).1 = (X.unit (P w), w)) ∧
      (∀ p : pullbackSpace P X.src, (E.toEpGroupoid.inv p).1 = (X.inv p.1.1, E.μ p)) ∧
      (∀ p q : pullbackSpace P X.src, p.1.2 = E.μ q →
        (E.toEpGroupoid.comp p q).1 = (X.comp p.1.1 q.1.1, q.1.2))) ∧
    -- (b) `s_𝐖`, `t_𝐖` are fibrewise linear local sc-diffeomorphisms covering `s_X`, `t_X`
    (∃ (hcs : ∀ p : pullbackSpace P X.src, P p.1.2 = X.src (pullbackProj P X.src p))
        (hct : ∀ p : pullbackSpace P X.src, P (E.μ p) = X.tgt (pullbackProj P X.src p)),
      (B.pullback hs).toMPolyfold0.IsLocalScDiffeo B.toMPolyfold0 (fun p => p.1.2) ∧
      (B.pullback hs).toMPolyfold0.IsLocalScDiffeo B.toMPolyfold0 E.μ ∧
      (∀ ψ : Mor, IsLinearMap ℝ
        (fiberRestrict (pullbackProj P X.src) P X.src (fun p => p.1.2) hcs ψ)) ∧
      (∀ ψ : Mor, IsLinearMap ℝ (fiberRestrict (pullbackProj P X.src) P X.tgt E.μ hct ψ))) ∧
    -- (c) `(P, 𝐏) : (W, 𝐖) → (X, 𝐗)` is an sc-smooth functor
    (∃ F : EpFunctor E.toEpGroupoid X, F.obj = P ∧ F.mor = fun p => p.1.1) ∧
    -- (d) the orbit of `w` covers the orbit of `P(w)`
    (∀ w : W, P '' orbitB E.toEpGroupoid.toGroupoidStr w = orbitB X.toGroupoidStr (P w)) ∧
    -- (e) `|P| : |W| → |X|` is surjective and continuous
    (∃ f : E.toEpGroupoid.OrbitSpace → X.OrbitSpace,
      (∀ w : W, f (E.toEpGroupoid.π w) = X.π (P w)) ∧ Function.Surjective f ∧
      @Continuous _ _ (TopologicalSpace.coinduced E.toEpGroupoid.π inferInstance)
        (TopologicalSpace.coinduced X.π inferInstance) f)

end RoundTrip.V8_22
