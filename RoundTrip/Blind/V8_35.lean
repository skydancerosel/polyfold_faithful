import Polyfold
/-! Blind formalization of V8_35 (the 2017 book, arXiv 1707.08941, Part II, §8.4, Proposition 8.3
(Geometric Lift) and its proof, pp. 281–282; 2021: Proposition 8.5.7, pp. 389–391).

Text: associated with a covering functor `f : D → C` and a geometric lift `τ : L_D → L_C ∘ f` there
is a natural construction of a proper covering functor `F : Y → X` between two ep-groupoids.
Construction: `X = G_x ⋉ U(x)`, `s(g, z) = z`, `t(g, z) = g ∗ z`; `Y = ⋃_{y ∈ D} U(y)`,
`𝐘 = ⋃_{(y, y') ∈ D × D} [mor(y, y') × U(y)]`, `s(ψ, z) = z`, `t(ψ, z) = φ_{yy'}(ψ)(z)`,
`(ψ, z') ∘ (γ, z) = (ψ ∘ γ, z)`, units `(1_y, z)`, inverses `(ψ⁻¹, φ_{yy'}(ψ)(z))`, and "one
verifies" that `Y` is an ep-groupoid; `F|U(y) := τ(y)`, `F(ψ, z) = (f(ψ), τ(y)(z))`.  The map (8.16)
`𝐘 → 𝐗 ₛ×_F Y`, `(ψ, z) ↦ ((f(ψ), F(z)), z)`, is a bijection, by the definition of a covering
functor, and a local sc-diffeomorphism, hence an sc-diffeomorphism.

Choices:
- Setting as in my `RoundTrip/Blind/V8_33.lean`: `D` a finite Mathlib groupoid, `C = SingleObj G`
  (`G = G_x` finite, `g ∘ h = g * h`), `f` a covering functor (the project's `IsCoveringFunctor`,
  = the text's definition, see V8_32), `L` the project's `GeometricLift f` into `MPolyfoldCat`
  (universe 0).  `U(x) = (L_C star).carrier`, `U(y) = (L_D y).carrier`,
  `g ∗ z = L_C(g)(z)` (`actB`), `φ_{yy'}(ψ) = L_D(ψ)`, `τ(y) = (L.τ.app y).toFun`.
- The sets: `X`'s objects `U(x)`, morphisms `G × U(x)`; `Y`'s objects `Σ y, U(y)` (the disjoint
  union), morphisms `Σ (ψ : Σ a b, a ⟶ b), U(a)` (the disjoint union of the `mor(y, y') × U(y)`).
  Topologies: Mathlib's sigma and product topologies, `G` discrete.  Paracompactness of these
  spaces (required by the project's `EpGroupoid`) is asserted (existentially), not assumed.
- "Ep-groupoids": project `EpGroupoid` structures `EX`, `EY` on these sets whose structure maps are
  the text's (`IsModelB`): for `EX` `s`, `t`, composition on composable pairs, units `(1, z)`,
  inverses `(g⁻¹, g ∗ z)` (the translation groupoid of Chapter 7); for `EY` `s`, `t`, composition of
  every composable pair `((ψ, φ(γ)(z)), (γ, z))` (every composable pair has this form), units and
  inverses as in the text.
- M-polyfold structures (the text: `X = G_x ⋉ U(x)` with Chapter 7's structure, `G × U(x)` as
  `#G` copies of `U(x)`; `Y`, `𝐘` "a disjoint union of M-polyfolds possesses a natural M-polyfold
  structure", not described, V8.34): characterized by the summands: the identity
  `U(x) → X` and each `z ↦ (g, z)`, `z ↦ ⟨y, z⟩`, `z ↦ ⟨ψ, z⟩` is an sc-diffeomorphism
  (`IsScDiffeoOn`) from the M-polyfold `U(·)` onto the corresponding (open) summand.  This pins the
  structures down up to the identity being an sc-diffeomorphism, which is all sc-notions see.
- `F` (`A` in the Lean code): a project `EpFunctor EY EX` with `A⟨y, z⟩ = τ(y)(z)` and
  `A⟨ψ, z⟩ = (f(ψ), τ(s ψ)(z))`; B asserts it is a proper covering functor (the project's
  `IsProperCovering`, = Definition 8.5.1, `#print`ed) and that (8.16) (the project's
  `EpFunctor.fibredMap`, `φ ↦ (F φ, s φ)`, which is the text's map) is a bijection; that (8.16) is
  an sc-diffeomorphism is part of `IsProperCovering`.  "Natural" is not formalized.
- FALSE IN A DEGENERATE CASE (formalized literally anyway): the text allows `D` with no objects
  (Definition 8.5.5 asks only finitely many objects).  For `D = ∅` and `U(x) ≠ ∅` (e.g. `L_C` any
  functor with a nonempty M-polyfold, `L_D` and `τ` empty), `f` is a covering functor but `Y = ∅`,
  so `F : ∅ → U(x)` is not surjective and not a proper covering functor.  B is false for that
  reason; with `D` nonempty (as when `D = F⁻¹(x)`, Theorem 8.5.8) I see nothing wrong.
-/
namespace RoundTrip.V8_35
open Polyfold CategoryTheory

section
variable {D : Type} [Groupoid D] {G : Type} [Group G] {f : D ⥤ SingleObj G}

/-- `U(x) = L_C(x)`. -/
abbrev UxB (L : GeometricLift.{0} f) : Type := (L.LC.obj (SingleObj.star G)).carrier

/-- The objects `Y = ⨆_{y ∈ D} U(y)`. -/
abbrev ObjYB (L : GeometricLift.{0} f) : Type := Σ y : D, (L.LD.obj y).carrier

/-- The morphisms `𝐘 = ⨆_{(y, y')} mor(y, y') × U(y)`. -/
abbrev MorYB (L : GeometricLift.{0} f) : Type :=
  Σ ψ : (Σ (a : D) (b : D), (a ⟶ b)), (L.LD.obj ψ.1).carrier

/-- The action `g ∗ z = L_C(g)(z)` of `G_x` on `U(x)`. -/
def actB (L : GeometricLift.{0} f) (g : G) (z : UxB L) : UxB L :=
  (L.LC.map (show SingleObj.star G ⟶ SingleObj.star G from g)).toFun z

/-- The construction of Proposition 8.5.7: `EX = G_x ⋉ U(x)`, `EY` the groupoid on `⨆ U(y)` and
`⨆ mor(y, y') × U(y)`, both with the disjoint-union M-polyfold structures, and the functor
`A = F : EY → EX`, `A⟨y, z⟩ = τ(y)(z)`, `A⟨ψ, z⟩ = (f(ψ), τ(y)(z))`. -/
def IsModelB (L : GeometricLift.{0} f) [TopologicalSpace G] [DiscreteTopology G]
    [ParacompactSpace (ObjYB L)]
    [ParacompactSpace (MorYB L)] [ParacompactSpace (G × UxB L)]
    (EY : EpGroupoid (ObjYB L) (MorYB L)) (EX : EpGroupoid (UxB L) (G × UxB L))
    (A : EpFunctor EY EX) : Prop :=
  -- `X = G_x ⋉ U(x)`
  (∀ p : G × UxB L, EX.src p = p.2) ∧
  (∀ p : G × UxB L, EX.tgt p = actB L p.1 p.2) ∧
  (∀ p q : G × UxB L, EX.src p = EX.tgt q → EX.comp p q = (p.1 * q.1, q.2)) ∧
  (∀ z : UxB L, EX.unit z = (1, z)) ∧
  (∀ p : G × UxB L, EX.inv p = (p.1⁻¹, actB L p.1 p.2)) ∧
  -- the M-polyfold structures of `X`: `U(x)` itself, and `#G` copies `{g} × U(x)` of it
  (∃ h : UxB L → UxB L,
    (L.LC.obj (SingleObj.star G)).P.IsScDiffeoOn EX.PObj id h Set.univ Set.univ) ∧
  (∀ g : G, ∃ h : G × UxB L → UxB L,
    (L.LC.obj (SingleObj.star G)).P.IsScDiffeoOn EX.PMor (fun z => (g, z)) h Set.univ
      {p | p.1 = g}) ∧
  -- the groupoid `Y`
  (∀ (ψ : Σ (a : D) (b : D), (a ⟶ b)) (z : (L.LD.obj ψ.1).carrier),
    EY.src ⟨ψ, z⟩ = ⟨ψ.1, z⟩) ∧
  (∀ (a b : D) (ψ : a ⟶ b) (z : (L.LD.obj a).carrier),
    EY.tgt ⟨⟨a, b, ψ⟩, z⟩ = ⟨b, (L.LD.map ψ).toFun z⟩) ∧
  (∀ (a b c : D) (γ : a ⟶ b) (ψ : b ⟶ c) (z : (L.LD.obj a).carrier),
    EY.comp ⟨⟨b, c, ψ⟩, (L.LD.map γ).toFun z⟩ ⟨⟨a, b, γ⟩, z⟩ = ⟨⟨a, c, γ ≫ ψ⟩, z⟩) ∧
  (∀ (y : D) (z : (L.LD.obj y).carrier), EY.unit ⟨y, z⟩ = ⟨⟨y, y, 𝟙 y⟩, z⟩) ∧
  (∀ (a b : D) (ψ : a ⟶ b) (z : (L.LD.obj a).carrier),
    EY.inv ⟨⟨a, b, ψ⟩, z⟩ = ⟨⟨b, a, Groupoid.inv ψ⟩, (L.LD.map ψ).toFun z⟩) ∧
  -- the M-polyfold structures of `Y`, `𝐘`: the summands `U(y)` are open sc-diffeomorphic copies
  (∀ y : D, ∃ h : ObjYB L → (L.LD.obj y).carrier,
    (L.LD.obj y).P.IsScDiffeoOn EY.PObj (fun z => (⟨y, z⟩ : ObjYB L)) h Set.univ
      (Set.range (fun z => (⟨y, z⟩ : ObjYB L)))) ∧
  (∀ ψ : Σ (a : D) (b : D), (a ⟶ b), ∃ h : MorYB L → (L.LD.obj ψ.1).carrier,
    (L.LD.obj ψ.1).P.IsScDiffeoOn EY.PMor (fun z => (⟨ψ, z⟩ : MorYB L)) h Set.univ
      (Set.range (fun z => (⟨ψ, z⟩ : MorYB L)))) ∧
  -- the functor `F`
  (∀ (y : D) (z : (L.LD.obj y).carrier), A.obj ⟨y, z⟩ = (L.τ.app y).toFun z) ∧
  (∀ (a b : D) (ψ : a ⟶ b) (z : (L.LD.obj a).carrier),
    A.mor ⟨⟨a, b, ψ⟩, z⟩ = ((f.map ψ : G), (L.τ.app a).toFun z))

end

/-- Proposition 8.5.7: for a covering functor `f` with a geometric lift `L`, the construction
`Y = ⨆ U(y)`, `X = G_x ⋉ U(x)`, `F = τ` gives ep-groupoids and a proper covering functor
`F : Y → X`, with (8.16) a bijection. -/
def B : Prop :=
  ∀ (D : Type) [Groupoid D] [Fintype D] [∀ a b : D, Fintype (a ⟶ b)]
    (G : Type) [Group G] [Fintype G] (f : D ⥤ SingleObj G),
    IsCoveringFunctor f → ∀ L : GeometricLift.{0} f,
      letI : TopologicalSpace G := ⊥
      haveI : DiscreteTopology G := ⟨rfl⟩
      ∃ (_ : ParacompactSpace (ObjYB L)) (_ : ParacompactSpace (MorYB L))
        (_ : ParacompactSpace (G × UxB L))
        (EY : EpGroupoid (ObjYB L) (MorYB L)) (EX : EpGroupoid (UxB L) (G × UxB L))
        (A : EpFunctor EY EX),
        IsModelB L EY EX A ∧ A.IsProperCovering ∧ Function.Bijective A.fibredMap

end RoundTrip.V8_35
