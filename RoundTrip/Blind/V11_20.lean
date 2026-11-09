import Polyfold
/-! Blind formalization of V11_20 (the Springer 2021 book, Part II, §11.3, Lemma 11.3.4 with
(11.8), (11.9), pp. 538–539).

Text: for an equivalence `F`, `(F_*h)(y) = Tψ ∘ TF(x) h(x)` for `ψ : F(x) → y` (11.8) and
`TF(x)(F^*h')(x) = h'(F(x))` (11.9); for a generalized isomorphism `f = [X ←F A →G Y]`,
`f_* = G_*F^*` and `f^* = F_*G^*` are well-defined maps between the sets `Γ(π̂)` of section
functors, with `(f⁻¹)_* = f^*`, `(g ∘ f)_* = g_* ∘ f_*`, `(g ∘ f)^* = f^* ∘ g^*`.

Choices:
- Setting: for (11.8), (11.9) ep-groupoids `X : EpGroupoid Obj Mor`, `Y : EpGroupoid Obj' Mor'`
  with all four spaces in `Type` (as in `V10_13.lean`) and an equivalence `F`
  (`EpFunctor.IsEquivalence`, Definition 10.1.1, `#print`ed).  For the generalized maps: objects
  `X Y Z : EP.{0}`, morphisms of the project's `EP(E⁻¹)`, "generalized isomorphism" the project's
  `EPLoc.IsGeneralizedIso` (`#print`ed: two-sided inverse in `EP(E⁻¹)`), representatives the
  project's `Diagram` (`d.F` the equivalence `F : A → X`, `d.Φ` the functor `G : A → Y`), `[d]`
  is `EPLoc.homMk d`.  `g ∘ f` is Mathlib's `f ≫ g`; `f⁻¹` is any `g` with `f ≫ g = 𝟙`,
  `g ≫ f = 𝟙`.
- `Γ(π̂_X)`, the section functors of `π̂ : Gr̂(X) → X`: the project's `GrHatSections`
  (`#print`ed: `h(x) ∈ Gr̂(x)` and natural along morphisms, for `x ∈ X_∞`; junk `0` off `X_∞`,
  where `Gr̂` is not defined).  `Gr̂(x)`: nonnegative finite formal sums of oriented subspaces of
  `T_xX` (`GrHat`, `#print`ed).
- `TF(x)`, `Tψ`, "`Tψ ∘ TF(x) h(x)`": `F.tangent.obj` (Part I's tangent map of `F` on objects),
  `Y.tangentMor ψ` (Definition 7.1.4), and a formal sum is moved summand by summand with
  `OrTangent.map` (image of the subspace and of its oriented frames) through
  `Finsupp.mapDomain`; all `#print`ed.
- `F_*h`, `F^*h'`: the project's `EpFunctor.pushSection`, `pullSection` (`#print`ed; the former
  uses a chosen `(x, ψ)`).  (11.8) is formalized as: for every `y ∈ Y_∞` and EVERY `x`,
  `ψ : F(x) → y`, `(F_*h)(y)` is the displayed value (definition plus independence of the
  choice).  (11.9) is formalized literally, for `x ∈ X_∞`.  Both maps send `Γ` to `Γ`.
- `f_* = G_*F^*`, `f^* = F_*G^*` on a representative: the project's `Diagram.pushSection`,
  `Diagram.pullSection` (`#print`ed: exactly `d.Φ.pushSection (d.F.pullSection h)` and
  `d.F.pushSection (d.Φ.pullSection h')`).  "Well-defined maps `Γ → Γ`": for every representative
  the value lies in `Γ`, and two representatives give the same value.  The three identities are
  asserted for every choice of representatives and for sections in `Γ` (equalities of functions;
  all maps are `0` off the smooth points by construction).
- Nothing looks false to me.
-/
namespace RoundTrip.V11_20
open Polyfold Polyfold.EPLocalization CategoryTheory

/-- (11.8), (11.9) and `F_*, F^* : Γ → Γ` for an equivalence `F`. -/
def EquivPartB : Prop :=
  ∀ (Obj Mor Obj' Mor' : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
    (X : EpGroupoid Obj Mor) (Y : EpGroupoid Obj' Mor') (F : EpFunctor X Y),
    F.IsEquivalence →
      -- (11.8), for every choice of `x` and `ψ : F(x) → y`
      (∀ h ∈ X.GrHatSections, ∀ (y : Obj'), y ∈ Y.PObj.smoothSet →
        ∀ (x : Obj) (ψ : Mor'), Y.src ψ = F.obj x → Y.tgt ψ = y →
          F.pushSection h y =
            Finsupp.mapDomain (MPolyfold.OrTangent.map (Y.tangentMor ψ ∘ F.tangent.obj)) (h x)) ∧
      -- (11.9)
      (∀ h' ∈ Y.GrHatSections, ∀ x : Obj, x ∈ X.PObj.smoothSet →
        Finsupp.mapDomain (MPolyfold.OrTangent.map F.tangent.obj) (F.pullSection h' x) =
          h' (F.obj x)) ∧
      -- `F_*`, `F^*` are maps `Γ(π̂_X) → Γ(π̂_Y)`, `Γ(π̂_Y) → Γ(π̂_X)`
      (∀ h ∈ X.GrHatSections, F.pushSection h ∈ Y.GrHatSections) ∧
      (∀ h' ∈ Y.GrHatSections, F.pullSection h' ∈ X.GrHatSections)

/-- `f_* = G_*F^*`, `f^* = F_*G^*` are well-defined maps between the `Γ(π̂)`, and
`(f⁻¹)_* = f^*`, `(g ∘ f)_* = g_* ∘ f_*`, `(g ∘ f)^* = f^* ∘ g^*`. -/
def GenIsoPartB : Prop :=
  -- well-defined maps `Γ → Γ`
  (∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y), EPLoc.IsGeneralizedIso f →
    ∀ d d' : Diagram X Y, EPLoc.homMk d = f → EPLoc.homMk d' = f →
      (∀ h ∈ X.X.GrHatSections,
        d.pushSection h ∈ Y.X.GrHatSections ∧ d.pushSection h = d'.pushSection h) ∧
      (∀ h' ∈ Y.X.GrHatSections,
        d.pullSection h' ∈ X.X.GrHatSections ∧ d.pullSection h' = d'.pullSection h')) ∧
  -- `(f⁻¹)_* = f^*`
  (∀ (X Y : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y) (g : EPLoc.of Y ⟶ EPLoc.of X),
    f ≫ g = 𝟙 _ → g ≫ f = 𝟙 _ →
    ∀ (d : Diagram X Y) (e : Diagram Y X), EPLoc.homMk d = f → EPLoc.homMk e = g →
      ∀ h' ∈ Y.X.GrHatSections, e.pushSection h' = d.pullSection h') ∧
  -- `(g ∘ f)_* = g_* ∘ f_*` and `(g ∘ f)^* = f^* ∘ g^*`
  (∀ (X Y Z : EP.{0}) (f : EPLoc.of X ⟶ EPLoc.of Y) (g : EPLoc.of Y ⟶ EPLoc.of Z),
    EPLoc.IsGeneralizedIso f → EPLoc.IsGeneralizedIso g →
    ∀ (d : Diagram X Y) (e : Diagram Y Z) (c : Diagram X Z),
      EPLoc.homMk d = f → EPLoc.homMk e = g → EPLoc.homMk c = f ≫ g →
      (∀ h ∈ X.X.GrHatSections, c.pushSection h = e.pushSection (d.pushSection h)) ∧
      (∀ h'' ∈ Z.X.GrHatSections, c.pullSection h'' = d.pullSection (e.pullSection h'')))

/-- Lemma 11.3.4 with (11.8), (11.9). -/
def B : Prop := EquivPartB ∧ GenIsoPartB

end RoundTrip.V11_20
