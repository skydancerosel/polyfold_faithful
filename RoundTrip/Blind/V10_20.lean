import Polyfold
/-! Blind formalization of V10_20 (the text's Part II, §10.2, Theorem 10.2.2, the last two
claims, p. 478 of the Springer 2021 book; 2017: Theorem 10.2, p. 343).

Text: if `G` is an equivalence, `π_X` is one and `d = d_X ∘ π_X`; if both are,
`d_X(x) = d(x, φ, z) = d_Z(z)`.

Choices:
- Setting and the ep-groupoid `X ×_Y Z` exactly as in my `RoundTrip/Blind/V10_18.lean` (all
  spaces in `Type`; `X ×_Y Z` built from scratch on subtypes of `X × 𝐘 × Z` and `𝐗 × 𝐘 × 𝐙`
  with the structure maps of Definition 10.2.1 and the sub-M-polyfold structures, `IsWFPEpB`;
  paracompactness witnesses existentially quantified).
- Reading of "if `G` is an equivalence": `G` an equivalence and `F` only sc-smooth (the case
  symmetric to V10_19; the item's "if both are" for the second claim shows that the first one
  does not assume `F` to be an equivalence).  The existence of the ep-groupoid `X ×_Y Z` in this
  case (the symmetric form of the first claim, V10_18) is restated, since `π_X` and `d` refer to
  it.  If the text meant "if also `G` is an equivalence", my (a) is stronger than the text.
- `π_X`: an sc-smooth functor (`EpFunctor`) `(x, φ, z) ↦ x`, `(h, φ, k) ↦ h`; "equivalence" is the
  project's `EpFunctor.IsEquivalence` (2021 Definition 10.1.1, `RoundTrip/Blind/V10_1.lean`).
- `d = d_{X ×_Y Z}`, `d_X`, `d_Z`: degeneracy indices of the object M-polyfolds (the project's
  `MPolyfold.degIndex`, Definition 2.22).
- (b) is asserted for every object `(x, φ, z)`, both equalities.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_20
open Polyfold

section
variable {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjZ MorZ : Type} [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
  [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
  {X : EpGroupoid ObjX MorX} {Y : EpGroupoid ObjY MorY} {Z : EpGroupoid ObjZ MorZ}

/-- The objects `(x, φ, z) ∈ X × 𝐘 × Z` of `X ×_Y Z`: `φ : F(x) → G(z)`. -/
def objSetB (F : EpFunctor X Y) (G : EpFunctor Z Y) : Set (ObjX × MorY × ObjZ) :=
  {p | Y.src p.2.1 = F.obj p.1 ∧ Y.tgt p.2.1 = G.obj p.2.2}

/-- The morphisms `(h, φ, k) ∈ 𝐗 × 𝐘 × 𝐙` of `X ×_Y Z`: `φ : F(s h) → G(s k)`. -/
def morSetB (F : EpFunctor X Y) (G : EpFunctor Z Y) : Set (MorX × MorY × MorZ) :=
  {q | Y.src q.2.1 = F.obj (X.src q.1) ∧ Y.tgt q.2.1 = G.obj (Z.src q.2.2)}

/-- `G(k) ∘ φ ∘ F(h⁻¹)`. -/
def conjB (F : EpFunctor X Y) (G : EpFunctor Z Y) (h : MorX) (φ : MorY) (k : MorZ) : MorY :=
  Y.comp (G.mor k) (Y.comp φ (F.mor (X.inv h)))

/-- **Definition 10.2.1**: the groupoid `Γ` on these objects and morphisms has the structure maps
of the weak fibred product. -/
def HasWFPMapsB (F : EpFunctor X Y) (G : EpFunctor Z Y)
    (Γ : GroupoidStr (objSetB F G) (morSetB F G)) : Prop :=
  (∀ m, (Γ.src m).1 = (X.src m.1.1, m.1.2.1, Z.src m.1.2.2)) ∧
  (∀ m, (Γ.tgt m).1 = (X.tgt m.1.1, conjB F G m.1.1 m.1.2.1 m.1.2.2, Z.tgt m.1.2.2)) ∧
  (∀ o, (Γ.unit o).1 = (X.unit o.1.1, o.1.2.1, Z.unit o.1.2.2)) ∧
  (∀ m, (Γ.inv m).1 = (X.inv m.1.1, conjB F G m.1.1 m.1.2.1 m.1.2.2, Z.inv m.1.2.2)) ∧
  (∀ m' m, Γ.src m' = Γ.tgt m →
    (Γ.comp m' m).1 = (X.comp m'.1.1 m.1.1, m.1.2.1, Z.comp m'.1.2.2 m.1.2.2))

/-- `E` is the weak fibred product `X ×_Y Z` as an ep-groupoid: the groupoid of
Definition 10.2.1, with the structures of sub-M-polyfolds of `X × 𝐘 × Z` (objects) and of
`𝐗 × 𝐘 × 𝐙` (morphisms). -/
def IsWFPEpB (F : EpFunctor X Y) (G : EpFunctor Z Y)
    [ParacompactSpace (MorY × ObjZ)] [ParacompactSpace (ObjX × MorY × ObjZ)]
    [ParacompactSpace (MorY × MorZ)] [ParacompactSpace (MorX × MorY × MorZ)]
    [ParacompactSpace (objSetB F G)] [ParacompactSpace (morSetB F G)]
    (E : EpGroupoid (objSetB F G) (morSetB F G)) : Prop :=
  HasWFPMapsB F G E.toGroupoidStr ∧
  ∃ (hS : (X.PObj.prod (Y.PMor.prod Z.PObj)).IsSubMPolyfold (objSetB F G))
    (hT : (X.PMor.prod (Y.PMor.prod Z.PMor)).IsSubMPolyfold (morSetB F G)),
    E.PObj = MPolyfold.subPolyfold hS ∧ E.PMor = MPolyfold.subPolyfold hT

end

/-- Theorem 10.2.2, last two claims: (a) for an equivalence `G`, `π_X` is an equivalence and
`d(x, φ, z) = d_X(x)`; (b) for two equivalences, `d_X(x) = d(x, φ, z) = d_Z(z)`. -/
def B : Prop :=
  ∀ (ObjX MorX ObjY MorY ObjZ MorZ : Type)
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
    [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
    (X : EpGroupoid ObjX MorX) (Y : EpGroupoid ObjY MorY) (Z : EpGroupoid ObjZ MorZ)
    (F : EpFunctor X Y) (G : EpFunctor Z Y),
    -- (a) `G` an equivalence
    (G.IsEquivalence →
      ∃ (_ : ParacompactSpace (MorY × ObjZ)) (_ : ParacompactSpace (ObjX × MorY × ObjZ))
        (_ : ParacompactSpace (MorY × MorZ)) (_ : ParacompactSpace (MorX × MorY × MorZ))
        (_ : ParacompactSpace (objSetB F G)) (_ : ParacompactSpace (morSetB F G))
        (E : EpGroupoid (objSetB F G) (morSetB F G)), IsWFPEpB F G E ∧
        (∃ πX : EpFunctor E X,
          πX.obj = (fun a => a.1.1) ∧ πX.mor = (fun m => m.1.1) ∧ πX.IsEquivalence) ∧
        ∀ a, E.PObj.degIndex a = X.PObj.degIndex a.1.1) ∧
    -- (b) `F` and `G` equivalences
    (F.IsEquivalence → G.IsEquivalence →
      ∃ (_ : ParacompactSpace (MorY × ObjZ)) (_ : ParacompactSpace (ObjX × MorY × ObjZ))
        (_ : ParacompactSpace (MorY × MorZ)) (_ : ParacompactSpace (MorX × MorY × MorZ))
        (_ : ParacompactSpace (objSetB F G)) (_ : ParacompactSpace (morSetB F G))
        (E : EpGroupoid (objSetB F G) (morSetB F G)), IsWFPEpB F G E ∧
        ∀ a, X.PObj.degIndex a.1.1 = E.PObj.degIndex a ∧
          E.PObj.degIndex a = Z.PObj.degIndex a.1.2.2)

end RoundTrip.V10_20
