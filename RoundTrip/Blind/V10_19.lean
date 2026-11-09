import Polyfold
/-! Blind formalization of V10_19 (the text's Part II, §10.2, Theorem 10.2.2, pp. 477–478 of the
Springer 2021 book; 2017: Theorem 10.2, p. 343), the claims for an equivalence `F`.

Text: if `F` is an equivalence, `π_Z` is an equivalence, `F ∘ π_X ≃ G ∘ π_Z`,
`d_{X ×_Y Z} = d_Z ∘ π_Z`, and tameness and a paracompact orbit space pass from `Z`.

Choices:
- Setting and the ep-groupoid `X ×_Y Z` exactly as in my `RoundTrip/Blind/V10_18.lean` (all
  spaces in `Type`; `F`, `G` sc-smooth functors, `G` arbitrary; `X ×_Y Z` built from scratch on
  subtypes of `X × 𝐘 × Z` and `𝐗 × 𝐘 × 𝐙` with the structure maps of Definition 10.2.1 and the
  sub-M-polyfold structures, `IsWFPEpB`; paracompactness witnesses existentially quantified).
  The claims below are made for this ep-groupoid, whose existence (V10_18) is restated.
- `π_X`, `π_Z`: sc-smooth functors (`EpFunctor`) with `(x, φ, z) ↦ x`, `(h, φ, k) ↦ h`, resp.
  `↦ z`, `↦ k`; their existence as `EpFunctor`s (sc-smoothness) is part of the claim.
- "`π_Z` is an equivalence": the project's `EpFunctor.IsEquivalence` (2021 Definition 10.1.1,
  `RoundTrip/Blind/V10_1.lean`).
- "`F ∘ π_X ≃ G ∘ π_Z`" (the square commutes up to a natural transformation): there is a natural
  transformation `F ∘ π_X → G ∘ π_Z` of sc-smooth functors, the project's `EpNatTrans` (read
  with `#print`: an sc-smooth `τ : X ×_Y Z → 𝐘` with `τ(a) : F(π_X a) → G(π_Z a)` and
  naturality `τ(t m) ∘ F(π_X m) = G(π_Z m) ∘ τ(s m)`); composites by `EpFunctor.comp`.  Only
  existence is claimed (the text does not name the transformation in the statement).
- `d_{X ×_Y Z}`, `d_Z`: degeneracy indices of the object M-polyfolds (the project's
  `MPolyfold.degIndex`, Definition 2.22; Definition 7.5 uses the object M-polyfold).
- "tameness passes from `Z`": `Z` tame ⇒ `X ×_Y Z` tame, tameness of an ep-groupoid being that
  of its object M-polyfold (Definition 7.6; `MPolyfold.IsTame`, Definition 2.37, trusted).
  "a paracompact orbit space passes from `Z`": `|Z|` paracompact ⇒ `|X ×_Y Z|` paracompact
  (orbit spaces with the project's quotient topology on `GroupoidStr.OrbitSpace`).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_19
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

/-- Theorem 10.2.2 for an equivalence `F`: `π_Z` is an equivalence, `F ∘ π_X ≃ G ∘ π_Z`,
`d_{X ×_Y Z}(x, φ, z) = d_Z(z)`, and tameness and paracompactness of the orbit space pass from
`Z` to `X ×_Y Z`. -/
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
    F.IsEquivalence →
      ∃ (_ : ParacompactSpace (MorY × ObjZ)) (_ : ParacompactSpace (ObjX × MorY × ObjZ))
        (_ : ParacompactSpace (MorY × MorZ)) (_ : ParacompactSpace (MorX × MorY × MorZ))
        (_ : ParacompactSpace (objSetB F G)) (_ : ParacompactSpace (morSetB F G))
        (E : EpGroupoid (objSetB F G) (morSetB F G)), IsWFPEpB F G E ∧
        ∃ (πX : EpFunctor E X) (πZ : EpFunctor E Z),
          -- the projections
          πX.obj = (fun a => a.1.1) ∧ πX.mor = (fun m => m.1.1) ∧
          πZ.obj = (fun a => a.1.2.2) ∧ πZ.mor = (fun m => m.1.2.2) ∧
          -- `π_Z` is an equivalence
          πZ.IsEquivalence ∧
          -- `F ∘ π_X ≃ G ∘ π_Z`
          Nonempty (EpNatTrans (EpFunctor.comp F πX) (EpFunctor.comp G πZ)) ∧
          -- `d_{X ×_Y Z} = d_Z ∘ π_Z`
          (∀ a, E.PObj.degIndex a = Z.PObj.degIndex a.1.2.2) ∧
          -- tameness passes from `Z`
          (Z.PObj.IsTame → E.PObj.IsTame) ∧
          -- a paracompact orbit space passes from `Z`
          (ParacompactSpace Z.OrbitSpace → ParacompactSpace E.OrbitSpace)

end RoundTrip.V10_19
