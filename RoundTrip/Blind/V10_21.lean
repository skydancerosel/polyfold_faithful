import Polyfold
/-! Blind formalization of V10_21 (the text's Part II, §10.2, Remark 10.2.3, pp. 482–483 of the
Springer 2021 book; 2017: Remark 10.2, p. 347).

Text: for two equivalences both projections are equivalences, with a natural transformation `τ`
between `F ∘ π_X` and `G ∘ π_Z`; remarks on smaller models.

Choices:
- Setting and the ep-groupoid `X ×_Y Z` exactly as in my `RoundTrip/Blind/V10_18.lean` (all
  spaces in `Type`; `X ×_Y Z` built from scratch on subtypes of `X × 𝐘 × Z` and `𝐗 × 𝐘 × 𝐙`
  with the structure maps of Definition 10.2.1 and the sub-M-polyfold structures, `IsWFPEpB`;
  paracompactness witnesses existentially quantified); its existence is restated.
- `π_X`, `π_Z`: sc-smooth functors (`EpFunctor`) `(x, φ, z) ↦ x`, `(h, φ, k) ↦ h`, resp. `↦ z`,
  `↦ k`; "equivalence" is the project's `EpFunctor.IsEquivalence` (2021 Definition 10.1.1,
  `RoundTrip/Blind/V10_1.lean`).
- "a natural transformation `τ` between `F ∘ π_X` and `G ∘ π_Z`": there is an `EpNatTrans`
  (sc-smooth natural transformation, read with `#print`) from `F ∘ π_X` to `G ∘ π_Z`; the
  direction does not matter (its inverse is again one).  Only existence is claimed.
- "remarks on smaller models": not formalized (the item gives no precise statement).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_21
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

/-- Remark 10.2.3: for two equivalences `F`, `G`, both projections of `X ×_Y Z` are
equivalences, and there is a natural transformation `τ : F ∘ π_X → G ∘ π_Z`. -/
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
    F.IsEquivalence → G.IsEquivalence →
      ∃ (_ : ParacompactSpace (MorY × ObjZ)) (_ : ParacompactSpace (ObjX × MorY × ObjZ))
        (_ : ParacompactSpace (MorY × MorZ)) (_ : ParacompactSpace (MorX × MorY × MorZ))
        (_ : ParacompactSpace (objSetB F G)) (_ : ParacompactSpace (morSetB F G))
        (E : EpGroupoid (objSetB F G) (morSetB F G)), IsWFPEpB F G E ∧
        ∃ (πX : EpFunctor E X) (πZ : EpFunctor E Z),
          πX.obj = (fun a => a.1.1) ∧ πX.mor = (fun m => m.1.1) ∧
          πZ.obj = (fun a => a.1.2.2) ∧ πZ.mor = (fun m => m.1.2.2) ∧
          πX.IsEquivalence ∧ πZ.IsEquivalence ∧
          Nonempty (EpNatTrans (EpFunctor.comp F πX) (EpFunctor.comp G πZ))

end RoundTrip.V10_21
