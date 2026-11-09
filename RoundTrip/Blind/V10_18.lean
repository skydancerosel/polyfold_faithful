import Polyfold
/-! Blind formalization of V10_18 (the text's Part II, §10.2, Theorem 10.2.2, first claim, p. 477
of the Springer 2021 book; 2017: Theorem 10.2, p. 343).

Text: if `F` is an equivalence and `G` sc-smooth, `X ×_Y Z` is an ep-groupoid with the
sub-M-polyfold structures from `X × 𝐘 × Z` and `𝐗 × 𝐘 × 𝐙`.

Choices:
- Setting: ep-groupoids `X`, `Y`, `Z` (the project's `EpGroupoid`, Definition 7.3, checked in
  `RoundTrip/Blind/V7_3.lean`), all six spaces in `Type` (universe 0, as in the other Part II
  blind files); `F : X → Y`, `G : Z → Y` sc-smooth functors (`EpFunctor`,
  `RoundTrip/Blind/V7_9.lean`); "equivalence" is the project's `EpFunctor.IsEquivalence`
  (2021 Definition 10.1.1, read with `#print`, characterized in `RoundTrip/Blind/V10_1.lean`).
- `X ×_Y Z` is built from scratch (the project's `WeakFibredProduct` is not used): objects the
  subtype `objSetB F G` of `X × 𝐘 × Z` (triples `(x, φ, z)` with `φ : F(x) → G(z)`), morphisms the
  subtype `morSetB F G` of `𝐗 × 𝐘 × 𝐙` (triples `(h, φ, k)` with `φ : F(s h) → G(s k)`), with the
  subspace topologies; the structure maps of Definition 10.2.1 (as I read them in
  `RoundTrip/Blind/V10_17.lean`) are imposed on the `.1` of the values (`HasWFPMapsB`), the
  composition on composable pairs only.
- "is an ep-groupoid with the sub-M-polyfold structures": there is a project `EpGroupoid` on
  these subtypes (Definition 7.3, by V7_3) with these structure maps whose object M-polyfold is
  `objSetB F G` as a sub-M-polyfold of the product M-polyfold `X × (𝐘 × Z)` and whose morphism
  M-polyfold is `morSetB F G` as a sub-M-polyfold of `𝐗 × (𝐘 × 𝐙)` (the project's
  `MPolyfold.prod` and `MPolyfold.subPolyfold`, as in V7_3; `X × 𝐘 × Z` is bracketed to the
  right).  The sub-M-polyfold properties are part of the claim.  The product and subset
  M-polyfolds need paracompactness of the products and of the subtypes as instance arguments;
  these are existentially quantified (true, M-polyfolds are metrizable); being `Prop`s, the
  structures do not depend on the witnesses.  The ep-groupoid is unique if it exists, so `∃` is
  the text's "the".
- `G(k) ∘ φ ∘ F(h⁻¹)` is `Y.comp (G.mor k) (Y.comp φ (F.mor (X.inv h)))`.
- Nothing looks false to me.
-/
namespace RoundTrip.V10_18
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

/-- Theorem 10.2.2, first claim: for an equivalence `F` and an sc-smooth `G`, the weak fibred
product `X ×_Y Z` with its sub-M-polyfold structures is an ep-groupoid. -/
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
        (E : EpGroupoid (objSetB F G) (morSetB F G)), IsWFPEpB F G E

end RoundTrip.V10_18
