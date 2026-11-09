import Polyfold
/-! Blind formalization of V10_17 (the text's Part II, §10.2, Definition 10.2.1, p. 477 of the
Springer 2021 book; 2017: Definition 10.3, p. 342).

Text: for `F : X → Y`, `G : Z → Y`, `X ×_Y Z` has objects `(x, φ, z)` with `φ : F(x) → G(z)` and
morphisms `(h, φ, k)`, with source, target, units, inverses `ι` and composition as listed.

The listed structure maps, as I read the definition: a morphism `(h, φ, k)` has `h : x → x'` in
`X`, `k : z → z'` in `Z` and `φ : F(x) → G(z)` in `Y`;
`s(h, φ, k) = (s(h), φ, s(k))`, `t(h, φ, k) = (t(h), G(k) ∘ φ ∘ F(h⁻¹), t(k))`,
`1_{(x, φ, z)} = (1_x, φ, 1_z)`, `ι(h, φ, k) = (h⁻¹, G(k) ∘ φ ∘ F(h⁻¹), k⁻¹)`,
`(h', φ', k') ∘ (h, φ, k) = (h' ∘ h, φ, k' ∘ k)` when `s(h', φ', k') = t(h, φ, k)`.

Choices:
- This item is a definition.  Setting: ep-groupoids `X`, `Y`, `Z` (the project's `EpGroupoid`,
  Definition 7.3, `RoundTrip/Blind/V7_3.lean`), all six spaces in `Type` (universe 0, as in the
  other Part II blind files); `F`, `G` sc-smooth functors (`EpFunctor`,
  `RoundTrip/Blind/V7_9.lean`).  The definition only needs functors; the project's construction
  takes sc-smooth ones, which is the setting of §10.2.
- B says that the project's weak fibred product (`WeakFibredProduct.Obj F G`,
  `WeakFibredProduct.Mor F G` with the entry maps `x`, `φ`, `z`, `h`, `k`, the constructors
  `Obj.mk`, `Mor.mk`, and the groupoid `WeakFibredProduct.groupoid F G`) is the text's:
  (a) objects are exactly the triples `(x, φ, z)` with `φ : F(x) → G(z)` (the entries satisfy
  the constraint, determine the object, and every such triple occurs); (b) the same for the
  morphisms `(h, φ, k)` with `φ : F(s h) → G(s k)`; (c) the five structure maps are the listed
  ones, the composition on composable pairs only (the text defines it only there).  Since the
  project's `GroupoidStr` satisfies the groupoid laws, this also contains the text's implicit
  claim that these data form a groupoid.
- `G(k) ∘ φ ∘ F(h⁻¹)` is written `Y.comp (G.mor k) (Y.comp φ (F.mor (X.inv h)))` (`F(h⁻¹) =
  F(h)⁻¹` and the bracketing do not matter, by functoriality and associativity on composable
  pairs).  Composition order: `comp a b = a ∘ b`, `b` first (the project's `GroupoidStr`).
- Nothing looks false to me.
-/
namespace RoundTrip.V10_17
open Polyfold

section
variable {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjZ MorZ : Type} [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
  [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
  {X : EpGroupoid ObjX MorX} {Y : EpGroupoid ObjY MorY} {Z : EpGroupoid ObjZ MorZ}

/-- `G(k) ∘ φ ∘ F(h⁻¹)`, the middle entry of `t(h, φ, k)` and of `ι(h, φ, k)`. -/
def conjB (F : EpFunctor X Y) (G : EpFunctor Z Y) (h : MorX) (φ : MorY) (k : MorZ) : MorY :=
  Y.comp (G.mor k) (Y.comp φ (F.mor (X.inv h)))

/-- **Definition 10.2.1** for the project's weak fibred product of `F` and `G`. -/
def IsTextWFPB (F : EpFunctor X Y) (G : EpFunctor Z Y) : Prop :=
  -- (a) the objects are the triples `(x, φ, z)`, `φ : F(x) → G(z)`
  (∀ o : WeakFibredProduct.Obj F G, Y.src o.φ = F.obj o.x ∧ Y.tgt o.φ = G.obj o.z) ∧
  (∀ o o' : WeakFibredProduct.Obj F G, o.x = o'.x → o.φ = o'.φ → o.z = o'.z → o = o') ∧
  (∀ (x : ObjX) (φ : MorY) (z : ObjZ) (h₁ : Y.src φ = F.obj x) (h₂ : Y.tgt φ = G.obj z),
    (WeakFibredProduct.Obj.mk F G x φ z h₁ h₂).x = x ∧
      (WeakFibredProduct.Obj.mk F G x φ z h₁ h₂).φ = φ ∧
      (WeakFibredProduct.Obj.mk F G x φ z h₁ h₂).z = z) ∧
  -- (b) the morphisms are the triples `(h, φ, k)`, `h : x → x'`, `k : z → z'`, `φ : F(x) → G(z)`
  (∀ m : WeakFibredProduct.Mor F G,
    Y.src m.φ = F.obj (X.src m.h) ∧ Y.tgt m.φ = G.obj (Z.src m.k)) ∧
  (∀ m m' : WeakFibredProduct.Mor F G, m.h = m'.h → m.φ = m'.φ → m.k = m'.k → m = m') ∧
  (∀ (h : MorX) (φ : MorY) (k : MorZ) (h₁ : Y.src φ = F.obj (X.src h))
      (h₂ : Y.tgt φ = G.obj (Z.src k)),
    (WeakFibredProduct.Mor.mk F G h φ k h₁ h₂).h = h ∧
      (WeakFibredProduct.Mor.mk F G h φ k h₁ h₂).φ = φ ∧
      (WeakFibredProduct.Mor.mk F G h φ k h₁ h₂).k = k) ∧
  -- (c) source `s(h, φ, k) = (s(h), φ, s(k))`
  (∀ m : WeakFibredProduct.Mor F G,
    ((WeakFibredProduct.groupoid F G).src m).x = X.src m.h ∧
      ((WeakFibredProduct.groupoid F G).src m).φ = m.φ ∧
      ((WeakFibredProduct.groupoid F G).src m).z = Z.src m.k) ∧
  -- target `t(h, φ, k) = (t(h), G(k) ∘ φ ∘ F(h⁻¹), t(k))`
  (∀ m : WeakFibredProduct.Mor F G,
    ((WeakFibredProduct.groupoid F G).tgt m).x = X.tgt m.h ∧
      ((WeakFibredProduct.groupoid F G).tgt m).φ = conjB F G m.h m.φ m.k ∧
      ((WeakFibredProduct.groupoid F G).tgt m).z = Z.tgt m.k) ∧
  -- unit `1_{(x, φ, z)} = (1_x, φ, 1_z)`
  (∀ o : WeakFibredProduct.Obj F G,
    ((WeakFibredProduct.groupoid F G).unit o).h = X.unit o.x ∧
      ((WeakFibredProduct.groupoid F G).unit o).φ = o.φ ∧
      ((WeakFibredProduct.groupoid F G).unit o).k = Z.unit o.z) ∧
  -- inverse `ι(h, φ, k) = (h⁻¹, G(k) ∘ φ ∘ F(h⁻¹), k⁻¹)`
  (∀ m : WeakFibredProduct.Mor F G,
    ((WeakFibredProduct.groupoid F G).inv m).h = X.inv m.h ∧
      ((WeakFibredProduct.groupoid F G).inv m).φ = conjB F G m.h m.φ m.k ∧
      ((WeakFibredProduct.groupoid F G).inv m).k = Z.inv m.k) ∧
  -- composition `(h', φ', k') ∘ (h, φ, k) = (h' ∘ h, φ, k' ∘ k)` on composable pairs
  (∀ m' m : WeakFibredProduct.Mor F G,
    (WeakFibredProduct.groupoid F G).src m' = (WeakFibredProduct.groupoid F G).tgt m →
      ((WeakFibredProduct.groupoid F G).comp m' m).h = X.comp m'.h m.h ∧
        ((WeakFibredProduct.groupoid F G).comp m' m).φ = m.φ ∧
        ((WeakFibredProduct.groupoid F G).comp m' m).k = Z.comp m'.k m.k)

end

/-- Definition 10.2.1: the project's weak fibred product `X ×_Y Z` is the text's groupoid. -/
def B : Prop :=
  ∀ (ObjX MorX ObjY MorY ObjZ MorZ : Type)
    [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
    [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
    (X : EpGroupoid ObjX MorX) (Y : EpGroupoid ObjY MorY) (Z : EpGroupoid ObjZ MorZ)
    (F : EpFunctor X Y) (G : EpFunctor Z Y), IsTextWFPB F G

end RoundTrip.V10_17
