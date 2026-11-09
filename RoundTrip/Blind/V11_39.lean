import Polyfold
/-! Blind formalization of V11_39 (the text's Part II, §11.6, Theorem 11.6.6, p. 555 of the
Springer 2021 book, with steps (D)–(F) of the proof, pp. 560–561; 2017: Theorem 11.10, p. 405).

Text: (1) `H` is a proper covering; (2) `(π_{Y''}, π_{X''})` is an equivalence; (3) the two
composites to `F'` are naturally equivalent; tameness of `X''` passes to the products; if
`(ζ, ξ)` is an equivalence, so is `(π_Y, π_X)`.

Choices:
- Setting, the weak fibred products `P = Y ×_{Y'} Y''` (`PB`) and `Q = X ×_{X'} X''` (`QB`), and
  `H` given by (11.18), (11.19) (`IsHB`) exactly as in my `RoundTrip/Blind/V11_38.lean` (copied):
  proper covering functors `F : Y → X`, `F' : Y' → X'`, `F'' : Y'' → X''` (the project's
  `EpFunctor.IsProperCovering`), all spaces in `Type`, `Γ = (Ψ, Φ) : F → F'` an equivalence and
  `Λ = (ζ, ξ) : F'' → F'` a functor (the project's `ProperCoveringHom`, `IsEquivalence`,
  characterized in my `RoundTrip/Blind/V11_36.lean`).
- (1) as in V11_38: an sc-smooth functor `H : P → Q` with (11.18), (11.19), a proper covering.
- The projections, as I read them: `π_Y(y, ψ', y'') = y`, `π_Y(h, ψ', h'') = h`, and
  `π_{Y''}`, `π_X`, `π_{X''}` likewise (first resp. last entry).  `(π_Y, π_X) : H → F` and
  `(π_{Y''}, π_{X''}) : H → F''` are functors between proper coverings (Definition 11.6.4 (1));
  I assert that elements `πL`, `πR` of the project's `ProperCoveringHom` with these components
  exist (they are unique by V11_36), and do not use the project's `projLeftHom`,
  `projRightHom`, `WeakFibredProduct.projLeft/projRight`.
- (2) "equivalence": the project's `ProperCoveringHom.IsEquivalence` (Definition 11.6.4 (2),
  V11_36).
- (3) "the two composites to `F'`": `(Ψ, Φ) ∘ (π_Y, π_X) = (Ψ ∘ π_Y, Φ ∘ π_X)` and
  `(ζ, ξ) ∘ (π_{Y''}, π_{X''}) = (ζ ∘ π_{Y''}, ξ ∘ π_{X''})` (composition componentwise, with the
  project's `EpFunctor.comp`).  "naturally equivalent" (my `NatEquivB`): there is a natural
  transformation in the sense of Definition 11.6.5 (my `RoundTrip/Blind/V11_37.lean`): a pair
  of `EpNatTrans` `τ_P : Ψ ∘ π_Y → ζ ∘ π_{Y''}`, `τ_Q : Φ ∘ π_X → ξ ∘ π_{X''}` with
  `τ_Q ∘ H = F' ∘ τ_P` (11.20).  The direction does not matter (the targets are groupoids); I
  take the direction of the displayed `≃` from the first composite to the second.
- "tameness of `X''` passes to the products" (my reading): if `X''` is tame (the project's
  `EpGroupoid.IsTame`: the object M-polyfold is tame), then `P` and `Q` are tame.
- "if `(ζ, ξ)` is an equivalence, so is `(π_Y, π_X)`": `Λ.IsEquivalence → πL.IsEquivalence`.
- B is the conjunction of all the claims.  Nothing looks false to me.
-/
namespace RoundTrip.V11_39
open Polyfold

section
variable {ObjY MorY : Type} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY' MorY' : Type} [TopologicalSpace ObjY'] [T2Space ObjY'] [ParacompactSpace ObjY']
  [TopologicalSpace MorY'] [T2Space MorY'] [ParacompactSpace MorY']
  {ObjX' MorX' : Type} [TopologicalSpace ObjX'] [T2Space ObjX'] [ParacompactSpace ObjX']
  [TopologicalSpace MorX'] [T2Space MorX'] [ParacompactSpace MorX']
  {ObjY'' MorY'' : Type} [TopologicalSpace ObjY''] [T2Space ObjY''] [ParacompactSpace ObjY'']
  [TopologicalSpace MorY''] [T2Space MorY''] [ParacompactSpace MorY'']
  {ObjX'' MorX'' : Type} [TopologicalSpace ObjX''] [T2Space ObjX''] [ParacompactSpace ObjX'']
  [TopologicalSpace MorX''] [T2Space MorX''] [ParacompactSpace MorX'']
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}
  {Y' : EpGroupoid ObjY' MorY'} {X' : EpGroupoid ObjX' MorX'}
  {Y'' : EpGroupoid ObjY'' MorY''} {X'' : EpGroupoid ObjX'' MorX''}
  {F : EpFunctor Y X} {F' : EpFunctor Y' X'} {F'' : EpFunctor Y'' X''}

/-- The ep-groupoid `P = Y ×_{Y'} Y''` (weak fibred product of `Ψ` and `ζ`). -/
noncomputable def PB (Γ : ProperCoveringHom F F') (hΓ : Γ.IsEquivalence)
    (Λ : ProperCoveringHom F'' F') :
    EpGroupoid (WeakFibredProduct.Obj Γ.Ψ Λ.Ψ) (WeakFibredProduct.Mor Γ.Ψ Λ.Ψ) :=
  WeakFibredProduct.epGroupoid Γ.Ψ Λ.Ψ (Or.inl hΓ.isEquivalence_Ψ.isLocalScDiffeo_obj)

/-- The ep-groupoid `Q = X ×_{X'} X''` (weak fibred product of `Φ` and `ξ`). -/
noncomputable def QB (Γ : ProperCoveringHom F F') (hΓ : Γ.IsEquivalence)
    (Λ : ProperCoveringHom F'' F') :
    EpGroupoid (WeakFibredProduct.Obj Γ.Φ Λ.Φ) (WeakFibredProduct.Mor Γ.Φ Λ.Φ) :=
  WeakFibredProduct.epGroupoid Γ.Φ Λ.Φ (Or.inl hΓ.isEquivalence_Φ.isLocalScDiffeo_obj)

/-- `H` is given by (11.18) on objects and (11.19) on morphisms. -/
def IsHB (Γ : ProperCoveringHom F F') (hΓ : Γ.IsEquivalence) (Λ : ProperCoveringHom F'' F')
    (H : EpFunctor (PB Γ hΓ Λ) (QB Γ hΓ Λ)) : Prop :=
  (∀ o : WeakFibredProduct.Obj Γ.Ψ Λ.Ψ,
    (H.obj o).x = F.obj o.x ∧ (H.obj o).φ = F'.mor o.φ ∧ (H.obj o).z = F''.obj o.z) ∧
  (∀ m : WeakFibredProduct.Mor Γ.Ψ Λ.Ψ,
    (H.mor m).h = F.mor m.h ∧ (H.mor m).φ = F'.mor m.φ ∧ (H.mor m).k = F''.mor m.k)

end

section
variable {ObjA MorA : Type} [TopologicalSpace ObjA] [T2Space ObjA] [ParacompactSpace ObjA]
  [TopologicalSpace MorA] [T2Space MorA] [ParacompactSpace MorA]
  {ObjC MorC : Type} [TopologicalSpace ObjC] [T2Space ObjC] [ParacompactSpace ObjC]
  [TopologicalSpace MorC] [T2Space MorC] [ParacompactSpace MorC]
  {ObjY' MorY' : Type} [TopologicalSpace ObjY'] [T2Space ObjY'] [ParacompactSpace ObjY']
  [TopologicalSpace MorY'] [T2Space MorY'] [ParacompactSpace MorY']
  {ObjX' MorX' : Type} [TopologicalSpace ObjX'] [T2Space ObjX'] [ParacompactSpace ObjX']
  [TopologicalSpace MorX'] [T2Space MorX'] [ParacompactSpace MorX']
  {A : EpGroupoid ObjA MorA} {C : EpGroupoid ObjC MorC}
  {Y' : EpGroupoid ObjY' MorY'} {X' : EpGroupoid ObjX' MorX'}

/-- Definition 11.6.5: the functors `(ζ, ξ), (ζ', ξ') : G → F'` (from `G : A → C` to
`F' : Y' → X'`) are naturally equivalent: there are natural transformations `τ_Y : ζ → ζ'`,
`τ_X : ξ → ξ'` with `τ_X ∘ G = F' ∘ τ_Y` (11.20). -/
def NatEquivB (G : EpFunctor A C) (F' : EpFunctor Y' X') (ζ ζ' : EpFunctor A Y')
    (ξ ξ' : EpFunctor C X') : Prop :=
  ∃ (τY : EpNatTrans ζ ζ') (τX : EpNatTrans ξ ξ'), ∀ a : ObjA, τX.app (G.obj a) = F'.mor (τY.app a)

end

/-- Theorem 11.6.6: `H` is a proper covering, `(π_{Y''}, π_{X''}) : H → F''` is an equivalence,
`(Ψ, Φ) ∘ (π_Y, π_X) ≃ (ζ, ξ) ∘ (π_{Y''}, π_{X''})`, `(π_Y, π_X)` is an equivalence when `(ζ, ξ)`
is, and `P`, `Q` are tame when `X''` is. -/
def B : Prop :=
  ∀ (ObjY MorY : Type) [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
    (ObjX MorX : Type) [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
    (ObjY' MorY' : Type) [TopologicalSpace ObjY'] [T2Space ObjY'] [ParacompactSpace ObjY']
    [TopologicalSpace MorY'] [T2Space MorY'] [ParacompactSpace MorY']
    (ObjX' MorX' : Type) [TopologicalSpace ObjX'] [T2Space ObjX'] [ParacompactSpace ObjX']
    [TopologicalSpace MorX'] [T2Space MorX'] [ParacompactSpace MorX']
    (ObjY'' MorY'' : Type) [TopologicalSpace ObjY''] [T2Space ObjY''] [ParacompactSpace ObjY'']
    [TopologicalSpace MorY''] [T2Space MorY''] [ParacompactSpace MorY'']
    (ObjX'' MorX'' : Type) [TopologicalSpace ObjX''] [T2Space ObjX''] [ParacompactSpace ObjX'']
    [TopologicalSpace MorX''] [T2Space MorX''] [ParacompactSpace MorX'']
    (Y : EpGroupoid ObjY MorY) (X : EpGroupoid ObjX MorX)
    (Y' : EpGroupoid ObjY' MorY') (X' : EpGroupoid ObjX' MorX')
    (Y'' : EpGroupoid ObjY'' MorY'') (X'' : EpGroupoid ObjX'' MorX'')
    (F : EpFunctor Y X) (F' : EpFunctor Y' X') (F'' : EpFunctor Y'' X''),
    F.IsProperCovering → F'.IsProperCovering → F''.IsProperCovering →
    ∀ (Γ : ProperCoveringHom F F') (hΓ : Γ.IsEquivalence) (Λ : ProperCoveringHom F'' F'),
      (∃ H : EpFunctor (PB Γ hΓ Λ) (QB Γ hΓ Λ),
        -- (1) `H` of (11.18), (11.19) is a proper covering
        IsHB Γ hΓ Λ H ∧ H.IsProperCovering ∧
        ∃ (πR : ProperCoveringHom H F'') (πL : ProperCoveringHom H F),
          -- `πR = (π_{Y''}, π_{X''})` and `πL = (π_Y, π_X)`
          (∀ o : WeakFibredProduct.Obj Γ.Ψ Λ.Ψ, πR.Ψ.obj o = o.z) ∧
          (∀ m : WeakFibredProduct.Mor Γ.Ψ Λ.Ψ, πR.Ψ.mor m = m.k) ∧
          (∀ o : WeakFibredProduct.Obj Γ.Φ Λ.Φ, πR.Φ.obj o = o.z) ∧
          (∀ m : WeakFibredProduct.Mor Γ.Φ Λ.Φ, πR.Φ.mor m = m.k) ∧
          (∀ o : WeakFibredProduct.Obj Γ.Ψ Λ.Ψ, πL.Ψ.obj o = o.x) ∧
          (∀ m : WeakFibredProduct.Mor Γ.Ψ Λ.Ψ, πL.Ψ.mor m = m.h) ∧
          (∀ o : WeakFibredProduct.Obj Γ.Φ Λ.Φ, πL.Φ.obj o = o.x) ∧
          (∀ m : WeakFibredProduct.Mor Γ.Φ Λ.Φ, πL.Φ.mor m = m.h) ∧
          -- (2) `(π_{Y''}, π_{X''})` is an equivalence
          πR.IsEquivalence ∧
          -- (3) `(Ψ, Φ) ∘ (π_Y, π_X) ≃ (ζ, ξ) ∘ (π_{Y''}, π_{X''})`
          NatEquivB H F' (Γ.Ψ.comp πL.Ψ) (Λ.Ψ.comp πR.Ψ) (Γ.Φ.comp πL.Φ) (Λ.Φ.comp πR.Φ) ∧
          -- if `(ζ, ξ)` is an equivalence, so is `(π_Y, π_X)`
          (Λ.IsEquivalence → πL.IsEquivalence)) ∧
      -- tameness of `X''` passes to `Y ×_{Y'} Y''` and `X ×_{X'} X''`
      (X''.IsTame → (PB Γ hΓ Λ).IsTame ∧ (QB Γ hΓ Λ).IsTame)

end RoundTrip.V11_39
