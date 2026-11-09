import Polyfold
/-! Blind formalization of V8_43 (the 2017 book, Part II, §8.5.2 = 2021 §8.6.2, pp. 288–289:
the structure of strong bundle coverings).

Text: for a proper strong bundle covering functor `A` (2017 Definition 8.10), `Q ∘ A = F ∘ P`:
a strong bundle `P : W → Y` over an ep-groupoid comes with `μ_Y`, associating with a morphism
`φ : y → y'` a topological linear isomorphism `μ_Y(φ) : P⁻¹(y) → P⁻¹(y')`, a morphism `w → w'`
being a pair `(φ, w) : w → μ_Y(φ)(w)`; the same for `Q : V → X`.  On morphisms
`A(φ, w) = (F(φ), A_{s(φ)}(w))`, where `A_y : P⁻¹(y) → Q⁻¹(F(y))` is the topological linear
isomorphism induced by `A`, and `t(A(φ, w)) = A(t(φ, w))` gives
`μ_X(F(φ)) ∘ A_{s(φ)} = A_{t(φ)} ∘ μ_Y(φ)`.  With `Ban` the category of Banach spaces and
topological linear isomorphisms, `μ_Y : Y → Ban`, `μ_X : X → Ban` are functors, and `y ↦ A_y`
is a natural transformation `μ_Y → μ_X ∘ F`.

Choices:
- The quoted pages are the 2017 book's, so "proper strong bundle covering functor" is 2017
  Definition 8.10, in which `A : (W, 𝐖) → (V, 𝐕)` is a functor between the ep-groupoids of the
  two bundles: the project's `EpStrongBundle.IsProperStrongBundleCovering EW EV F A` with
  `A : EpFunctor EW.toEpGroupoid EV.toEpGroupoid` (read with `#print`; it contains
  `Q ∘ A = F ∘ P`).  (The 2021 form, with `A` a map `W → V`, is item V8_50.)
- Setting: universe 0 throughout.  `Y : EpGroupoid ObjY MorY`, `X : EpGroupoid ObjX MorX`,
  `W`, `V : Type` with their topologies, `P : W → ObjY`, `Q : V → ObjX` with the linear structures
  on the fibres, `BW`, `BV` Part I strong bundles over the object M-polyfolds, `EW`, `EV` the
  strong bundles over the ep-groupoids (structure maps `μ_Y = EW.μ`, `μ_X = EV.μ`, 2017
  Definition 8.4).  The instances `ParacompactSpace (𝐘 ₛ×_P W)`, `ParacompactSpace (𝐗 ₛ×_Q V)`
  are required by the project to form the ep-groupoids `(W, 𝐖)`, `(V, 𝐕)` (in the text these
  are M-polyfolds, paracompact by definition); `F : EpFunctor Y X`.
- Morphisms of `(W, 𝐖)` are the pairs `m = (φ, w)` with `P(w) = s(φ)` (the project's
  `pullbackSpace P Y.src`, the set `{(φ, w) | P w = s φ}`); "`(φ, w) : w → μ_Y(φ)(w)`" is the
  statement that `s(φ, w) = w` and `t(φ, w) = μ_Y(φ, w)` in `(W, 𝐖)` (conjunct (0), for `W`
  and for `V`).
- `A_y` is "the map induced by `A`" on the fibre `P⁻¹(y)`; "is a topological linear
  isomorphism" is: there is a continuous linear equivalence `P⁻¹(y) ≃L[ℝ] Q⁻¹(F(y))` (fibres with
  the subspace topologies from `W`, `V` and the given linear structures) whose underlying map is
  `w ↦ A(w)` (conjunct (2)).  Likewise for `μ_Y(φ)`: a continuous linear equivalence
  `P⁻¹(s φ) ≃L[ℝ] P⁻¹(t φ)` whose underlying map is `w ↦ μ_Y(φ, w)`.
- "On morphisms `A(φ, w) = (F(φ), A_{s(φ)}(w))`": `A.mor (φ, w) = (F.mor φ, A.obj w)` as pairs
  (conjunct (1)).
- `μ_X(F(φ)) ∘ A_{s(φ)} = A_{t(φ)} ∘ μ_Y(φ)`: for every `φ ∈ 𝐘` and `w ∈ P⁻¹(s φ)`,
  `μ_X(F(φ), A(w)) = A(μ_Y(φ, w))` (conjunct (3)); the proof that `(F(φ), A(w))` is a morphism of
  `(V, 𝐕)` is taken as a hypothesis `hv` (it always holds, so this is no restriction).
- "`μ_Y : Y → Ban` is a functor" (my `IsBanFunctor`): every fibre `P⁻¹(y)` is Banachable (the
  project's `IsBanachable`: linearly homeomorphic to a Banach space), every `μ_Y(φ)` is a
  topological linear isomorphism as above, `μ_Y(1_y) = id` and `μ_Y(ψ ∘ γ) = μ_Y(ψ) ∘ μ_Y(γ)`
  on composable pairs (conjunct (4), for `μ_Y` and `μ_X`).
- "`y ↦ A_y` is a natural transformation `μ_Y → μ_X ∘ F`": the components are morphisms of
  `Ban` (conjunct (2)) and the naturality square is conjunct (3); no separate conjunct.
- Nothing looks false to me.
-/
namespace RoundTrip.V8_43
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}

/-- `μ : X → Ban` is a functor: Banach fibres, `μ(φ)` topological linear isomorphisms
`P⁻¹(s φ) → P⁻¹(t φ)`, `μ(1_x) = id`, `μ(ψ ∘ γ) = μ(ψ) ∘ μ(γ)`. -/
def IsBanFunctor (E : EpStrongBundle X B) : Prop :=
  (∀ x : Obj, IsBanachable (P ⁻¹' {x})) ∧
  (∀ φ : Mor, ∃ e : (P ⁻¹' {X.src φ}) ≃L[ℝ] (P ⁻¹' {X.tgt φ}),
    ∀ (w : P ⁻¹' {X.src φ}) (hw : P w.1 = X.src φ), (e w).1 = E.μ ⟨(φ, w.1), hw⟩) ∧
  (∀ (w : W) (h : P w = X.src (X.unit (P w))), E.μ ⟨(X.unit (P w), w), h⟩ = w) ∧
  (∀ (ψ γ : Mor) (w : W), X.src ψ = X.tgt γ → ∀ (h₁ : P w = X.src γ)
    (h₂ : P (E.μ ⟨(γ, w), h₁⟩) = X.src ψ) (h₃ : P w = X.src (X.comp ψ γ)),
    E.μ ⟨(X.comp ψ γ, w), h₃⟩ = E.μ ⟨(ψ, E.μ ⟨(γ, w), h₁⟩), h₂⟩)

end

/-- The structure of a (2017) proper strong bundle covering functor `A` over `F`: morphisms
`(φ, w) : w → μ(φ, w)`, `A(φ, w) = (F(φ), A(w))`, fibre maps `A_y` topological linear
isomorphisms, `μ_X(F φ) ∘ A_{s φ} = A_{t φ} ∘ μ_Y(φ)`, and `μ_Y`, `μ_X` functors to `Ban`. -/
def B : Prop :=
  ∀ (ObjY MorY : Type) [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
    [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY] (Y : EpGroupoid ObjY MorY)
    (ObjX MorX : Type) [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
    [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX] (X : EpGroupoid ObjX MorX)
    (W : Type) [TopologicalSpace W] [T2Space W] [ParacompactSpace W] (P : W → ObjY)
    [∀ y, AddCommGroup (P ⁻¹' {y})] [∀ y, Module ℝ (P ⁻¹' {y})] (BW : StrongBundle Y.PObj P)
    [ParacompactSpace (pullbackSpace P Y.src)]
    (V : Type) [TopologicalSpace V] [T2Space V] [ParacompactSpace V] (Q : V → ObjX)
    [∀ x, AddCommGroup (Q ⁻¹' {x})] [∀ x, Module ℝ (Q ⁻¹' {x})] (BV : StrongBundle X.PObj Q)
    [ParacompactSpace (pullbackSpace Q X.src)]
    (EW : EpStrongBundle Y BW) (EV : EpStrongBundle X BV) (F : EpFunctor Y X)
    (A : EpFunctor EW.toEpGroupoid EV.toEpGroupoid),
    EW.IsProperStrongBundleCovering EV F A →
      -- (0) a morphism `(φ, w)` goes from `w` to `μ(φ, w)`, in `(W, 𝐖)` and in `(V, 𝐕)`
      ((∀ m : pullbackSpace P Y.src,
          EW.toEpGroupoid.src m = m.1.2 ∧ EW.toEpGroupoid.tgt m = EW.μ m) ∧
        (∀ m : pullbackSpace Q X.src,
          EV.toEpGroupoid.src m = m.1.2 ∧ EV.toEpGroupoid.tgt m = EV.μ m)) ∧
      -- (1) `A(φ, w) = (F(φ), A(w))`
      (∀ m : pullbackSpace P Y.src, (A.mor m).1 = (F.mor m.1.1, A.obj m.1.2)) ∧
      -- (2) `A_y : P⁻¹(y) → Q⁻¹(F(y))` is a topological linear isomorphism
      (∀ y : ObjY, ∃ e : (P ⁻¹' {y}) ≃L[ℝ] (Q ⁻¹' {F.obj y}),
        ∀ w : P ⁻¹' {y}, (e w).1 = A.obj w.1) ∧
      -- (3) `μ_X(F(φ)) ∘ A_{s(φ)} = A_{t(φ)} ∘ μ_Y(φ)`
      (∀ (φ : MorY) (w : W) (hw : P w = Y.src φ) (hv : Q (A.obj w) = X.src (F.mor φ)),
        EV.μ ⟨(F.mor φ, A.obj w), hv⟩ = A.obj (EW.μ ⟨(φ, w), hw⟩)) ∧
      -- (4) `μ_Y : Y → Ban` and `μ_X : X → Ban` are functors
      IsBanFunctor EW ∧ IsBanFunctor EV

end RoundTrip.V8_43
