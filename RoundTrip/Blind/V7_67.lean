import Polyfold
/-! Blind formalization of V7_67 (the 2017 book's Part II, §7.5.2, the proof of Theorem 7.4,
pp. 255–256).

Text (claims of the proof): `(|U_λ|)` is an open covering of `|X|`; every `x` has an open `V(x)`
with (1) an open `W(x)` with the natural `G_x`-action, `V(x) ⊆ cl V(x) ⊆ W(x)`, `V(x)` invariant,
(2) `t : s⁻¹(cl V(x)) → X` proper, (3) `V(x) ⊆ U_λ` for some `λ`,
(4) `(π⁻¹(|V(x)|) ∖ V(x)) ∩ W(x) = ∅`; there is a locally finite refinement `(V'_i)` of
`(|V(x)|)` with `V'_i ⊆ |V(x_i)|` and open `V''_i`, `cl V''_i ⊆ V'_i`, covering `|X|`;
`U''_i = V(x_i) ∩ π⁻¹(V''_i)` is invariant with saturation `π⁻¹(V''_i)`; for a continuous
partition of unity `(β_i)` subordinate to `(V''_i)`, `(β_i ∘ π)|V(x_i)` has support in `U''_i`;
there is (Lemma 7.10) an sc-smooth invariant `f_i ≥ (β_i ∘ π)|V(x_i)` supported in `V(x_i)`;
its extension `h_i` (to the saturation of `V(x_i)`, by `0` outside) is compatible with
morphisms; `Σ h_i` is locally finite and `> 0`; `(h_i / h)` is the desired partition of unity.

Choices:
- Setting: `Obj Mor : Type` (universe 0, as in the other blind files), with the instances of the
  project's `EpGroupoid`, `X : EpGroupoid Obj Mor` (Definition 7.3, fields read with `#print`, as
  in `RoundTrip/Blind/V7_49.lean`); `|X| = X.OrbitSpace` (quotient topology, `#synth`), `π = X.π`;
  `G_x = X.Isotropy x`.  Hypotheses of Theorem 7.4 (item V7_65): `ParacompactSpace X.OrbitSpace`,
  `X.PObj.AdmitsScPartitionsOfUnity` (Definition 5.28, `#print`, item V5_47), a cover
  `U : Λ → Set Obj` (`Λ : Type`) by open saturated sets (`IsSatB`: `π⁻¹(π(U)) = U`).
- Natural action (`IsNatActionB`): the clauses of `RoundTrip/Blind/V7_62.lean` (Theorem 7.1,
  not the project's `NaturalRep`, which asks connectedness).  Invariance of a set: `Φ(g)` maps
  it into itself.  Properness (2): the project's `X.IsProperSubset (cl V(x))` (`#print`: Mathlib's
  `IsProperMap` of `t : s⁻¹(cl V(x)) → X`; item V7_59).  `|A| = π(A)`.
- "Partition of unity of the ep-groupoid" (`IsEpScPOUB`): Definition 7.16 as in
  `RoundTrip/Blind/V7_65.lean`.  `supp = tsupport`; sc-smooth = `IsScSmoothMap realPolyfold`.
- Shape of B (a conjunction): what the proof says HOLDS is claimed for EVERY choice of the
  earlier data (the `V(x), W(x)` with (1)–(4) as functions of `x`; any refinement data
  `I : Type`, `x_i`, `V'_i`, `V''_i`; any subordinate `β`); what the proof says to TAKE is
  claimed to exist (the `V(x)`; the refinement; `β`; the `f_i` together with `h_i`).
- The `f_i` / `h_i` step is existential: there are `f_i` with the stated properties (sc-smooth,
  `≥ 0`, `supp ⊆ V(x_i)`, invariant on `V(x_i)`, `≥ (β_i ∘ π)|V(x_i)`, read as the function
  `1_{V(x_i)} · (β_i ∘ π)` on `X`) whose extensions `h_i` (`h_i = f_i` on `V(x_i)`, `0` off
  `π⁻¹(π(V(x_i)))`, `h_i(s φ) = h_i(t φ)`; such `h_i` exist, which is the well-definedness claim)
  are sc-smooth, with locally finite supports (Mathlib's `LocallyFinite`; for these saturated
  supports the same as the saturated-neighbourhood version), `Σ h_i > 0` everywhere, `(h_i / h)` an
  sc-smooth partition of unity of `X` with every `supp(h_i / h)` in some `U_λ` (the refinement
  `i ↦ λ`; the re-indexing to `Λ` is Theorem 7.4 itself, item V7_65).  DOUBT: as I read it, for an
  ARBITRARY `f_i` with only `supp f_i ⊆ V(x_i)` the local finiteness of `(h_i)` need not hold; it
  holds for the `f_i` of the construction of Lemma 7.10 (support in `cl U''_i`, so
  `π(supp f_i) ⊆ V'_i`).  Hence the existential reading.  Also, `x_i ∈ U''_i` (needed to apply
  Lemma 7.10 literally with `U(x) = U''_i`) is not given; the construction does not need it.
- Nothing else looks false to me (`|X|` is Hausdorff by Definition 7.3 (3), so it is normal, which
  the refinement and `β` use).
-/
namespace RoundTrip.V7_67
open Polyfold

section
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- `U ⊆ X` is saturated: `π⁻¹(π(U)) = U`. -/
def IsSatB (X : EpGroupoid Obj Mor) (U : Set Obj) : Prop :=
  X.π ⁻¹' (X.π '' U) = U

/-- **The natural `G_x`-action on `U`** (Theorem 7.1), as in `RoundTrip/Blind/V7_62.lean`. -/
def IsNatActionB (X : EpGroupoid Obj Mor) (x : Obj) (U : Set Obj)
    (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor) : Prop :=
  IsOpen U ∧ x ∈ U ∧
  (∀ g, ∃ ψ : Obj → Obj, X.PObj.IsScDiffeoOn X.PObj (Φ g) ψ U U) ∧
  (∀ g h, ∀ y ∈ U, Φ (g * h) y = Φ g (Φ h y)) ∧
  (∀ g, X.PObj.IsScSmoothOn X.PMor (Γ g) U) ∧
  (∀ g, Γ g x = g.val) ∧
  (∀ g, ∀ y ∈ U, X.src (Γ g y) = y ∧ X.tgt (Γ g y) = Φ g y) ∧
  (∀ h : Mor, X.src h ∈ U → X.tgt h ∈ U → ∃! g, Γ g (X.src h) = h)

/-- An sc-smooth partition of unity of the ep-groupoid `X` (Definition 7.16), as in
`RoundTrip/Blind/V7_65.lean`. -/
def IsEpScPOUB (X : EpGroupoid Obj Mor) {Λ : Type} (β : Λ → Obj → ℝ) : Prop :=
  (∀ l, X.PObj.IsScSmoothMap realPolyfold (β l)) ∧
  (∀ l y, 0 ≤ β l y) ∧
  (∀ y, ∑ᶠ l, β l y = 1) ∧
  (∀ y, ∃ W : Set Obj, IsOpen W ∧ IsSatB X W ∧ y ∈ W ∧
    {l | (W ∩ tsupport (β l)).Nonempty}.Finite) ∧
  (∀ l (φ : Mor), β l (X.src φ) = β l (X.tgt φ))

/-- `V = V(x)` with (1)–(4) of the proof, `W = W(x)` carrying the natural action `(Φ, Γ)`. -/
def IsGoodNbhdB (X : EpGroupoid Obj Mor) {Λ : Type} (U : Λ → Set Obj) (x : Obj)
    (V W : Set Obj) (Φ : X.Isotropy x → Obj → Obj) (Γ : X.Isotropy x → Obj → Mor) : Prop :=
  IsOpen V ∧ x ∈ V ∧
  -- (1)
  IsNatActionB X x W Φ Γ ∧ V ⊆ closure V ∧ closure V ⊆ W ∧ (∀ g, Set.MapsTo (Φ g) V V) ∧
  -- (2)
  X.IsProperSubset (closure V) ∧
  -- (3)
  (∃ l, V ⊆ U l) ∧
  -- (4)
  (X.π ⁻¹' (X.π '' V) \ V) ∩ W = ∅

/-- The refinement data: `(V'_i)` open, locally finite, covering, `V'_i ⊆ |V(x_i)|`; `V''_i` open,
`cl V''_i ⊆ V'_i`, covering `|X|`. -/
def IsRefinementB (X : EpGroupoid Obj Mor) (V : Obj → Set Obj) {I : Type} (xs : I → Obj)
    (V' V'' : I → Set X.OrbitSpace) : Prop :=
  (∀ i, IsOpen (V' i)) ∧ LocallyFinite V' ∧ (∀ i, V' i ⊆ X.π '' V (xs i)) ∧
  (⋃ i, V' i) = Set.univ ∧
  (∀ i, IsOpen (V'' i)) ∧ (∀ i, V'' i ⊆ closure (V'' i)) ∧ (∀ i, closure (V'' i) ⊆ V' i) ∧
  (⋃ i, V'' i) = Set.univ

end

/-- The proof of Theorem 7.4: its intermediate claims, ending with the partition of unity
`(h_i / h)` of the ep-groupoid `X` subordinate to the saturated cover. -/
def B : Prop :=
  ∀ (Obj Mor : Type) [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
    [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor),
    ParacompactSpace X.OrbitSpace → X.PObj.AdmitsScPartitionsOfUnity →
    ∀ (Λ : Type) (U : Λ → Set Obj), (∀ l, IsOpen (U l)) → (∀ l, IsSatB X (U l)) →
      ⋃ l, U l = Set.univ →
      -- `(|U_λ|)` is an open covering of `|X|`
      ((∀ l, IsOpen (X.π '' U l)) ∧ (⋃ l, X.π '' U l) = Set.univ) ∧
      -- every `x` has a `V(x)` with (1)–(4)
      (∀ x : Obj, ∃ (V W : Set Obj) (Φ : X.Isotropy x → Obj → Obj)
        (Γ : X.Isotropy x → Obj → Mor), IsGoodNbhdB X U x V W Φ Γ) ∧
      -- for every such choice:
      ∀ (V W : Obj → Set Obj) (Φ : ∀ x : Obj, X.Isotropy x → Obj → Obj)
        (Γ : ∀ x : Obj, X.Isotropy x → Obj → Mor),
        (∀ x, IsGoodNbhdB X U x (V x) (W x) (Φ x) (Γ x)) →
        -- the `|V(x)|` are open, and a shrunk locally finite refinement exists
        (∀ x, IsOpen (X.π '' V x)) ∧
        (∃ (I : Type) (xs : I → Obj) (V' V'' : I → Set X.OrbitSpace),
          IsRefinementB X V xs V' V'') ∧
        -- for every such refinement:
        ∀ (I : Type) (xs : I → Obj) (V' V'' : I → Set X.OrbitSpace),
          IsRefinementB X V xs V' V'' →
          -- `U''_i` is invariant, with saturation `π⁻¹(V''_i)`
          (∀ i, (∀ g, Set.MapsTo (Φ (xs i) g) (V (xs i) ∩ X.π ⁻¹' V'' i)
              (V (xs i) ∩ X.π ⁻¹' V'' i)) ∧
            X.π ⁻¹' (X.π '' (V (xs i) ∩ X.π ⁻¹' V'' i)) = X.π ⁻¹' V'' i) ∧
          -- a continuous partition of unity subordinate to `(V''_i)` exists
          (∃ β : PartitionOfUnity I X.OrbitSpace, β.IsSubordinate V'') ∧
          -- for every such `β`:
          ∀ β : PartitionOfUnity I X.OrbitSpace, β.IsSubordinate V'' →
            -- `(β_i ∘ π)|V(x_i)` has support in `U''_i`
            (∀ i, tsupport ((V (xs i)).indicator (fun y => β i (X.π y))) ⊆
              V (xs i) ∩ X.π ⁻¹' V'' i) ∧
            -- the `f_i`, their extensions `h_i`, and the partition of unity `(h_i / h)`
            ∃ f : I → Obj → ℝ,
              (∀ i, X.PObj.IsScSmoothMap realPolyfold (f i)) ∧ (∀ i y, 0 ≤ f i y) ∧
              (∀ i, tsupport (f i) ⊆ V (xs i)) ∧
              (∀ i g, ∀ y ∈ V (xs i), f i (Φ (xs i) g y) = f i y) ∧
              (∀ i y, (V (xs i)).indicator (fun y => β i (X.π y)) y ≤ f i y) ∧
              ∃ h : I → Obj → ℝ,
                (∀ i, ∀ y ∈ V (xs i), h i y = f i y) ∧
                (∀ i y, y ∉ X.π ⁻¹' (X.π '' V (xs i)) → h i y = 0) ∧
                (∀ i (φ : Mor), h i (X.src φ) = h i (X.tgt φ)) ∧
                (∀ i, X.PObj.IsScSmoothMap realPolyfold (h i)) ∧
                LocallyFinite (fun i => tsupport (h i)) ∧
                (∀ y, 0 < ∑ᶠ i, h i y) ∧
                IsEpScPOUB X (fun i y => h i y / ∑ᶠ j, h j y) ∧
                ∀ i, ∃ l, tsupport (fun y => h i y / ∑ᶠ j, h j y) ⊆ U l

end RoundTrip.V7_67
