import Polyfold.Chapter17.PolyfoldConstruction

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 746–747): **Remark 17.1.7** (functorial uniformizer constructions and the transport
data `σ, γ, τ`).  Numbers and pages are the 2021 text's.

# Functorial uniformizer constructions

## The text, paraphrased

(Remark 17.1.7) (a) A uniformizer construction is usually a recipe with set-many choices.
(b) Often `F` is a functor `C → SET`: an isomorphism `φ : α → α'` gives a bijection
`F(φ) : F(α) → F(α')`.  (c) Often, for `Ψ ∈ F(α)` and `Ψ' = F(φ)(Ψ)`, there are a group
isomorphism `γ : G → G'`, an equivariant sc-diffeomorphism `σ : O → O'` (so `σ̄ = γ ⋉ σ`), and a
natural transformation `τ : Ψ → Ψ' ∘ σ̄`; then `Ψ(q) ≅ Ψ'(σ(q))` via `τ(q)`, and `Ψ(g, q)`
corresponds to `Ψ'(σ̄(g, q))` by the commutative square.  "In many cases" (1)–(3) hold:
`σ`, `γ`, `τ` are compatible with composition in `φ`.

## What is formalized (namespace `Polyfold.GCT`)

* `UniformizerConstruction.Functorial` (**(b)**): maps `F(φ)` with `F(1_α) = id` and
  `F(φ' ∘ φ) = F(φ') ∘ F(φ)`; **`remark_17_1_7`**: each `F(φ) : F(α) → F(α')` is a bijection.
* `LocalUniformizer.TransportData` (**(c)**): `γ`, `σ` (an equivariant sc-diffeomorphism) and the
  natural transformation `τ`; `TransportData.isomorphic` (`Ψ(q) ≅ Ψ'(σ(q))`) and
  `TransportData.mor_eq` (`Ψ'(σ̄(g, q)) = τ(g ∗ q) ∘ Ψ(g, q) ∘ τ(q)⁻¹`, the square).
* Witnesses on `ℤ/2 ⋉ ℝ`: `reflectionFunctorial` (`F ≡ {Ψ₀}`, `F(φ) = id`) and, for every
  `k ∈ ℤ/2`, `reflectionTransport k` with `σ = k ∗ ·` (the reflection for `k = −1`),
  `τ(q) = (k, q)`.

## Readings

* (a) is not mathematical.  In (3) we read `σ(ψ,Ψ)` as `σ(φ,Ψ)`.  The compatibilities (1)–(3)
  are described as holding "in many cases" and are not used later in §17.1; they compare maps
  between the objects of `F(φ' ∘ φ)(Ψ)` and `F(φ')(F(φ)(Ψ))`, equal only through `F`'s
  functoriality; they are formalized in `OverlappingUniformizers.lean` (`remark_17_1_7_compatible_iff`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace GCT

variable {C : GCT.{u}}

namespace UniformizerConstruction

variable (U : C.UniformizerConstruction)

/-- **2021 Remark 17.1.7 (b), p. 746**: a **functorial** uniformizer construction: for every
morphism `φ : α → α'` a map `F(φ)` from `F(α)` to `F(α')`, with `F(1_α) = id` and
`F(φ' ∘ φ) = F(φ') ∘ F(φ)`. -/
structure Functorial where
  /-- `F(φ)`. -/
  map : C.Mor → C.LocalUniformizer → C.LocalUniformizer
  mapsTo : ∀ φ, MapsTo (map φ) (U.F (C.toGroupoidStr.src φ)) (U.F (C.toGroupoidStr.tgt φ))
  map_unit : ∀ α, ∀ Ψ ∈ U.F α, map (C.toGroupoidStr.unit α) Ψ = Ψ
  map_comp : ∀ φ' φ, C.toGroupoidStr.src φ' = C.toGroupoidStr.tgt φ →
    ∀ Ψ ∈ U.F (C.toGroupoidStr.src φ), map (C.toGroupoidStr.comp φ' φ) Ψ = map φ' (map φ Ψ)

/-- **2021 Remark 17.1.7 (b), p. 746**: for a functorial uniformizer construction every
`F(φ) : F(α) → F(α')` is a bijection (with inverse `F(φ⁻¹)`). -/
theorem remark_17_1_7 (T : U.Functorial) (φ : C.Mor) :
    BijOn (T.map φ) (U.F (C.toGroupoidStr.src φ)) (U.F (C.toGroupoidStr.tgt φ)) := by
  set G := C.toGroupoidStr
  have hmi : MapsTo (T.map (G.inv φ)) (U.F (G.tgt φ)) (U.F (G.src φ)) := by
    have := T.mapsTo (G.inv φ)
    rwa [G.src_inv, G.tgt_inv] at this
  refine InvOn.bijOn ⟨fun Ψ hΨ => ?_, fun Ψ hΨ => ?_⟩ (T.mapsTo φ) hmi
  · rw [← T.map_comp _ _ (G.src_inv φ) Ψ hΨ, G.inv_comp, T.map_unit _ Ψ hΨ]
  · have hΨ' : Ψ ∈ U.F (G.src (G.inv φ)) := by rwa [G.src_inv]
    rw [← T.map_comp _ _ (G.tgt_inv φ).symm Ψ hΨ', G.comp_inv, T.map_unit _ Ψ hΨ]

end UniformizerConstruction

namespace LocalUniformizer

/-- **2021 Remark 17.1.7 (c), p. 746**: **transport data** from `Ψ : G ⋉ O → C` to
`Ψ' : G' ⋉ O' → C`: a group isomorphism `γ : G → G'`, an equivariant sc-diffeomorphism
`σ : O → O'` (so that `σ̄ = γ ⋉ σ` is a functor), and a natural transformation
`τ : Ψ → Ψ' ∘ σ̄`. -/
structure TransportData (Ψ Ψ' : C.LocalUniformizer) where
  /-- `γ(φ,Ψ) : G → G'`. -/
  γ : Ψ.G ≃* Ψ'.G
  /-- `σ(φ,Ψ) : O → O'`. -/
  σ : Ψ.O → Ψ'.O
  /-- `σ⁻¹`. -/
  σInv : Ψ'.O → Ψ.O
  isScDiffeoOn_σ : Ψ.P.IsScDiffeoOn Ψ'.P σ σInv univ univ
  σ_smul : ∀ (g : Ψ.G) (q : Ψ.O), σ (g • q) = γ g • σ q
  /-- `τ(φ,Ψ)(q) : Ψ(q) → Ψ'(σ(q))`. -/
  τ : Ψ.O → C.Mor
  src_τ : ∀ q, C.toGroupoidStr.src (τ q) = Ψ.obj q
  tgt_τ : ∀ q, C.toGroupoidStr.tgt (τ q) = Ψ'.obj (σ q)
  /-- The square of Remark 17.1.7 commutes. -/
  natural : ∀ (g : Ψ.G) (q : Ψ.O), C.toGroupoidStr.comp (τ (g • q)) (Ψ.functor.mor (g, q)) =
    C.toGroupoidStr.comp (Ψ'.functor.mor (γ g, σ q)) (τ q)

namespace TransportData

variable {Ψ Ψ' : C.LocalUniformizer} (D : TransportData Ψ Ψ')

/-- `Ψ(q)` and `Ψ'(σ(q))` are isomorphic via `τ(q)` (Remark 17.1.7 (c)). -/
theorem isomorphic (q : Ψ.O) : C.toGroupoidStr.Isomorphic (Ψ.obj q) (Ψ'.obj (D.σ q)) :=
  ⟨D.τ q, D.src_τ q, D.tgt_τ q⟩

/-- `|Ψ(q)| = |Ψ'(σ(q))|`. -/
theorem π_obj_eq (q : Ψ.O) : C.toGroupoidStr.π (Ψ.obj q) = C.toGroupoidStr.π (Ψ'.obj (D.σ q)) :=
  (GroupoidStr.π_eq_π_iff _).2 (D.isomorphic q)

/-- **The morphism `Ψ(g, q)` corresponds to `Ψ'(σ̄(g, q))`** (Remark 17.1.7 (c), the square):
`Ψ'(γ(g), σ(q)) = τ(g ∗ q) ∘ Ψ(g, q) ∘ τ(q)⁻¹`. -/
theorem mor_eq (g : Ψ.G) (q : Ψ.O) :
    Ψ'.functor.mor (D.γ g, D.σ q) = C.toGroupoidStr.comp
      (C.toGroupoidStr.comp (D.τ (g • q)) (Ψ.functor.mor (g, q)))
      (C.toGroupoidStr.inv (D.τ q)) := by
  rw [D.natural]
  refine (GroupoidStr.comp_inv_cancel_right ?_).symm
  rw [D.tgt_τ]
  exact Ψ'.toUniformizer.src_mor (D.γ g, D.σ q)

end TransportData

/-! ### Witnesses on `ℤ/2 ⋉ ℝ` -/

open EpGroupoid.Examples

/-- **Transport data on the reflection uniformizer** for the morphism `(k, x) : x → k ∗ x`:
`γ = id`, `σ = k ∗ ·` (the reflection for `k = −1`), `τ(q) = (k, q)`. -/
def reflectionTransport (k : ℤˣ) : TransportData reflection reflection where
  γ := MulEquiv.refl _
  σ q := k • q
  σInv q := k⁻¹ • q
  isScDiffeoOn_σ :=
    { isScSmoothOn := isScSmoothMap_units_smul k
      isScSmoothOn_inv := isScSmoothMap_units_smul k⁻¹
      mapsTo := mapsTo_univ _ _
      mapsTo_inv := mapsTo_univ _ _
      left_inv := fun q _ => inv_smul_smul k q
      right_inv := fun q _ => smul_inv_smul k q }
  σ_smul g q := by
    change k • g • q = g • k • q
    rw [smul_smul, smul_smul, mul_comm]
  τ q := (k, q)
  src_τ _ := rfl
  tgt_τ _ := rfl
  natural g q := by
    change (k * g, q) = (g * k, q)
    rw [mul_comm]

/-- `σ` of `reflectionTransport (−1)` is not the identity. -/
theorem reflectionTransport_σ_ne : (reflectionTransport (-1)).σ ≠ id := by
  intro h
  have h' : -(fun _ => 1 : Fin 1 → ℝ) = fun _ => 1 :=
    (units_smul_rn_neg_one _).symm.trans (congrFun h _)
  have := congrFun h' 0
  norm_num at this

end LocalUniformizer

/-- **The functorial witness of Remark 17.1.7 (b)**: `F ≡ {Ψ₀}` on `ℤ/2 ⋉ ℝ`, `F(φ) = id`. -/
def reflectionUniformizerConstruction : GCT.reflection.UniformizerConstruction where
  F _ := {LocalUniformizer.reflection}
  isAt x Ψ hΨ := by
    rw [Set.mem_singleton_iff.1 hΨ]
    exact LocalUniformizer.tautological_isAt _ x

/-- `F(φ) = id` is functorial. -/
def reflectionFunctorial : reflectionUniformizerConstruction.Functorial where
  map _ Ψ := Ψ
  mapsTo _ _ h := h
  map_unit _ _ _ := rfl
  map_comp _ _ _ _ _ := rfl

end GCT

end Polyfold
