import Polyfold.Chapter17.PolyfoldConstructionExamples
import Polyfold.Chapter17.FunctorialUniformizers
import Polyfold.Chapter10.EquivalenceRefinement
import Polyfold.Chapter8.TangentLocal
import Polyfold.Chapter11.FaceIntersectionCounterexample

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, Chapter 17,
§17.1 (pp. 746–749): the compatibilities (1)–(3) of **Remark 17.1.7**, and a witness for
**Definition 17.1.8** in which some `F(α)` contains two different overlapping uniformizers.
Numbers and pages are the 2021 text's.

# Overlapping uniformizers

## The text, paraphrased

(Remark 17.1.7, p. 747) In many cases the constructions `(φ, Ψ) ↦ σ(φ,Ψ)`, `γ(φ,Ψ)`, `τ(φ,Ψ)`
satisfy (1) `σ(φ', F(φ)(Ψ)) ∘ σ(φ,Ψ) = σ(φ' ∘ φ, Ψ)`, (2) the same for `γ`, and
(3) `τ(φ', F(φ)(Ψ))(σ(ψ,Ψ)(q)) ∘ τ(φ,Ψ)(q) = τ(φ' ∘ φ, Ψ)(q)` for `q ∈ O`.
(Definition 17.1.8, p. 747) A polyfold structure gives every transition set `M(Ψ, Ψ')`,
`Ψ ∈ F(α)`, `Ψ' ∈ F(α')`, an M-polyfold structure with (a)–(c).

## What is formalized

* **Remark 17.1.7 (1)–(3)** (namespace `Polyfold.GCT`): `Functorial.TransportSystem` (the data
  `σ, γ, τ` for every `φ` and every `Ψ ∈ F(s(φ))`), the conditions `CompatibleSigma` (1),
  `CompatibleGamma` (2), `CompatibleTau` (3) and `Compatible`;
  `LocalUniformizer.TransportData.comp` (the composite of transport data, whose square commutes);
  **`remark_17_1_7_compatible_iff`**: (1)–(3) hold iff `(σ, γ, τ)(φ' ∘ φ, Ψ)` is the composite of
  `(σ, γ, τ)(φ, Ψ)` and `(σ, γ, τ)(φ', F(φ)(Ψ))`.  Witnesses on `ℤ/2 ⋉ ℝ`:
  `reflectionTransportSystem_compatible` (`σ(φ, Ψ₀) = k ∗ ·` for `φ = (k, x)`) and
  `not_compatibleSigma_reflectionConst` (`σ ≡ −·` is transport data for every `φ` but violates (1)).
* **Polyfold structures from slices** (namespace `Polyfold.GCT.PolyfoldConstruction`): for a
  translation GCT `K ⋉ U`, a `TranslationSlice` is an open `V ⊆ U` with a subgroup `H ≤ K`
  preserving `V` such that `k ∗ v ∈ V` (`v ∈ V`) forces `k ∈ H`; its uniformizer
  `TranslationSlice.unif : H ⋉ V → K ⋉ U` is the inclusion (a local uniformizer, Definition
  17.1.3).  `MorTr L L'` is `M(L, L')` with the topology induced by `mor : M(L, L') → K × U`, and
  `morTrM` the M-polyfold structure of the open subset `mor(M(L, L'))` of `K × U` transported
  along `mor`; `isLocalScDiffeo_mor`, `isScSmoothOn_of_mor`.  (a)–(c) of Definition 17.1.8 for
  slices: `slice_isLocalScDiffeo_src`, `slice_isLocalScDiffeo_tgt`, `slice_isScSmoothMap_unit`,
  `morTr_isScSmoothMap_inv`, `slice_isScSmoothMap_mul`.  For a set `𝒟` of slices any two of which
  overlap up to `K` (`Overlapping`), `sliceConstruction` (`F(x) = {Ψ_D | x ∈ V_D}`) is a polyfold
  structure, with `sliceConstruction_hasUniformizers` (if the slices cover `U`),
  `sliceConstruction_isTame`, `sliceConstruction_isEmbedding_mor`,
  `sliceConstruction_continuous_hat` (so `lemma_17_1_9_of_continuous` applies).
* **The witness** `overlapConstruction` on `ℤ/2 ⋉ ℝ`: the slices `ℝ` (group `ℤ/2`), `(−2, 2)`
  (group `ℤ/2`, centred at `0`) and `(1, 3)` (trivial group), with uniformizers `overlapUnif₀`,
  `overlapUnif₁`, `overlapUnif₂`; `overlapConstruction_hasUniformizers`,
  `overlapConstruction_hasCoveringUniformizers`, `overlapConstruction_isTame`,
  `overlapCoveringFamily` (`Ψ₀, Ψ₁, Ψ₂`); `overlap_two_uniformizers` (`Ψ₁, Ψ₂ ∈ F(3/2)`, with images
  `(−2, 2)` and `(1, 3)`, groups `ℤ/2` acting non-trivially and trivial, so `Ψ₁ ≠ Ψ₂`);
  `overlap_transition_nonempty` (`M(Ψ₁, Ψ₂)` contains `(3/2, 1, 3/2)` and
  `(−3/2, (−1, −3/2), 3/2)`, and `0 ∈ O₁` is not a source).

## Readings

* (1)–(3) compare maps into the objects of `F(φ')(F(φ)(Ψ))` and of `F(φ' ∘ φ)(Ψ)`; these
  uniformizers are equal by the functoriality of `F` (`Functorial.map_comp`), and we identify them
  along that equality (`TransportData.castTarget`).  `τ` takes values in `mor(C)`, so (3) needs no
  identification.  In (3) we read `σ(ψ,Ψ)` as `σ(φ,Ψ)`.
* The topology of `M(Ψ, Ψ')` in `sliceConstruction` is the one induced from the morphism space
  `K × U` of the ep-groupoid `K ⋉ U`; `Overlapping` is a condition of this construction (Part I's
  open-subset structure `restrictOpen` is for non-empty open subsets), not of the text.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace GCT

/-! ### Remark 17.1.7: the compatibilities (1)–(3) -/

namespace LocalUniformizer

namespace TransportData

variable {C : GCT.{u}} {Ψ Ψ' Ψ'' : C.LocalUniformizer}

/-- **The composite of transport data** `Ψ → Ψ' → Ψ''`: `γ = γ' ∘ γ`, `σ = σ' ∘ σ`,
`τ(q) = τ'(σ(q)) ∘ τ(q)` (the right-hand sides of (1)–(3) of Remark 17.1.7). -/
def comp (D' : TransportData Ψ' Ψ'') (D : TransportData Ψ Ψ') : TransportData Ψ Ψ'' where
  γ := D.γ.trans D'.γ
  σ := D'.σ ∘ D.σ
  σInv := D.σInv ∘ D'.σInv
  isScDiffeoOn_σ := D'.isScDiffeoOn_σ.comp D.isScDiffeoOn_σ
  σ_smul g q := by
    change D'.σ (D.σ (g • q)) = D'.γ (D.γ g) • D'.σ (D.σ q)
    rw [D.σ_smul, D'.σ_smul]
  τ q := C.toGroupoidStr.comp (D'.τ (D.σ q)) (D.τ q)
  src_τ q := by
    rw [C.toGroupoidStr.src_comp _ _ (by rw [D'.src_τ, D.tgt_τ]), D.src_τ]
  tgt_τ q := by
    rw [C.toGroupoidStr.tgt_comp _ _ (by rw [D'.src_τ, D.tgt_τ]), D'.tgt_τ]
    rfl
  natural g q := by
    set G := C.toGroupoidStr
    have e1 : G.src (D.τ (g • q)) = G.tgt (Ψ.functor.mor (g, q)) := by
      rw [D.src_τ, Ψ.toUniformizer.tgt_mor]
    have e2 : G.src (D'.τ (D.σ (g • q))) = G.tgt (D.τ (g • q)) := by rw [D'.src_τ, D.tgt_τ]
    have e3 : G.src (D'.τ (D.σ q)) = G.tgt (D.τ q) := by rw [D'.src_τ, D.tgt_τ]
    have e4 : G.src (Ψ'.functor.mor (D.γ g, D.σ q)) = G.tgt (D.τ q) := by
      rw [Ψ'.toUniformizer.src_mor, D.tgt_τ]
    have e5 : G.src (D'.τ (D.σ (g • q))) = G.tgt (Ψ'.functor.mor (D.γ g, D.σ q)) := by
      rw [D'.src_τ, Ψ'.toUniformizer.tgt_mor, D.σ_smul]
    have e6 : G.src (Ψ''.functor.mor (D'.γ (D.γ g), D'.σ (D.σ q))) = G.tgt (D'.τ (D.σ q)) := by
      rw [Ψ''.toUniformizer.src_mor, D'.tgt_τ]
    change G.comp (G.comp (D'.τ (D.σ (g • q))) (D.τ (g • q))) (Ψ.functor.mor (g, q)) =
      G.comp (Ψ''.functor.mor (D'.γ (D.γ g), D'.σ (D.σ q))) (G.comp (D'.τ (D.σ q)) (D.τ q))
    rw [G.comp_assoc _ _ _ e2 e1, D.natural, ← G.comp_assoc _ _ _ e5 e4,
      show D'.τ (D.σ (g • q)) = D'.τ (D.γ g • D.σ q) by rw [D.σ_smul], D'.natural,
      G.comp_assoc _ _ _ e6 e3]

/-- Transport data are determined by `γ`, `σ` and `τ` (`σ⁻¹` is the inverse of `σ`). -/
theorem ext_of_eq {D₁ D₂ : TransportData Ψ Ψ'} (hγ : D₁.γ = D₂.γ) (hσ : D₁.σ = D₂.σ)
    (hτ : D₁.τ = D₂.τ) : D₁ = D₂ := by
  have hσInv : D₁.σInv = D₂.σInv := funext fun y => by
    conv_lhs => rw [← D₂.isScDiffeoOn_σ.right_inv y (mem_univ y), ← hσ]
    exact D₁.isScDiffeoOn_σ.left_inv _ (mem_univ _)
  cases D₁
  cases D₂
  dsimp only at hγ hσ hτ hσInv
  subst hγ hσ hτ hσInv
  rfl

/-- Transport data `Ψ → Ψ'` as transport data `Ψ → Ψ''` along `Ψ' = Ψ''`. -/
def castTarget (h : Ψ' = Ψ'') (D : TransportData Ψ Ψ') : TransportData Ψ Ψ'' := h ▸ D

@[simp] theorem castTarget_rfl (D : TransportData Ψ Ψ') : D.castTarget rfl = D := rfl

@[simp] theorem castTarget_τ (h : Ψ' = Ψ'') (D : TransportData Ψ Ψ') :
    (D.castTarget h).τ = D.τ := by
  subst h
  rfl

end TransportData

end LocalUniformizer

namespace UniformizerConstruction

variable {C : GCT.{u}} {U : C.UniformizerConstruction}

variable (T : U.Functorial)

/-- **The data `σ(φ,Ψ)`, `γ(φ,Ψ)`, `τ(φ,Ψ)` of Remark 17.1.7 (c)**, for every morphism `φ` and
every `Ψ ∈ F(s(φ))`: transport data from `Ψ` to `F(φ)(Ψ)`. -/
structure Functorial.TransportSystem where
  /-- `(σ, γ, τ)(φ, Ψ)`. -/
  data : ∀ φ : C.Mor, ∀ Ψ ∈ U.F (C.toGroupoidStr.src φ),
    LocalUniformizer.TransportData Ψ (T.map φ Ψ)

variable {T}

theorem mem_src_comp {φ' φ : C.Mor} (hc : C.toGroupoidStr.src φ' = C.toGroupoidStr.tgt φ)
    {Ψ : C.LocalUniformizer} (hΨ : Ψ ∈ U.F (C.toGroupoidStr.src φ)) :
    Ψ ∈ U.F (C.toGroupoidStr.src (C.toGroupoidStr.comp φ' φ)) := by
  rwa [C.toGroupoidStr.src_comp _ _ hc]

theorem Functorial.map_mem_src (T : U.Functorial) {φ' φ : C.Mor}
    (hc : C.toGroupoidStr.src φ' = C.toGroupoidStr.tgt φ) {Ψ : C.LocalUniformizer}
    (hΨ : Ψ ∈ U.F (C.toGroupoidStr.src φ)) : T.map φ Ψ ∈ U.F (C.toGroupoidStr.src φ') :=
  hc ▸ T.mapsTo φ hΨ

namespace Functorial.TransportSystem

variable (Θ : T.TransportSystem)

/-- **Remark 17.1.7 (1)**: `σ(φ', F(φ)(Ψ)) ∘ σ(φ, Ψ) = σ(φ' ∘ φ, Ψ)` (the two sides are maps
into the objects of `F(φ')(F(φ)(Ψ)) = F(φ' ∘ φ)(Ψ)`, identified along the functoriality of
`F`). -/
def CompatibleSigma : Prop :=
  ∀ (φ' φ : C.Mor) (hc : C.toGroupoidStr.src φ' = C.toGroupoidStr.tgt φ) (Ψ : C.LocalUniformizer)
    (hΨ : Ψ ∈ U.F (C.toGroupoidStr.src φ)),
    (Θ.data φ' (T.map φ Ψ) (T.map_mem_src hc hΨ)).σ ∘ (Θ.data φ Ψ hΨ).σ =
      ((Θ.data (C.toGroupoidStr.comp φ' φ) Ψ (mem_src_comp hc hΨ)).castTarget
        (T.map_comp φ' φ hc Ψ hΨ)).σ

/-- **Remark 17.1.7 (2)**: `γ(φ', F(φ)(Ψ)) ∘ γ(φ, Ψ) = γ(φ' ∘ φ, Ψ)`. -/
def CompatibleGamma : Prop :=
  ∀ (φ' φ : C.Mor) (hc : C.toGroupoidStr.src φ' = C.toGroupoidStr.tgt φ) (Ψ : C.LocalUniformizer)
    (hΨ : Ψ ∈ U.F (C.toGroupoidStr.src φ)),
    (Θ.data φ Ψ hΨ).γ.trans (Θ.data φ' (T.map φ Ψ) (T.map_mem_src hc hΨ)).γ =
      ((Θ.data (C.toGroupoidStr.comp φ' φ) Ψ (mem_src_comp hc hΨ)).castTarget
        (T.map_comp φ' φ hc Ψ hΨ)).γ

/-- **Remark 17.1.7 (3)** (with `σ(ψ,Ψ)` read as `σ(φ,Ψ)`):
`τ(φ', F(φ)(Ψ))(σ(φ, Ψ)(q)) ∘ τ(φ, Ψ)(q) = τ(φ' ∘ φ, Ψ)(q)` for `q ∈ O`. -/
def CompatibleTau : Prop :=
  ∀ (φ' φ : C.Mor) (hc : C.toGroupoidStr.src φ' = C.toGroupoidStr.tgt φ) (Ψ : C.LocalUniformizer)
    (hΨ : Ψ ∈ U.F (C.toGroupoidStr.src φ)) (q : Ψ.O),
    C.toGroupoidStr.comp ((Θ.data φ' (T.map φ Ψ) (T.map_mem_src hc hΨ)).τ
      ((Θ.data φ Ψ hΨ).σ q)) ((Θ.data φ Ψ hΨ).τ q) =
      (Θ.data (C.toGroupoidStr.comp φ' φ) Ψ (mem_src_comp hc hΨ)).τ q

/-- The compatibilities (1)–(3) of Remark 17.1.7. -/
def Compatible : Prop := Θ.CompatibleSigma ∧ Θ.CompatibleGamma ∧ Θ.CompatibleTau

/-- **2021 Remark 17.1.7 (1)–(3), p. 747**: the compatibilities (1)–(3) say exactly that the
transport data are functorial in `φ`: `(σ, γ, τ)(φ' ∘ φ, Ψ)` is the composite of
`(σ, γ, τ)(φ, Ψ)` and `(σ, γ, τ)(φ', F(φ)(Ψ))` (`TransportData.comp`, itself transport data:
the composite of the two commutative squares commutes). -/
theorem remark_17_1_7_compatible_iff : Θ.Compatible ↔
    ∀ (φ' φ : C.Mor) (hc : C.toGroupoidStr.src φ' = C.toGroupoidStr.tgt φ)
      (Ψ : C.LocalUniformizer) (hΨ : Ψ ∈ U.F (C.toGroupoidStr.src φ)),
      (Θ.data (C.toGroupoidStr.comp φ' φ) Ψ (mem_src_comp hc hΨ)).castTarget
          (T.map_comp φ' φ hc Ψ hΨ) =
        (Θ.data φ' (T.map φ Ψ) (T.map_mem_src hc hΨ)).comp (Θ.data φ Ψ hΨ) := by
  constructor
  · rintro ⟨h1, h2, h3⟩ φ' φ hc Ψ hΨ
    refine LocalUniformizer.TransportData.ext_of_eq (h2 φ' φ hc Ψ hΨ).symm
      (h1 φ' φ hc Ψ hΨ).symm ?_
    rw [LocalUniformizer.TransportData.castTarget_τ]
    exact funext fun q => (h3 φ' φ hc Ψ hΨ q).symm
  · intro h
    refine ⟨fun φ' φ hc Ψ hΨ => ?_, fun φ' φ hc Ψ hΨ => ?_, fun φ' φ hc Ψ hΨ q => ?_⟩
    · rw [h φ' φ hc Ψ hΨ]
      rfl
    · rw [h φ' φ hc Ψ hΨ]
      rfl
    · have := congrArg (fun D => LocalUniformizer.TransportData.τ D q) (h φ' φ hc Ψ hΨ)
      simp only [LocalUniformizer.TransportData.castTarget_τ] at this
      rw [this]
      rfl

end Functorial.TransportSystem

end UniformizerConstruction

/-! #### Witnesses on `ℤ/2 ⋉ ℝ` -/

/-- `reflectionTransport k`, as transport data `Ψ → Ψ` for `Ψ = Ψ₀`. -/
def reflectionTransportAt (k : ℤˣ) :
    ∀ Ψ : GCT.reflection.LocalUniformizer, Ψ = LocalUniformizer.reflection →
      LocalUniformizer.TransportData Ψ Ψ
  | _, rfl => LocalUniformizer.reflectionTransport k

/-- **The transport system of Remark 17.1.7 (c) on `ℤ/2 ⋉ ℝ`**: for `φ = (k, x) : x → k x`,
`σ(φ, Ψ₀) = k ∗ ·`, `γ = id`, `τ(φ, Ψ₀)(q) = (k, q)`. -/
def reflectionTransportSystem : reflectionFunctorial.TransportSystem where
  data φ Ψ hΨ := reflectionTransportAt φ.1 Ψ hΨ

/-- **The compatibilities (1)–(3) of Remark 17.1.7 hold for `reflectionTransportSystem`**
(`σ(φ', ·) ∘ σ(φ, ·) = (k' k) ∗ ·`). -/
theorem reflectionTransportSystem_compatible : reflectionTransportSystem.Compatible := by
  refine ⟨?_, ?_, ?_⟩
  · intro φ' φ hc Ψ hΨ
    obtain rfl : Ψ = LocalUniformizer.reflection := hΨ
    funext q
    exact (mul_smul φ'.1 φ.1 q).symm
  · intro φ' φ hc Ψ hΨ
    obtain rfl : Ψ = LocalUniformizer.reflection := hΨ
    exact MulEquiv.ext fun _ => rfl
  · intro φ' φ hc Ψ hΨ q
    obtain rfl : Ψ = LocalUniformizer.reflection := hΨ
    rfl

/-- The transport system with `σ(φ, Ψ₀) = −·` for every `φ` (transport data for every `φ`). -/
def reflectionConstTransportSystem : reflectionFunctorial.TransportSystem where
  data _ Ψ hΨ := reflectionTransportAt (-1) Ψ hΨ

/-- **The compatibilities of Remark 17.1.7 are a genuine condition**: for
`reflectionConstTransportSystem` (1) does not hold (`(−·) ∘ (−·) = id ≠ −·`). -/
theorem not_compatibleSigma_reflectionConst :
    ¬ reflectionConstTransportSystem.CompatibleSigma := by
  intro h
  have h1 := congrFun (h (GCT.reflection.toGroupoidStr.unit 0)
    (GCT.reflection.toGroupoidStr.unit 0) (one_smul _ _).symm LocalUniformizer.reflection rfl)
    (fun _ => 1)
  change (-1 : ℤˣ) • (-1 : ℤˣ) • (fun _ => (1 : ℝ) : Fin 1 → ℝ) =
    (-1 : ℤˣ) • (fun _ => (1 : ℝ) : Fin 1 → ℝ) at h1
  rw [EpGroupoid.Examples.units_smul_rn_neg_one, EpGroupoid.Examples.units_smul_rn_neg_one,
    neg_neg] at h1
  have := congrFun h1 0
  norm_num at this

namespace PolyfoldConstruction

section TranslationSlice

variable (K U : Type u) [Group K] [MulAction K U] [TopologicalSpace U]

/-- **A slice of the translation groupoid `K ⋉ U`**: a non-empty open `V ⊆ U` and a subgroup
`H ≤ K` preserving `V` such that `k ∗ v ∈ V` for some `v ∈ V` forces `k ∈ H` (so that the
inclusion `H ⋉ V → K ⋉ U` is full). -/
structure TranslationSlice where
  /-- The open set `V`. -/
  V : Set U
  isOpen : IsOpen V
  nonempty : V.Nonempty
  /-- The group `H`. -/
  H : Subgroup K
  smul_mem : ∀ h ∈ H, ∀ v ∈ V, h • v ∈ V
  mem_of_smul_mem : ∀ (k : K), ∀ v ∈ V, k • v ∈ V → k ∈ H

variable {K U}

instance TranslationSlice.instMulAction (D : TranslationSlice K U) : MulAction D.H D.V where
  smul h v := ⟨h.1 • v.1, D.smul_mem h.1 h.2 v.1 v.2⟩
  one_smul v := Subtype.ext (one_smul K v.1)
  mul_smul h h' v := Subtype.ext (mul_smul h.1 h'.1 v.1)

@[simp] theorem TranslationSlice.smul_val (D : TranslationSlice K U) (h : D.H) (v : D.V) :
    (h • v).1 = h.1 • v.1 := rfl

instance TranslationSlice.instNonempty (D : TranslationSlice K U) : Nonempty D.V :=
  D.nonempty.to_subtype

variable [Finite K] [TopologicalSpace K] [DiscreteTopology K] [T2Space U] [ParacompactSpace U]
  {P : MPolyfold U} (hP : ∀ k : K, P.IsScSmoothMap P fun y => k • y)

omit [Finite K] [TopologicalSpace K] [DiscreteTopology K] in
theorem TranslationSlice.paracompactSpace (Q : MPolyfold U) (D : TranslationSlice K U) :
    ParacompactSpace D.V := by
  have := Q.metrizableSpace
  exact paracompactSpace_of_metrizableSpace _

/-- The inclusion functor `H ⋉ V → K ⋉ U`. -/
def TranslationSlice.functor (D : TranslationSlice K U) :
    GroupoidFunctor (GroupoidStr.translation D.H D.V) (GroupoidStr.translation K U) where
  obj v := v.1
  mor p := (p.1.1, p.2.1)
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ _ := rfl
  mor_unit _ := rfl

omit [Finite K] [TopologicalSpace K] [DiscreteTopology K] in
include hP in
theorem TranslationSlice.isOpenEmbedding_orbitMap (D : TranslationSlice K U) :
    IsOpenEmbedding D.functor.orbitMap := by
  have hπ := GroupoidStr.isOpenMap_π_translation (EpGroupoid.Examples.action_continuous_smul hP)
  refine IsOpenEmbedding.of_continuous_injective_isOpenMap ?_ ?_ ?_
  · exact continuous_quot_lift _ (continuous_quot_mk.comp continuous_subtype_val)
  · intro z z' h
    induction z using Quotient.inductionOn with
    | h v =>
    induction z' using Quotient.inductionOn with
    | h v' =>
    obtain ⟨φ, h1, h2⟩ := (GroupoidStr.π_eq_π_iff _).1 h
    change φ.2 = v.1 at h1
    change φ.1 • φ.2 = v'.1 at h2
    have hm : φ.1 ∈ D.H := D.mem_of_smul_mem φ.1 v.1 v.2 (by rw [← h1, h2]; exact v'.2)
    exact (GroupoidStr.π_eq_π_iff _).2 ⟨(⟨φ.1, hm⟩, v), rfl, Subtype.ext (by
      change φ.1 • v.1 = v'.1
      rw [← h1, h2])⟩
  · intro W hW
    have : D.functor.orbitMap '' W = (GroupoidStr.translation K U).π ''
        (Subtype.val '' ((GroupoidStr.translation D.H D.V).π ⁻¹' W)) := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        induction w using Quotient.inductionOn with
        | h v => exact ⟨v.1, ⟨v, hw, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨_, hv, rfl⟩
    rw [this]
    exact hπ _ (D.isOpen.isOpenMap_subtype_val _ (hW.preimage continuous_quot_mk))

variable (P) in
/-- **The local uniformizer of a slice** (Definition 17.1.3): the inclusion `H ⋉ V → K ⋉ U`,
with `V` an open sub-M-polyfold of `U`. -/
def TranslationSlice.unif (D : TranslationSlice K U) : (GCT.translation K U hP).LocalUniformizer :=
  haveI := D.paracompactSpace P
  { O := D.V
    P := P.restrictOpen D.isOpen
    G := D.H
    smooth_smul := fun h => MPolyfold.isScSmoothMap_restrict D.isOpen D.isOpen (hP h.1)
      fun v => D.smul_mem h.1 h.2 v.1 v.2
    functor := D.functor
    injective_obj := Subtype.val_injective
    full := (GroupoidFunctor.full_iff _).2 fun x x' ψ hs ht => by
      change ψ.2 = x.1 at hs
      change ψ.1 • ψ.2 = x'.1 at ht
      refine ⟨(⟨ψ.1, D.mem_of_smul_mem ψ.1 x.1 x.2 ?_⟩, x), rfl, ?_, ?_⟩
      · rw [← hs, ht]
        exact x'.2
      · exact Subtype.ext (by
          change ψ.1 • x.1 = x'.1
          rw [← hs, ht])
      · exact Prod.ext rfl hs.symm
    faithful := (GroupoidFunctor.faithful_iff _).2 fun φ φ' hs _ he =>
      Prod.ext (Subtype.ext (congrArg Prod.fst he)) hs
    isOpenEmbedding_orbitMap := D.isOpenEmbedding_orbitMap hP }

/-! ### Transition sets of uniformizers of a translation GCT, topologized by `mor` -/

open EpGroupoid.Examples

variable {hP}

/-- `M(L, L')` with the topology induced by `a ↦ a.mor ∈ K × U`. -/
@[nolint unusedArguments]
def MorTr (L L' : (GCT.translation K U hP).LocalUniformizer) : Type u := L.Trans L'

variable (L L' : (GCT.translation K U hP).LocalUniformizer)

/-- The topology of `M(L, L')` induced by `mor`. -/
@[instance_reducible]
def morTrTop : TopologicalSpace (L.Trans L') :=
  TopologicalSpace.induced (fun a : L.Trans L' => a.mor) inferInstance

instance : TopologicalSpace (MorTr L L') := morTrTop L L'

theorem mor_injective : Injective fun a : L.Trans L' => a.mor := by
  intro a b h
  change a.mor = b.mor at h
  refine GroupoidStr.TransitionSet.ext (L.toUniformizer.injective_obj ?_) h
    (L'.toUniformizer.injective_obj ?_)
  · exact a.src_mor.symm.trans ((congrArg _ h).trans b.src_mor)
  · exact a.tgt_mor.symm.trans ((congrArg _ h).trans b.tgt_mor)

theorem isEmbedding_mor : IsEmbedding fun a : MorTr L L' => a.mor :=
  ⟨⟨rfl⟩, mor_injective L L'⟩

instance : T2Space (MorTr L L') := (isEmbedding_mor L L').t2Space

theorem morTr_paracompactSpace : ParacompactSpace (MorTr L L') := by
  have := (actionMorPolyfold K P).metrizableSpace
  have := (isEmbedding_mor L L').metrizableSpace
  exact paracompactSpace_of_metrizableSpace _

instance : ParacompactSpace (MorTr L L') := morTr_paracompactSpace L L'

/-- The conditions under which `M(L, L')` carries the M-polyfold structure of an open subset of
`K × U`: the image of `mor` is open and `M(L, L')` is non-empty. -/
def MorTrOpenNonempty : Prop := IsOpen (range fun a : L.Trans L' => a.mor) ∧ Nonempty (L.Trans L')

variable {L L'}

/-- `mor` as a homeomorphism onto its image. -/
def morHomeomorph : MorTr L L' ≃ₜ range fun a : L.Trans L' => a.mor :=
  (isEmbedding_mor L L').toHomeomorph

@[simp] theorem morHomeomorph_apply (a : MorTr L L') : (morHomeomorph a).1 = a.mor := rfl

theorem morHomeomorph_symm_apply (a : MorTr L L') :
    morHomeomorph.symm (⟨a.mor, mem_range_self a⟩ : range fun a : L.Trans L' => a.mor) = a :=
  (isEmbedding_mor L L').toHomeomorph_symm_apply a

/-- The M-polyfold structure of `M(L, L')`: the open subset `mor(M(L, L'))` of `K × U`,
transported along `mor`. -/
def morTrM (h : MorTrOpenNonempty L L') : MPolyfold (MorTr L L') :=
  haveI : Nonempty (range fun a : L.Trans L' => a.mor) := h.2.map fun a => ⟨a.mor, a, rfl⟩
  haveI := (actionMorPolyfold K P).paracompactSpace_subtype (range fun a : L.Trans L' => a.mor)
  ((actionMorPolyfold K P).restrictOpen h.1).transport morHomeomorph.symm

/-- `mor : M(L, L') → K × U` is a local sc-diffeomorphism. -/
theorem isLocalScDiffeo_mor (h : MorTrOpenNonempty L L') :
    (morTrM h).IsLocalScDiffeo (actionMorPolyfold K P) fun a : MorTr L L' => a.mor := by
  have : Nonempty (range fun a : L.Trans L' => a.mor) := h.2.map fun a => ⟨a.mor, a, rfl⟩
  have := (actionMorPolyfold K P).paracompactSpace_subtype (range fun a : L.Trans L' => a.mor)
  have he := (MPolyfold.isScDiffeoOn_transport ((actionMorPolyfold K P).restrictOpen h.1)
    (morHomeomorph (L := L) (L' := L')).symm).symm
  have hl : (morTrM h).IsLocalScDiffeo ((actionMorPolyfold K P).restrictOpen h.1)
      (morHomeomorph (L := L) (L' := L')) := fun _ => ⟨univ, univ, _, mem_univ _, he⟩
  exact (MPolyfold.isLocalScDiffeo_subtypeVal h.1).comp hl

theorem isScSmoothMap_mor (h : MorTrOpenNonempty L L') :
    (morTrM h).IsScSmoothMap (actionMorPolyfold K P) fun a : MorTr L L' => a.mor :=
  (isLocalScDiffeo_mor h).isScSmoothMap

theorem continuous_mor : Continuous fun a : MorTr L L' => a.mor :=
  (isEmbedding_mor L L').continuous

/-- **A map into `M(L, L')` is sc-smooth if its `mor` is sc-smooth into `K × U`.** -/
theorem isScSmoothOn_of_mor (h : MorTrOpenNonempty L L') {Z : Type u} [TopologicalSpace Z]
    [T2Space Z] [ParacompactSpace Z] {PZ : MPolyfold Z} {f : Z → MorTr L L'} {W : Set Z}
    (hf : PZ.IsScSmoothOn (actionMorPolyfold K P) (fun z => (f z).mor) W) :
    PZ.IsScSmoothOn (morTrM h) f W := by
  have : Nonempty (range fun a : L.Trans L' => a.mor) := h.2.map fun a => ⟨a.mor, a, rfl⟩
  have := (actionMorPolyfold K P).paracompactSpace_subtype (range fun a : L.Trans L' => a.mor)
  have he := MPolyfold.isScDiffeoOn_transport ((actionMorPolyfold K P).restrictOpen h.1)
    (morHomeomorph (L := L) (L' := L')).symm
  have h1 : PZ.IsScSmoothOn ((actionMorPolyfold K P).restrictOpen h.1)
      (fun z => (⟨(f z).mor, mem_range_self (f z)⟩ : range fun a : L.Trans L' => a.mor)) W :=
    (MPolyfold.isScSmoothOn_restrictOpen_iff h.1).2 hf
  exact (he.isScSmoothOn.comp h1 (mapsTo_univ _ _)).congr fun z _ => morHomeomorph_symm_apply _

/-! ### Definition 17.1.8 (a)–(c) for slice uniformizers -/

/-- **(b)**: the inversion `M(L, L') → M(L', L)` is sc-smooth. -/
theorem morTr_isScSmoothMap_inv (h : MorTrOpenNonempty L L') (h' : MorTrOpenNonempty L' L) :
    (morTrM h).IsScSmoothMap (morTrM h')
      fun a : MorTr L L' => (GroupoidStr.TransitionSet.inv a : MorTr L' L) :=
  isScSmoothOn_of_mor h' ((actionEpGroupoid hP).isScSmoothMap_inv.comp (isScSmoothMap_mor h))

variable {D D' D'' : TranslationSlice K U}

/-- **(a)**: `s : M(Ψ_D, Ψ_D') → V` is a local sc-diffeomorphism. -/
theorem slice_isLocalScDiffeo_src (h : MorTrOpenNonempty (D.unif P hP) (D'.unif P hP)) :
    (morTrM h).IsLocalScDiffeo (D.unif P hP).P
      fun a : MorTr (D.unif P hP) (D'.unif P hP) => a.src := by
  have := D.paracompactSpace P
  intro a
  have hval : (fun a : MorTr (D.unif P hP) (D'.unif P hP) => (a.src : D.V).1) =
      (GroupoidStr.translation K U).src ∘ fun a => a.mor := funext fun a => a.src_mor.symm
  have h1 : (morTrM h).IsLocalScDiffeo P
      (fun a : MorTr (D.unif P hP) (D'.unif P hP) => (a.src : D.V).1) := by
    rw [hval]
    exact action_isLocalScDiffeo_src.comp (isLocalScDiffeo_mor h)
  have hc0 : Continuous fun a : MorTr (D.unif P hP) (D'.unif P hP) => (a.src : D.V).1 := by
    rw [hval]; exact continuous_snd.comp continuous_mor
  have hc : Continuous fun a : MorTr (D.unif P hP) (D'.unif P hP) => (a.src : D.V) :=
    continuous_induced_rng.2 hc0
  exact MPolyfold.IsLocalScDiffeoAt.of_comp_left
    ((MPolyfold.isLocalScDiffeo_subtypeVal D.isOpen).at _) hc (h1.at a)

/-- **(a)**: `t : M(Ψ_D, Ψ_D') → V'` is a local sc-diffeomorphism. -/
theorem slice_isLocalScDiffeo_tgt (h : MorTrOpenNonempty (D.unif P hP) (D'.unif P hP)) :
    (morTrM h).IsLocalScDiffeo (D'.unif P hP).P
      fun a : MorTr (D.unif P hP) (D'.unif P hP) => a.tgt := by
  have := D'.paracompactSpace P
  intro a
  have hval : (fun a : MorTr (D.unif P hP) (D'.unif P hP) => (a.tgt : D'.V).1) =
      (GroupoidStr.translation K U).tgt ∘ fun a => a.mor := funext fun a => a.tgt_mor.symm
  have h1 : (morTrM h).IsLocalScDiffeo P
      (fun a : MorTr (D.unif P hP) (D'.unif P hP) => (a.tgt : D'.V).1) := by
    rw [hval]
    exact (action_isLocalScDiffeo_tgt hP).comp (isLocalScDiffeo_mor h)
  have hc0 : Continuous fun a : MorTr (D.unif P hP) (D'.unif P hP) => (a.tgt : D'.V).1 := by
    rw [hval]; exact (action_continuous_smul_prod hP).comp continuous_mor
  have hc : Continuous fun a : MorTr (D.unif P hP) (D'.unif P hP) => (a.tgt : D'.V) :=
    continuous_induced_rng.2 hc0
  exact MPolyfold.IsLocalScDiffeoAt.of_comp_left
    ((MPolyfold.isLocalScDiffeo_subtypeVal D'.isOpen).at _) hc (h1.at a)

/-- **(b)**: the unit map `V → M(Ψ_D, Ψ_D)` is sc-smooth. -/
theorem slice_isScSmoothMap_unit (h : MorTrOpenNonempty (D.unif P hP) (D.unif P hP)) :
    (D.unif P hP).P.IsScSmoothMap (morTrM h)
      fun q => (GroupoidStr.TransitionSet.unit q : MorTr (D.unif P hP) (D.unif P hP)) := by
  have := D.paracompactSpace P
  exact isScSmoothOn_of_mor h ((actionEpGroupoid hP).isScSmoothMap_unit.comp
    (MPolyfold.isScSmoothMap_subtypeVal D.isOpen))

/-- **(c)**: the multiplication `M(Ψ_D', Ψ_D'') ₛ×ₜ M(Ψ_D, Ψ_D') → M(Ψ_D, Ψ_D'')` is
sc-smooth. -/
theorem slice_isScSmoothMap_mul (h₁ : MorTrOpenNonempty (D'.unif P hP) (D''.unif P hP))
    (h₂ : MorTrOpenNonempty (D.unif P hP) (D'.unif P hP))
    (h₃ : MorTrOpenNonempty (D.unif P hP) (D''.unif P hP)) :
    MPolyfold.IsScSmoothOnFibredProduct (morTrM h₁) (morTrM h₂) (morTrM h₃)
      (slice_isLocalScDiffeo_src h₁) (slice_isLocalScDiffeo_tgt h₂).isScSmoothMap
      fun p => (GroupoidStr.TransitionSet.mul p : MorTr (D.unif P hP) (D''.unif P hP)) := by
  set X := actionEpGroupoid hP
  set PM := actionMorPolyfold K P
  set M₁ := morTrM h₁
  set M₂ := morTrM h₂
  have := D'.paracompactSpace P
  have := MPolyfold.paracompactSpace_prod M₁ M₂
  have := (M₁.prod M₂).paracompactSpace_subtype (MPolyfold.fibredProduct
    (fun a : MorTr (D'.unif P hP) (D''.unif P hP) => a.src)
    (fun a : MorTr (D.unif P hP) (D'.unif P hP) => a.tgt))
  have := MPolyfold.paracompactSpace_prod PM PM
  have := (PM.prod PM).paracompactSpace_subtype (MPolyfold.fibredProduct X.src X.tgt)
  have hA := MPolyfold.isSubMPolyfold_fibredProduct (slice_isLocalScDiffeo_src h₁)
    (slice_isLocalScDiffeo_tgt h₂).isScSmoothMap
  have hB := MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src
    X.isLocalScDiffeo_tgt.isScSmoothMap
  have hc : (MPolyfold.subPolyfold hB).IsScSmoothMap PM fun p => X.comp p.1.1 p.1.2 :=
    X.isScSmoothComp
  let Φ : MPolyfold.fibredProduct (fun a : MorTr (D'.unif P hP) (D''.unif P hP) => a.src)
      (fun a : MorTr (D.unif P hP) (D'.unif P hP) => a.tgt) →
      MPolyfold.fibredProduct X.src X.tgt :=
    fun p => ⟨(p.1.1.mor, p.1.2.mor), by
      change p.1.1.mor.2 = p.1.2.mor.1 • p.1.2.mor.2
      have h1 : p.1.1.mor.2 = (p.1.1.src : D'.V).1 := p.1.1.src_mor
      have h2 : p.1.2.mor.1 • p.1.2.mor.2 = (p.1.2.tgt : D'.V).1 := p.1.2.tgt_mor
      rw [h1, h2]
      exact congrArg Subtype.val p.2⟩
  have hval := MPolyfold.subPolyfold_inclusion_isScSmooth hA
  have hΦ : (MPolyfold.subPolyfold hA).IsScSmoothMap (MPolyfold.subPolyfold hB) Φ := by
    refine MPolyfold.isScSmoothOn_subPolyfold_of_val hB ?_
    refine MPolyfold.IsScSmoothOn.prodMk ?_ ?_
    · exact (isScSmoothMap_mor h₁).comp ((MPolyfold.isScSmoothMap_fst M₁ M₂).comp hval)
    · exact (isScSmoothMap_mor h₂).comp ((MPolyfold.isScSmoothMap_snd M₁ M₂).comp hval)
  change (MPolyfold.subPolyfold hA).IsScSmoothMap (morTrM h₃) _
  exact isScSmoothOn_of_mor h₃ (hc.comp hΦ)

/-! ### The polyfold structure of a family of slices -/

variable (P hP)

/-- The image of a slice uniformizer is its slice. -/
theorem TranslationSlice.range_obj (D : TranslationSlice K U) : range (D.unif P hP).obj = D.V :=
  Subtype.range_coe

/-- `mor(M(Ψ_D, Ψ_D')) = {(k, u) | u ∈ V, k u ∈ V'}`. -/
theorem slice_range_mor (D D' : TranslationSlice K U) :
    range (fun a : (D.unif P hP).Trans (D'.unif P hP) => a.mor) =
      {p : K × U | p.2 ∈ D.V ∧ p.1 • p.2 ∈ D'.V} := by
  ext p
  constructor
  · rintro ⟨a, rfl⟩
    have h1 : a.mor.2 = (a.src : D.V).1 := a.src_mor
    have h2 : a.mor.1 • a.mor.2 = (a.tgt : D'.V).1 := a.tgt_mor
    exact ⟨h1 ▸ (a.src : D.V).2, h2 ▸ (a.tgt : D'.V).2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨(⟨p.2, h1⟩ : D.V), p, (⟨p.1 • p.2, h2⟩ : D'.V), rfl, rfl⟩, rfl⟩

/-- `M(Ψ_D, Ψ_D')` is non-empty iff some `k ∈ K` moves a point of `V` into `V'`. -/
theorem slice_nonempty_iff (D D' : TranslationSlice K U) :
    Nonempty ((D.unif P hP).Trans (D'.unif P hP)) ↔ ∃ v ∈ D.V, ∃ k : K, k • v ∈ D'.V := by
  constructor
  · rintro ⟨a⟩
    have h := (slice_range_mor P hP D D').subset (mem_range_self a)
    exact ⟨_, h.1, _, h.2⟩
  · rintro ⟨v, hv, k, hk⟩
    exact ⟨⟨(⟨v, hv⟩ : D.V), (k, v), (⟨k • v, hk⟩ : D'.V), rfl, rfl⟩⟩

theorem slice_morTrOpenNonempty {D D' : TranslationSlice K U}
    (h : ∃ v ∈ D.V, ∃ k : K, k • v ∈ D'.V) :
    MorTrOpenNonempty (D.unif P hP) (D'.unif P hP) := by
  refine ⟨?_, (slice_nonempty_iff P hP D D').2 h⟩
  rw [slice_range_mor]
  exact (D.isOpen.preimage continuous_snd).inter
    (D'.isOpen.preimage (action_continuous_smul_prod hP))

/-- The uniformizer construction of a set `𝒟` of slices: `F(x) = {Ψ_D | D ∈ 𝒟, x ∈ V_D}`. -/
def sliceF (𝒟 : Set (TranslationSlice K U)) :
    (GCT.translation K U hP).Obj → Set (GCT.translation K U hP).LocalUniformizer :=
  fun x => {L | ∃ D ∈ 𝒟, x ∈ D.V ∧ L = D.unif P hP}

/-- Any two slices of `𝒟` overlap up to `K`: every `M(Ψ_D, Ψ_D')` is non-empty. -/
def Overlapping (𝒟 : Set (TranslationSlice K U)) : Prop :=
  ∀ D ∈ 𝒟, ∀ D' ∈ 𝒟, ∃ v ∈ D.V, ∃ k : K, k • v ∈ D'.V

variable {P hP} in
theorem exists_slice_of_unif {𝒟 : Set (TranslationSlice K U)} (Ψ : GCT.Unif (sliceF P hP 𝒟)) :
    ∃ D ∈ 𝒟, Ψ.1 = D.unif P hP := by
  obtain ⟨_, D, hD, -, h⟩ := Ψ.2
  exact ⟨D, hD, h⟩

variable {P hP} in
theorem morTrOpenNonempty_of_unif {𝒟 : Set (TranslationSlice K U)} (hov : Overlapping 𝒟)
    (Ψ Ψ' : GCT.Unif (sliceF P hP 𝒟)) : MorTrOpenNonempty Ψ.1 Ψ'.1 := by
  obtain ⟨D, hD, h⟩ := exists_slice_of_unif Ψ
  obtain ⟨D', hD', h'⟩ := exists_slice_of_unif Ψ'
  rw [h, h']
  exact slice_morTrOpenNonempty P hP (hov D hD D' hD')

/-- **A polyfold structure (Definition 17.1.8) from an overlapping set of slices** of the
translation GCT `K ⋉ U`: `F(x) = {Ψ_D | x ∈ V_D}`, and `M(Ψ_D, Ψ_D')` is the open subset
`{(k, u) | u ∈ V_D, k u ∈ V_D'}` of `K × U`, transported along `mor`. -/
def sliceConstruction (𝒟 : Set (TranslationSlice K U)) (hov : Overlapping 𝒟) :
    (GCT.translation K U hP).PolyfoldConstruction where
  F := sliceF P hP 𝒟
  isAt x L hL := by
    obtain ⟨D, -, hx, rfl⟩ := hL
    exact ⟨⟨x, hx⟩, rfl⟩
  topM Ψ Ψ' := morTrTop Ψ.1 Ψ'.1
  t2M Ψ Ψ' := (inferInstance : T2Space (MorTr Ψ.1 Ψ'.1))
  paraM Ψ Ψ' := (inferInstance : ParacompactSpace (MorTr Ψ.1 Ψ'.1))
  M Ψ Ψ' := morTrM (morTrOpenNonempty_of_unif hov Ψ Ψ')
  isLocalScDiffeo_src := by
    rintro ⟨L, α, D, hD, hα, rfl⟩ ⟨L', α', D', hD', hα', rfl⟩
    exact slice_isLocalScDiffeo_src _
  isLocalScDiffeo_tgt := by
    rintro ⟨L, α, D, hD, hα, rfl⟩ ⟨L', α', D', hD', hα', rfl⟩
    exact slice_isLocalScDiffeo_tgt _
  isScSmoothMap_unit := by
    rintro ⟨L, α, D, hD, hα, rfl⟩
    exact slice_isScSmoothMap_unit _
  isScSmoothMap_inv Ψ Ψ' := morTr_isScSmoothMap_inv _ _
  isScSmoothMap_mul := by
    rintro ⟨L, α, D, hD, hα, rfl⟩ ⟨L', α', D', hD', hα', rfl⟩ ⟨L'', α'', D'', hD'', hα'', rfl⟩
    exact slice_isScSmoothMap_mul _ _ _

variable {𝒟 : Set (TranslationSlice K U)} (hov : Overlapping 𝒟)

/-- If the slices cover `U`, every `F(x)` is non-empty. -/
theorem sliceConstruction_hasUniformizers (hcov : ∀ x : U, ∃ D ∈ 𝒟, x ∈ D.V) :
    (sliceConstruction P hP 𝒟 hov).HasUniformizers := fun x => by
  obtain ⟨D, hD, hx⟩ := hcov x
  exact ⟨D.unif P hP, D, hD, hx, rfl⟩

/-- The construction is tame if `U` is. -/
theorem sliceConstruction_isTame (hT : P.IsTame) : (sliceConstruction P hP 𝒟 hov).IsTame := by
  rintro x L ⟨D, -, -, rfl⟩
  have := D.paracompactSpace P
  exact MPolyfold.isTame_restrictOpen P D.isOpen hT

variable {P hP hov} in
/-- The topology of `M(Ψ, Ψ')` is induced by `mor : M(Ψ, Ψ') → K × U`. -/
theorem sliceConstruction_isEmbedding_mor (Ψ Ψ' : (sliceConstruction P hP 𝒟 hov).Unif) :
    IsEmbedding fun a : (sliceConstruction P hP 𝒟 hov).Tr Ψ Ψ' => a.mor :=
  isEmbedding_mor Ψ.1 Ψ'.1

variable {P hP hov} in
/-- `Ψ̂ : G × O → M(Ψ, Ψ)` is continuous, so Lemma 17.1.9 holds in the form
`lemma_17_1_9_of_continuous`. -/
theorem sliceConstruction_continuous_hat (Ψ : (sliceConstruction P hP 𝒟 hov).Unif) :
    Continuous ((sliceConstruction P hP 𝒟 hov).hat Ψ) := by
  obtain ⟨L, α, D, hD, hα, rfl⟩ := Ψ
  refine continuous_induced_rng.2 ?_
  exact (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd)

/-- `Ψ_D` as a uniformizer of the construction. -/
abbrev sliceUnif {D : TranslationSlice K U} (hD : D ∈ 𝒟) (x : U) (hx : x ∈ D.V) :
    (sliceConstruction P hP 𝒟 hov).Unif :=
  ⟨D.unif P hP, x, D, hD, hx, rfl⟩

end TranslationSlice

/-! ### The witness: two different overlapping uniformizers on `ℤ/2 ⋉ ℝ` -/

section Overlap

open EpGroupoid.Examples

/-- The slice `ℝ` with the group `ℤ/2` (the whole of `ℤ/2 ⋉ ℝ`). -/
def overlapSlice₀ : TranslationSlice ℤˣ (Fin 1 → ℝ) where
  V := univ
  isOpen := isOpen_univ
  nonempty := univ_nonempty
  H := ⊤
  smul_mem _ _ _ _ := mem_univ _
  mem_of_smul_mem k _ _ _ := Subgroup.mem_top k

/-- The slice `(−2, 2)` with the group `ℤ/2` (a uniformizer centred at `0`). -/
def overlapSlice₁ : TranslationSlice ℤˣ (Fin 1 → ℝ) where
  V := {x | |x 0| < 2}
  isOpen := isOpen_lt (continuous_apply 0).abs continuous_const
  nonempty := ⟨0, by simp⟩
  H := ⊤
  smul_mem h _ v hv := by
    rcases Int.units_eq_one_or h with rfl | rfl
    · rwa [one_smul]
    · change |((-1 : ℤˣ) • v) 0| < 2
      rw [units_smul_rn_neg_one, Pi.neg_apply, abs_neg]
      exact hv
  mem_of_smul_mem k _ _ _ := Subgroup.mem_top k

/-- The slice `(1, 3)` with the trivial group. -/
def overlapSlice₂ : TranslationSlice ℤˣ (Fin 1 → ℝ) where
  V := {x | 1 < x 0 ∧ x 0 < 3}
  isOpen := (isOpen_lt continuous_const (continuous_apply 0)).inter
    (isOpen_lt (continuous_apply 0) continuous_const)
  nonempty := ⟨fun _ => 2, by norm_num⟩
  H := ⊥
  smul_mem h hh v hv := by
    rw [Subgroup.mem_bot.1 hh, one_smul]
    exact hv
  mem_of_smul_mem k v hv hkv := by
    rcases Int.units_eq_one_or k with rfl | rfl
    · exact Subgroup.one_mem _
    · exfalso
      have h1 : 1 < ((-1 : ℤˣ) • v) 0 := hkv.1
      rw [units_smul_rn_neg_one, Pi.neg_apply] at h1
      have h2 : 1 < v 0 := hv.1
      linarith

/-- The three slices. -/
def overlapSlices : Set (TranslationSlice ℤˣ (Fin 1 → ℝ)) :=
  {overlapSlice₀, overlapSlice₁, overlapSlice₂}

/-- The common point `3/2`. -/
abbrev overlapPoint : Fin 1 → ℝ := fun _ => 3 / 2

theorem overlapPoint_mem : ∀ D ∈ overlapSlices, overlapPoint ∈ D.V := by
  intro D hD
  rcases hD with rfl | rfl | rfl
  · exact mem_univ _
  · change |(3 / 2 : ℝ)| < 2
    rw [abs_of_pos (by norm_num)]
    norm_num
  · change 1 < (3 / 2 : ℝ) ∧ (3 / 2 : ℝ) < 3
    norm_num

theorem overlapSlices_overlapping : Overlapping overlapSlices := fun D hD D' hD' =>
  ⟨overlapPoint, overlapPoint_mem D hD, 1, by rw [one_smul]; exact overlapPoint_mem D' hD'⟩

/-- **The non-degenerate witness with two different overlapping uniformizers** (Definition
17.1.8) on `ℤ/2 ⋉ ℝ`: `F(x)` consists of `Ψ₀ : ℤ/2 ⋉ ℝ → C`, of `Ψ₁ : ℤ/2 ⋉ (−2, 2) → C`
if `|x| < 2`, and of `Ψ₂ : {1} ⋉ (1, 3) → C` if `1 < x < 3` (all inclusions); `M(Ψ, Ψ')` is
the open subset of `ℤ/2 × ℝ` of the morphisms from the domain of `Ψ` to that of `Ψ'`. -/
abbrev overlapConstruction : GCT.reflection.PolyfoldConstruction :=
  sliceConstruction (rnPolyfold 1) isScSmoothMap_units_smul overlapSlices
    overlapSlices_overlapping

theorem overlapConstruction_hasUniformizers : overlapConstruction.HasUniformizers :=
  sliceConstruction_hasUniformizers _ _ _ fun _ => ⟨overlapSlice₀, Or.inl rfl, mem_univ _⟩

theorem overlapConstruction_hasCoveringUniformizers :
    overlapConstruction.HasCoveringUniformizers :=
  UniformizerConstruction.hasCoveringUniformizers_of_hasUniformizers _
    overlapConstruction_hasUniformizers

theorem overlapConstruction_isTame : overlapConstruction.IsTame :=
  sliceConstruction_isTame _ _ _ rnPolyfold_isTame

/-- `Ψ₀ : ℤ/2 ⋉ ℝ → C`, the uniformizer of the slice `ℝ` (the inclusion of `univ`). -/
abbrev overlapUnif₀ : overlapConstruction.Unif :=
  sliceUnif _ _ overlapSlices_overlapping (D := overlapSlice₀) (Or.inl rfl) overlapPoint
    (overlapPoint_mem _ (Or.inl rfl))

/-- `Ψ₁ : ℤ/2 ⋉ (−2, 2) → C`. -/
abbrev overlapUnif₁ : overlapConstruction.Unif :=
  sliceUnif _ _ overlapSlices_overlapping (D := overlapSlice₁) (Or.inr (Or.inl rfl)) overlapPoint
    (overlapPoint_mem _ (Or.inr (Or.inl rfl)))

/-- `Ψ₂ : {1} ⋉ (1, 3) → C`. -/
abbrev overlapUnif₂ : overlapConstruction.Unif :=
  sliceUnif _ _ overlapSlices_overlapping (D := overlapSlice₂) (Or.inr (Or.inr rfl)) overlapPoint
    (overlapPoint_mem _ (Or.inr (Or.inr rfl)))

/-- `Ψ₁` is centred at `0`: `0` is fixed by `G₁ = ℤ/2`. -/
theorem overlapUnif₁_isCentredAt : overlapUnif₁.1.toUniformizer.IsCentredAt (0 : Fin 1 → ℝ) :=
  ⟨⟨0, by change |(0 : ℝ)| < 2; norm_num⟩, rfl, fun g => Subtype.ext (smul_zero g.1)⟩

/-- The footprint of `Ψ₀` is `|C|`. -/
theorem overlapUnif₀_footprint : overlapUnif₀.1.footprint = univ := by
  refine eq_univ_of_forall fun z => ?_
  induction z using Quotient.inductionOn with
  | h x => exact overlapUnif₀.1.mem_footprint_iff.2 ⟨⟨x, mem_univ x⟩, rfl⟩

/-- **A covering family containing the two overlapping uniformizers** `Ψ₁, Ψ₂` (and `Ψ₀`). -/
def overlapCoveringFamily : overlapConstruction.CoveringFamily where
  ι := Fin 3
  Ψ := ![overlapUnif₀, overlapUnif₁, overlapUnif₂]
  cover := eq_univ_of_forall fun z =>
    mem_iUnion.2 ⟨0, by
      change z ∈ overlapUnif₀.1.footprint
      rw [overlapUnif₀_footprint]
      exact mem_univ z⟩

/-- **`F(3/2)` contains two different uniformizers with different domains**: `Ψ₁` and `Ψ₂` both
lie in `F(3/2)`; `Ψ₁(O₁) = (−2, 2)` and `Ψ₂(O₂) = (1, 3)`; `G₁ = ℤ/2` acts non-trivially while
`G₂` is trivial; so `Ψ₁ ≠ Ψ₂`. -/
theorem overlap_two_uniformizers :
    overlapUnif₁.1 ∈ overlapConstruction.F overlapPoint ∧
      overlapUnif₂.1 ∈ overlapConstruction.F overlapPoint ∧
      range overlapUnif₁.1.obj = {x : Fin 1 → ℝ | |x 0| < 2} ∧
      range overlapUnif₂.1.obj = {x : Fin 1 → ℝ | 1 < x 0 ∧ x 0 < 3} ∧
      (∃ (g : overlapUnif₁.1.G) (q : overlapUnif₁.1.O), g • q ≠ q) ∧
      Subsingleton overlapUnif₂.1.G ∧ overlapUnif₁.1 ≠ overlapUnif₂.1 := by
  have h1 : range overlapUnif₁.1.obj = {x : Fin 1 → ℝ | |x 0| < 2} :=
    TranslationSlice.range_obj _ _ overlapSlice₁
  have h2 : range overlapUnif₂.1.obj = {x : Fin 1 → ℝ | 1 < x 0 ∧ x 0 < 3} :=
    TranslationSlice.range_obj _ _ overlapSlice₂
  refine ⟨⟨overlapSlice₁, Or.inr (Or.inl rfl), overlapPoint_mem _ (Or.inr (Or.inl rfl)), rfl⟩,
    ⟨overlapSlice₂, Or.inr (Or.inr rfl), overlapPoint_mem _ (Or.inr (Or.inr rfl)), rfl⟩, h1, h2,
    ?_, ?_, ?_⟩
  · refine ⟨⟨-1, Subgroup.mem_top _⟩, ⟨fun _ => 1, by
      change |(1 : ℝ)| < 2
      norm_num⟩, fun h => ?_⟩
    have h' := congrArg (fun q : overlapSlice₁.V => q.1 0) h
    change ((-1 : ℤˣ) • (fun _ => (1 : ℝ) : Fin 1 → ℝ)) 0 = 1 at h'
    rw [units_smul_rn_neg_one, Pi.neg_apply] at h'
    norm_num at h'
  · exact ⟨fun g h => Subtype.ext ((Subgroup.mem_bot.1 g.2).trans (Subgroup.mem_bot.1 h.2).symm)⟩
  · intro h
    have h0 : (0 : Fin 1 → ℝ) ∈ range overlapUnif₁.1.obj := by
      rw [h1]
      change |(0 : ℝ)| < 2
      norm_num
    rw [h, h2] at h0
    have : (1 : ℝ) < 0 := h0.1
    norm_num at this

/-- **The transition set between the two different uniformizers is non-empty**, and it contains
an element over a non-identity morphism: `(−3/2, (−1, −3/2), 3/2) ∈ M(Ψ₁, Ψ₂)` and
`(3/2, 1, 3/2) ∈ M(Ψ₁, Ψ₂)`; its source map is not onto (`0` is not a source). -/
theorem overlap_transition_nonempty :
    (∃ a : overlapConstruction.Tr overlapUnif₁ overlapUnif₂,
        a.mor = ((-1 : ℤˣ), fun _ => -(3 / 2 : ℝ)) ∧ (a.tgt : overlapSlice₂.V).1 = overlapPoint) ∧
      (∃ a : overlapConstruction.Tr overlapUnif₁ overlapUnif₂,
        a.mor = GCT.reflection.toGroupoidStr.unit overlapPoint) ∧
      ∃ q : overlapUnif₁.1.O, ∀ a : overlapConstruction.Tr overlapUnif₁ overlapUnif₂,
        a.src ≠ q := by
  refine ⟨⟨⟨(⟨fun _ => -(3 / 2), ?_⟩ : overlapSlice₁.V), ((-1 : ℤˣ), fun _ => -(3 / 2 : ℝ)),
      (⟨overlapPoint, overlapPoint_mem _ (Or.inr (Or.inr rfl))⟩ : overlapSlice₂.V), rfl, ?_⟩,
      rfl, rfl⟩, ⟨⟨(⟨overlapPoint, overlapPoint_mem _ (Or.inr (Or.inl rfl))⟩ : overlapSlice₁.V),
      GCT.reflection.toGroupoidStr.unit overlapPoint,
      (⟨overlapPoint, overlapPoint_mem _ (Or.inr (Or.inr rfl))⟩ : overlapSlice₂.V), rfl,
      one_smul _ _⟩, rfl⟩, ⟨(⟨0, by change |(0 : ℝ)| < 2; norm_num⟩ : overlapSlice₁.V), ?_⟩⟩
  · change |-(3 / 2 : ℝ)| < 2
    rw [abs_neg, abs_of_pos (by norm_num)]
    norm_num
  · change (-1 : ℤˣ) • (fun _ => -(3 / 2 : ℝ) : Fin 1 → ℝ) = overlapPoint
    rw [units_smul_rn_neg_one]
    funext i
    simp
  · intro a ha
    have hs : a.mor.2 = (a.src : overlapSlice₁.V).1 := a.src_mor
    have ht : a.mor.1 • a.mor.2 = (a.tgt : overlapSlice₂.V).1 := a.tgt_mor
    rw [ha] at hs
    rw [hs, smul_zero] at ht
    have h1 : 1 < (a.tgt : overlapSlice₂.V).1 0 := (a.tgt : overlapSlice₂.V).2.1
    rw [← ht] at h1
    norm_num at h1

end Overlap

end PolyfoldConstruction

end GCT

end Polyfold
