import Polyfold.Chapter9.BranchedIntegral
import Polyfold.Chapter9.GeneralCorollaries
import Polyfold.Chapter10.EquivalenceZhou

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 9, §9.5,
**Proposition 9.5.13 (2)**, p. 446 (new in the 2021 edition): the data on the reduced ep-groupoid
`X_R` induced from the data on `X`.

# The data induced on `X_R`

## The text, paraphrased

(Proof of Proposition 9.5.13 (2), pp. 447–448) Under LUC one passes to `X_R` (Section 7.2).  Both
have the same object M-polyfold; `Θ' = Θ`.  For `x ∈ X` take `U(x)` with the properness property
and the natural `G_x`-action and a local oriented branching structure representing `Θ̂` over `U(x)`;
"we can take the same local branching structure for `Θ̂'`", and `♯G_x^eff = ♯G'_x`.

## What is formalized (namespace `Polyfold.EpGroupoid`)

* **The natural `G^R_x`-action on `U(x)`** (what "the same local branching structure" needs):
  for a natural representation `R` of `G_x` on `U(x)` with the property of Definition 7.2.18
  (`NaturalRep.HasLUC`), `NaturalRep.toReduced` is a natural representation of the isotropy group
  `G^R_x = G_x/T_x` of `X_R` on the same `U(x)`: `Φ^R([g]) = Φ(g)`, `Γ^R([g], y) = [Γ(g, y)]`.
  The three facts behind it: `Φ_eq_of_reducedIsotropyHom_eq` (`T_x = ker Φ` under LUC, so `Φ`
  descends), `reducedπ_Γ_eq_of_reducedIsotropyHom_eq` (`Γ(gk, y) = Γ(g, y) ∘ Γ(k, y)` with
  `Γ(k, y) ∈ 𝐗^T`), and `reducedIsotropyHom_eq_of_reducedπ_Γ_eq` (uniqueness in (3) of Theorem
  7.1.13: `[Γ(a, y)] = [Γ(b, y)]` forces `a = bc` with `Γ(c, y) ∈ 𝐗^T`, so `Φ(c) = id` near `y`,
  and LUC gives `c ∈ T_x`).
* `HasPropernessProperty.toReduced` (the properness property passes to `X_R`),
  `TameBranchingStructure.toReduced`, `OrientedTameStructure.toReduced` (same `U`, sheets,
  weights, orientations), `OrientedTameStructure.represents_toReduced_iff`,
  `OrientedTameStructure.sheetSum_toReduced`, `card_isotropy_reduced_eq_card_effIsotropy`.
* **Tangent maps of morphisms**: `tangentMor_reducedπ` (`T[φ] = Tφ` on `T_{s φ}X`, from the
  naturality `EpFunctor.tangentMor_mor` for the reduction functor), `isMorTangentOn_of_reduced`,
  and `SheetIntegration.toReduced` (a `SheetIntegration` on `X` is one on `X_R`, with the same
  integrals).
* `grHatPush_reducedπ`, `tangentValue_reduced` (with `hasIndependentTangentSums`),
  `IsOrientation.toReduced`, `IsBranchedEpSubgroupoid.toReduced_of_paracompact` (given the
  paracompactness of `|supp Θ|` in `|X_R|`, which `ReducedIntegral.lean` supplies).

## Reading

* "The same local branching structure" is read literally: the fields of an (oriented, tame)
  local branching structure only involve the object M-polyfold, except the natural representation
  and the properness property, which are carried over as above.  The LUC enters only through the
  natural representation, as in the text (Definition 7.2.18 for the chosen `U(x)`).
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology

noncomputable section

namespace Polyfold

open MPolyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}

namespace NaturalRep

variable {x : Obj} (R : X.NaturalRep x)

/-- Under LUC, `[g] = [g']` gives `g⁻¹ g' ∈ ker Φ`. -/
theorem inv_mul_mem_kerΦ (hL : R.HasLUC) {g g' : X.Isotropy x}
    (h : X.reducedIsotropyHom x g = X.reducedIsotropyHom x g') : g⁻¹ * g' ∈ R.kerΦ := by
  rw [R.kerΦ_eq_trivialSubgroup hL, ← X.ker_reducedIsotropyHom x, MonoidHom.mem_ker, map_mul,
    map_inv, h, inv_mul_cancel]

/-- **`Φ` descends to `G_x/T_x`** (LUC: `T_x = ker Φ`). -/
theorem Φ_eq_of_reducedIsotropyHom_eq (hL : R.HasLUC) {g g' : X.Isotropy x}
    (h : X.reducedIsotropyHom x g = X.reducedIsotropyHom x g') {y : Obj} (hy : y ∈ R.U) :
    R.Φ g y = R.Φ g' y := by
  have hk := R.mem_kerΦ.1 (R.inv_mul_mem_kerΦ hL h) y hy
  calc R.Φ g y = R.Φ g (R.Φ (g⁻¹ * g') y) := by rw [hk]
    _ = R.Φ (g * (g⁻¹ * g')) y := (R.Φ_mul _ _ y hy).symm
    _ = R.Φ g' y := by rw [mul_inv_cancel_left]

/-- **`[Γ(g, y)]` only depends on `[g]`**: `Γ(g k, y) = Γ(g, y) ∘ Γ(k, y)` with `Γ(k, y) ∈ 𝐗^T`
for `k ∈ T_x = ker Φ`. -/
theorem reducedπ_Γ_eq_of_reducedIsotropyHom_eq (hL : R.HasLUC) {g g' : X.Isotropy x}
    (h : X.reducedIsotropyHom x g = X.reducedIsotropyHom x g') {y : Obj} (hy : y ∈ R.U) :
    X.reducedπ (R.Γ g' y) = X.reducedπ (R.Γ g y) := by
  set k := g⁻¹ * g' with hkdef
  have hk : ∀ z ∈ R.U, R.Φ k z = z := R.mem_kerΦ.1 (R.inv_mul_mem_kerΦ hL h)
  have hT : R.Γ k y ∈ X.nonEffectivePart :=
    R.Γ_mem_of_eventually hy (Filter.mem_of_superset (R.isOpen_U.mem_nhds hy) hk)
  have hg' : g' = g * k := by rw [hkdef, mul_inv_cancel_left]
  have he : R.Γ g' y = X.comp (R.Γ g y) (R.Γ k y) := by
    rw [hg', ← R.Γ_mul g k hy, hk y hy]
  refine X.reducedπ_eq_iff.2 (reducedRel_iff.2 ⟨R.Γ k y, hT, ?_, he⟩)
  rw [R.src_Γ g y hy, R.tgt_Γ k y hy, hk y hy]

/-- **Uniqueness in (3) of Theorem 7.1.13 for `X_R`**: under LUC, `[Γ(a, y)] = [Γ(b, y)]` gives
`[a] = [b]`.  Write `Γ(a, y) = Γ(b, y) ∘ k` with `k ∈ 𝐗^T`, `k = Γ(c, y)`; then `a = bc` and
`Φ(c) = id` near `y`, so on `U(x)` by LUC, i.e. `c ∈ T_x`. -/
theorem reducedIsotropyHom_eq_of_reducedπ_Γ_eq (hL : R.HasLUC) {a b : X.Isotropy x} {y : Obj}
    (hy : y ∈ R.U) (h : X.reducedπ (R.Γ a y) = X.reducedπ (R.Γ b y)) :
    X.reducedIsotropyHom x a = X.reducedIsotropyHom x b := by
  obtain ⟨k, hk, hc, he⟩ := reducedRel_iff.1 (X.reducedπ_eq_iff.1 h)
  have hks : X.src k = y := by
    have h1 := X.src_comp _ _ hc
    rw [← he, R.src_Γ a y hy] at h1
    exact h1.symm
  have hkt : X.tgt k = y := by rw [← hc, R.src_Γ b y hy]
  obtain ⟨c, hc', -⟩ := R.existsUnique_Γ k (by rw [hks]; exact hy) (by rw [hkt]; exact hy)
  rw [hks] at hc'
  have hΦc : R.Φ c y = y := by rw [← R.tgt_Γ c y hy, hc', hkt]
  have hab : a = b * c := by
    obtain ⟨g, -, hu⟩ := R.existsUnique_Γ (R.Γ a y) (by rw [R.src_Γ a y hy]; exact hy)
      (by rw [R.tgt_Γ a y hy]; exact R.mapsTo_Φ a hy)
    have h1 : R.Γ a (X.src (R.Γ a y)) = R.Γ a y := by rw [R.src_Γ a y hy]
    have h2 : R.Γ (b * c) (X.src (R.Γ a y)) = R.Γ a y := by
      rw [R.src_Γ a y hy, ← R.Γ_mul b c hy, hΦc, hc', ← he]
    exact (hu a h1).trans (hu _ h2).symm
  have hcT : R.Γ c y ∈ X.nonEffectivePart := hc' ▸ hk
  obtain ⟨D, hDs, hDo, hyD⟩ := mem_nhds_iff.1 (R.eventually_Φ_eq_of_Γ_mem hy hcT)
  have hcK : c ∈ R.kerΦ := R.mem_kerΦ.2 (hL c D hDo ⟨y, hyD⟩ (fun z hz => (hDs hz).1)
    fun z hz => (hDs hz).2)
  rw [R.kerΦ_eq_trivialSubgroup hL, ← X.ker_reducedIsotropyHom x, MonoidHom.mem_ker] at hcK
  rw [hab, map_mul, hcK, mul_one]

end NaturalRep

variable [T2Space X.ReducedMor]

variable (X) in
/-- `g ↦ [g]`, `G_x → G^R_x`, with values in the isotropy group of `x` in `X_R`. -/
def reducedIsotropyHomR (x : Obj) : X.Isotropy x →* X.reducedEpGroupoid.Isotropy x :=
  X.reducedIsotropyHom x

theorem surjective_reducedIsotropyHomR (x : Obj) : Surjective (X.reducedIsotropyHomR x) :=
  X.surjective_reducedIsotropyHom x

variable (X) in
/-- A preimage `g ∈ G_x` of `τ ∈ G^R_x`. -/
def reducedLiftR (x : Obj) (τ : X.reducedEpGroupoid.Isotropy x) : X.Isotropy x :=
  surjInv (surjective_reducedIsotropyHomR (X := X) x) τ

theorem reducedIsotropyHomR_reducedLiftR (x : Obj) (τ : X.reducedEpGroupoid.Isotropy x) :
    X.reducedIsotropyHomR x (X.reducedLiftR x τ) = τ :=
  surjInv_eq _ τ

namespace NaturalRep

variable {x : Obj} (R : X.NaturalRep x)

/-- **The natural `G^R_x`-action on `U(x)`** (2021 p. 447, "we can take the same local branching
structure"; Theorem 7.1.13 for `X_R`): a natural representation `R` of `G_x` on `U(x)` with the
property of Definition 7.2.18 gives one of the isotropy group `G^R_x = G_x/T_x` of `X_R` on the
same `U(x)`, with `Φ^R([g]) = Φ(g)` and `Γ^R([g], y) = [Γ(g, y)]`. -/
def toReduced (hL : R.HasLUC) : X.reducedEpGroupoid.NaturalRep x where
  U := R.U
  isOpen_U := R.isOpen_U
  isConnected_U := R.isConnected_U
  mem_U := R.mem_U
  Φ τ := R.Φ (X.reducedLiftR x τ)
  Γ τ y := X.reducedπ (R.Γ (X.reducedLiftR x τ) y)
  isScDiffeoOn_Φ τ := by
    have hd := R.isScDiffeoOn_Φ (X.reducedLiftR x τ)
    have hh : X.reducedIsotropyHomR x (X.reducedLiftR x τ)⁻¹ =
        X.reducedIsotropyHomR x (X.reducedLiftR x τ⁻¹) := by
      rw [map_inv, reducedIsotropyHomR_reducedLiftR, reducedIsotropyHomR_reducedLiftR]
    have he : ∀ y ∈ R.U, R.Φ (X.reducedLiftR x τ)⁻¹ y = R.Φ (X.reducedLiftR x τ⁻¹) y :=
      fun y hy => R.Φ_eq_of_reducedIsotropyHom_eq hL hh hy
    refine ⟨hd.isScSmoothOn, hd.isScSmoothOn_inv.congr he, hd.mapsTo, fun y hy => ?_,
      fun y hy => ?_, fun y hy => ?_⟩
    · rw [← he y hy]; exact hd.mapsTo_inv hy
    · rw [← he _ (hd.mapsTo hy)]; exact hd.left_inv y hy
    · rw [← he y hy]; exact hd.right_inv y hy
  Φ_mul τ σ y hy := by
    rw [← R.Φ_mul _ _ y hy]
    have hh : X.reducedIsotropyHomR x (X.reducedLiftR x (τ * σ)) =
        X.reducedIsotropyHomR x (X.reducedLiftR x τ * X.reducedLiftR x σ) := by
      rw [map_mul, reducedIsotropyHomR_reducedLiftR, reducedIsotropyHomR_reducedLiftR,
        reducedIsotropyHomR_reducedLiftR]
    exact R.Φ_eq_of_reducedIsotropyHom_eq hL hh hy
  isScSmoothOn_Γ τ :=
    MPolyfold.IsScSmoothOn.comp X.isScSmoothMap_reducedπ (R.isScSmoothOn_Γ _)
      (Set.mapsTo_univ _ _)
  Γ_self τ := by
    rw [R.Γ_self]
    exact congrArg GroupoidStr.Isotropy.val (reducedIsotropyHomR_reducedLiftR x τ)
  src_Γ τ y hy := R.src_Γ _ y hy
  tgt_Γ τ y hy := R.tgt_Γ _ y hy
  existsUnique_Γ h hs ht := by
    obtain ⟨h₀, rfl⟩ := X.surjective_reducedπ h
    have hs' : X.src h₀ ∈ R.U := hs
    obtain ⟨g₀, hg₀, -⟩ := R.existsUnique_Γ h₀ hs ht
    refine ⟨X.reducedIsotropyHomR x g₀, ?_, fun τ hτ => ?_⟩
    · change X.reducedπ (R.Γ (X.reducedLiftR x (X.reducedIsotropyHomR x g₀)) (X.src h₀)) =
        X.reducedπ h₀
      rw [R.reducedπ_Γ_eq_of_reducedIsotropyHom_eq hL
        (reducedIsotropyHomR_reducedLiftR x (X.reducedIsotropyHomR x g₀)).symm hs', hg₀]
    · change X.reducedπ (R.Γ (X.reducedLiftR x τ) (X.src h₀)) = X.reducedπ h₀ at hτ
      have hτ' : X.reducedπ (R.Γ (X.reducedLiftR x τ) (X.src h₀)) =
          X.reducedπ (R.Γ g₀ (X.src h₀)) := by rw [hg₀]; exact hτ
      have h' : X.reducedIsotropyHomR x (X.reducedLiftR x τ) = X.reducedIsotropyHomR x g₀ :=
        R.reducedIsotropyHom_eq_of_reducedπ_Γ_eq hL hs' hτ'
      rwa [reducedIsotropyHomR_reducedLiftR] at h'

@[simp]
theorem toReduced_U (hL : R.HasLUC) : (R.toReduced hL).U = R.U := rfl

theorem toReduced_Φ (hL : R.HasLUC) (g : X.Isotropy x) {y : Obj} (hy : y ∈ R.U) :
    (R.toReduced hL).Φ (X.reducedIsotropyHomR x g) y = R.Φ g y :=
  R.Φ_eq_of_reducedIsotropyHom_eq hL (reducedIsotropyHomR_reducedLiftR x _) hy

end NaturalRep

/-! ### The properness property and the local branching structures -/

/-- **The properness property passes to `X_R`**: `t : s⁻¹(cl U) → X` on `𝐗^R` is the image of
the proper `t` on `s⁻¹(cl U) ⊆ 𝐗` under the continuous surjection `π` (as in
`exists_isProperMap_reduced`). -/
theorem HasPropernessProperty.toReduced {U : Set Obj} (h : X.HasPropernessProperty U) :
    X.reducedEpGroupoid.HasPropernessProperty U := by
  refine ⟨h.1, ?_⟩
  let f : X.src ⁻¹' closure U → X.reducedSrc ⁻¹' closure U := fun φ => ⟨X.reducedπ φ.1, φ.2⟩
  refine isProperMap_of_comp_of_surj (f := f)
    ((X.continuous_reducedπ.comp continuous_subtype_val).subtype_mk _)
    (X.continuous_reducedTgt.comp continuous_subtype_val) h.2 ?_
  rintro ⟨q, hq⟩
  obtain ⟨φ, rfl⟩ := X.surjective_reducedπ q
  exact ⟨⟨φ, hq⟩, rfl⟩

variable {Θ : Obj → ℚ} {x : Obj}

/-- A local branching structure of `Θ` on `X_R` is one on `X` (the converse of
`LocalBranchingStructure.toReduced`, `MeasureEffective.lean`). -/
def LocalBranchingStructure.fromReduced (B : X.reducedEpGroupoid.LocalBranchingStructure Θ x) :
    X.LocalBranchingStructure Θ x where
  U := B.U
  isOpen_U := B.isOpen_U
  mem_U := B.mem_U
  ι := B.ι
  M := B.M
  subset_U := B.subset_U
  isSmoothSubmanifold := B.isSmoothSubmanifold
  mem_M := B.mem_M
  isProperMap := B.isProperMap
  σ := B.σ
  σ_pos := B.σ_pos
  eq_sum := B.eq_sum

/-- An oriented local branching structure of `Θ` on `X` is one on `X_R`. -/
def OrientedBranchingStructure.toReduced (B : X.OrientedBranchingStructure Θ x) :
    X.reducedEpGroupoid.OrientedBranchingStructure Θ x where
  toLocalBranchingStructure := LocalBranchingStructure.toReduced X B.toLocalBranchingStructure
  dim := B.dim
  isSubmanifoldOfDim := B.isSubmanifoldOfDim
  orient := B.orient

/-- **A tame local branching structure on `X` whose `U(x)` has the property of Definition 7.2.18
is one on `X_R`** (2021 p. 447): the same `U(x)`, sheets and weights, the natural `G^R_x`-action
`NaturalRep.toReduced`, and the properness property `HasPropernessProperty.toReduced`. -/
def TameBranchingStructure.toReduced (B : X.TameBranchingStructure Θ x) (hL : B.rep.HasLUC) :
    X.reducedEpGroupoid.TameBranchingStructure Θ x where
  toLocalBranchingStructure := LocalBranchingStructure.toReduced X B.toLocalBranchingStructure
  rep := B.rep.toReduced hL
  U_eq := B.U_eq
  hasPropernessProperty := B.hasPropernessProperty.toReduced
  hasTameInducedStructure := B.hasTameInducedStructure

variable {n : ℕ}

/-- **"We can take the same local branching structure for `Θ̂'`"** (2021 p. 447): an oriented
tame structure of dimension `n` on `X` whose `U(x)` has the property of Definition 7.2.18 is one
on `X_R`, with the same `U(x)`, sheets, weights and orientations. -/
def OrientedTameStructure.toReduced (C : X.OrientedTameStructure n Θ x) (hL : C.rep.HasLUC) :
    X.reducedEpGroupoid.OrientedTameStructure n Θ x where
  toTameBranchingStructure := C.toTameBranchingStructure.toReduced hL
  isSubmanifoldOfDim := C.isSubmanifoldOfDim
  orient := C.orient

@[simp]
theorem OrientedTameStructure.toReduced_M (C : X.OrientedTameStructure n Θ x)
    (hL : C.rep.HasLUC) (i : C.ι) : (C.toReduced hL).M i = C.M i := rfl

@[simp]
theorem OrientedTameStructure.toReduced_U (C : X.OrientedTameStructure n Θ x)
    (hL : C.rep.HasLUC) : (C.toReduced hL).U = C.U := rfl

/-- The structure on `X_R` describes the same orientation `T̂Θ`. -/
theorem OrientedTameStructure.represents_toReduced_iff (C : X.OrientedTameStructure n Θ x)
    (hL : C.rep.HasLUC) (T : Obj → X.PObj.OrTangent →₀ ℚ) :
    (C.toReduced hL).Represents T ↔ C.Represents T :=
  Iff.rfl

/-- **The normalizing factor** (2021 p. 448, `♯G_x^eff = ♯G'_x`): the isotropy group of `x` in
`X_R` has the order of `G_x^eff`. -/
theorem card_isotropy_reduced_eq_card_effIsotropy (x : Obj) :
    Nat.card (X.reducedEpGroupoid.Isotropy x) = Nat.card (X.EffIsotropy x) :=
  (card_effIsotropy_eq_reduced X x).1.symm

/-! ### Tangent maps of morphisms and the integration on `X_R` -/

/-- **`T[φ] = Tφ` on `T_{s φ}X`**: the tangent map of the morphism `[φ]` of `X_R` is that of `φ`
(naturality `EpFunctor.tangentMor_mor` for the reduction functor, whose tangent on objects is the
identity). -/
theorem tangentMor_reducedπ {φ : Mor} {a : X.PObj.TangentSpace}
    (ha : X.PObj.levelVal 1 (X.PObj.tangentProj a) = X.src φ) :
    X.reducedEpGroupoid.tangentMor (X.reducedπ φ) a = X.tangentMor φ a := by
  have hφ : φ ∈ X.PMor.levelSet 1 :=
    (X.mem_levelSet_src_iff φ 1).1 (by rw [← ha]; exact MPolyfold.levelVal_mem _)
  have h := X.reductionFunctor.tangentMor_mor hφ ha
  have hid : ∀ b, X.reductionFunctor.tangent.obj b = b := fun b =>
    congrFun (MPolyfold.tangentMap_id (P := X.PObj)) b
  rwa [hid, hid] at h

/-- A local sc-diffeomorphism with the tangent maps of morphisms of `X_R` has those of morphisms
of `X`. -/
theorem isMorTangentOn_of_reduced {f f' : Obj → Obj} {U U' : Set Obj}
    (hf : X.PObj.IsScDiffeoOn X.PObj f f' U U') {N : Set Obj}
    (h : X.reducedEpGroupoid.IsMorTangentOn hf N) : X.IsMorTangentOn hf N := by
  intro w hw
  obtain ⟨q, hs, ht, hT⟩ := h w hw
  obtain ⟨φ, rfl⟩ := X.surjective_reducedπ q
  refine ⟨φ, hs, ht, fun α hα => ?_⟩
  rw [← X.tangentMor_reducedπ (hα.trans hs.symm)]
  exact hT α hα

variable {S : Set (Set Obj)} {G : SheetNullSets S} {Ω : Type*} [AddCommGroup Ω] [Module ℝ Ω]

/-- **The integration on `X_R` induced by the one on `X`** (2021 p. 446, "the data on `X_R`
induced from `(Θ̂, ω)`"): the same integrals over the same oriented sheets; the invariance under
the local sc-diffeomorphisms with the tangent maps of morphisms of `X_R` follows from that for `X`
(`isMorTangentOn_of_reduced`). -/
def SheetIntegration.toReduced (𝓘 : X.SheetIntegration G Ω) :
    X.reducedEpGroupoid.SheetIntegration G Ω where
  integ := 𝓘.integ
  integ_add := 𝓘.integ_add
  integ_smul := 𝓘.integ_smul
  lindelof := 𝓘.lindelof
  inter_mem := 𝓘.inter_mem
  isMeasIn_inter := 𝓘.isMeasIn_inter
  isNull_tangent_ne := 𝓘.isNull_tangent_ne
  isMeasIn_tangent_eq := 𝓘.isMeasIn_tangent_eq
  integ_hasSum := 𝓘.integ_hasSum
  integ_null := 𝓘.integ_null
  integ_congr := 𝓘.integ_congr
  integ_neg := 𝓘.integ_neg
  image_mem N hN _ _ _ _ hf hNU h :=
    𝓘.image_mem N hN hf hNU (isMorTangentOn_of_reduced (X := X) hf h)
  isMeasIn_image N hN _ _ _ _ hf hNU h :=
    𝓘.isMeasIn_image N hN hf hNU (isMorTangentOn_of_reduced (X := X) hf h)
  integ_image ω N hN _ o hM _ _ _ _ hf hNU h :=
    𝓘.integ_image ω N hN o hM hf hNU (isMorTangentOn_of_reduced (X := X) hf h)

@[simp]
theorem SheetIntegration.toReduced_integ (𝓘 : X.SheetIntegration G Ω) :
    𝓘.toReduced.integ = 𝓘.integ := rfl

/-- The sums `∑ σᵢ ∫_{A ∩ Mᵢ} ω|(Mᵢ, oᵢ)` on `X_R` and on `X` agree. -/
theorem OrientedTameStructure.sheetSum_toReduced (𝓘 : X.SheetIntegration G Ω)
    (C : X.OrientedTameStructure n Θ x) (hL : C.rep.HasLUC) (ω : Ω) (A : Set Obj) :
    (C.toReduced hL).sheetSum 𝓘.toReduced ω A = C.sheetSum 𝓘 ω A := rfl

/-! ### The orientation and the branched ep⁺-subgroupoid on `X_R` -/

/-- `t(L̂, [φ]) = t(L̂, φ)` on `Gr̂(s φ)`. -/
theorem grHatPush_reducedπ {φ : Mor} {w : X.PObj.OrTangent →₀ ℚ} (hw : w ∈ X.GrHat (X.src φ)) :
    X.reducedEpGroupoid.grHatPush (X.reducedπ φ) w = X.grHatPush φ w :=
  Finsupp.mapDomain_congr fun g hg => OrTangent.push_congr
    (fun α hα => X.tangentMor_reducedπ ((hw.2 g hg).1 α hα))
    fun _ hv i => (hw.2 g hg).mem_carrier hv i

/-- `TΘ` is the same on `X_R` and on `X` (by the independence of the tangent sums, 2021
Theorem 9.2.1 (1), `hasIndependentTangentSums`). -/
theorem tangentValue_reduced (Θ : Obj → ℚ) (x : Obj) :
    X.reducedEpGroupoid.tangentValue Θ x = X.tangentValue Θ x := by
  unfold tangentValue
  by_cases h : Nonempty (X.LocalBranchingStructure Θ x)
  · have h' : Nonempty (X.reducedEpGroupoid.LocalBranchingStructure Θ x) :=
      ⟨LocalBranchingStructure.toReduced X h.some⟩
    rw [dif_pos h, dif_pos h']
    exact hasIndependentTangentSums Θ x h'.some.fromReduced h.some
  · have h' : ¬ Nonempty (X.reducedEpGroupoid.LocalBranchingStructure Θ x) :=
      fun ⟨B⟩ => h ⟨B.fromReduced⟩
    rw [dif_neg h, dif_neg h']
    rfl

/-- **The orientation `T̂Θ` of `Θ` on `X` is one on `X_R`** (2021 p. 447, `Θ' = Θ`). -/
theorem IsOrientation.toReduced {T : Obj → X.PObj.OrTangent →₀ ℚ} (hT : X.IsOrientation Θ T) :
    X.reducedEpGroupoid.IsOrientation Θ T where
  mem := hT.mem
  natural q hq := by
    obtain ⟨φ, rfl⟩ := X.surjective_reducedπ q
    have hφ : X.src φ ∈ X.PObj.smoothSet := hq
    exact (grHatPush_reducedπ (hT.mem _ hφ)).trans (hT.natural φ hφ)
  lifts y hy := (hT.lifts y hy).trans (tangentValue_reduced Θ y).symm
  locallyOriented y hy := by
    obtain ⟨B, hB⟩ := hT.locallyOriented y hy
    exact ⟨B.toReduced, hB⟩

/-- **`Θ` is a branched ep⁺-subgroupoid of `X_R`** (2021 p. 447), given that `|supp Θ| ⊆ |X_R|`
is paracompact (it is homeomorphic to `|supp Θ| ⊆ |X|`, `ReducedIntegral.lean`). -/
theorem IsBranchedEpSubgroupoid.toReduced_of_paracompact (h : X.IsBranchedEpSubgroupoid Θ)
    (hp : ParacompactSpace (X.reducedEpGroupoid.orbitSupp Θ)) :
    X.reducedEpGroupoid.IsBranchedEpSubgroupoid Θ where
  nonneg := h.nonneg
  isFunctorial := (isFunctorial_reduced_iff X).2 h.isFunctorial
  support_subset := h.support_subset
  paracompactSpace_orbitSupp := hp
  localBranching y hy := ⟨LocalBranchingStructure.toReduced X (h.localBranching y hy).some⟩

end EpGroupoid

end Polyfold
