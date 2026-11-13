import Polyfold.Chapter7.SmoothRegularAssembly
import Polyfold.Chapter10.EquivalenceReduced

/-!
# Appendix 7.6.4: `(X^i)_R = (X_R)^i` as ep-groupoids (Theorem 7.6.7, Corollary 7.6.8)

2021 Theorem 7.6.7, p. 351 (new in the 2021 edition): under (SLUC) the natural set-theoretic
identification between `(X¹)_R` and `(X_R)¹` is an sc-diffeomorphism on the object spaces and on the
morphism spaces, and similarly for `(Xⁱ)_R` and `(X_R)ⁱ` for every `i`.  2021 Corollary 7.6.8: the
same under (ZHOU).

The project had the case `i = 1` as sets (`theorem_7_6_7_of_isLUC`, `SmoothConnectedReps.lean`):
`(𝐗^T)^1 = (𝐗^1)^T`, and `[φ]₁ ↦ [φ]` is a continuous injection `(𝐗¹)^R → 𝐗^R` onto `π(𝐗_1)`.

## What is formalized

* `reducedRaise`: the natural map `(𝐗¹)^R → (𝐗^R)¹`, `[φ]₁ ↦ [φ]`, with `reducedRaise_π`.  Here
  `(𝐗^R)¹` is the level-`1` M-polyfold of `reducedPolyfold`; `[φ]` lies on level `1` because
  `π : 𝐗 → 𝐗^R` is a local sc-diffeomorphism.
* `bijective_reducedRaise`, `isScDiffeoOn_reducedRaise`: it is an sc-diffeomorphism from the
  morphism M-polyfold of `(X¹)_R` onto that of `(X_R)¹` (the text's diagram: `π₁ : 𝐗¹ → (𝐗¹)^R`
  and the level-`1` lift of `π : 𝐗 → 𝐗^R` are local sc-diffeomorphisms, and
  `reducedRaise ∘ π₁` is that lift).
* `raiseReducedFunctor`, `raiseReducedFunctorInv`: the identity on objects and `reducedRaise`
  (resp. its inverse) on morphisms are morphisms of `EP` between `(X¹)_R` and `(X_R)¹`.
* `theorem_7_6_7_one`: **Theorem 7.6.7 for `i = 1`**, under `T_R` Hausdorff for `X` and `X¹`
  (equivalent to LUC for `X` and `X¹`, Theorem 7.2.22): the identification is the identity on
  objects, an sc-diffeomorphism on morphisms, and an isomorphism of ep-groupoids.
* `EP.reducedOfLUC`: the bundled `X_R` of an ep-groupoid with LUC; `EP.liftOneIso`: `X ≅ Y` in `EP`
  gives `X¹ ≅ Y¹`; `EP.raiseReducedIso`: `(X¹)_R ≅ (X_R)¹` in `EP`.
* `EP.theorem_7_6_7`: **Theorem 7.6.7 for every `i`**, under (SLUC): `(Xⁱ)_R ≅ (X_R)ⁱ` in `EP`
  (an isomorphism of ep-groupoids: sc-smooth functors inverse to each other, hence
  sc-diffeomorphisms on objects and on morphisms), by the text's induction
  `(Xⁱ)_R = ((X^{i-1})¹)_R = ((X^{i-1})_R)¹ = … = (X_R)ⁱ`.
* `EP.corollary_7_6_8`: **Corollary 7.6.8**: the same under (ZHOU) (which implies (SLUC),
  `EP.theorem_7_4_13_all_of_isZhou`).

## Reading

* "(SLUC)" is `EP.IsSLUC` (every `Xⁱ` has LUC).  For `i = 1` only LUC for `X` and `X¹` is used;
  it is taken in the equivalent form `T2Space X.ReducedMor`, `T2Space X.liftOne.ReducedMor`,
  which the M-polyfolds `𝐗^R`, `(𝐗¹)^R` need.
* For general `i` the statement is an isomorphism in `EP` between `(Xⁱ)_R` and `(X_R)ⁱ`.  For
  `i = 1` it is the natural identification (the identity on objects, `[φ]₁ ↦ [φ]` on morphisms,
  `theorem_7_6_7_one`); for `i ≥ 2` it is the composite of the text's identifications, built by
  recursion on `i` (`(Xⁱ)` is `EP.lift`, iterated `liftOne`).
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

section RaiseOne

variable [T2Space X.ReducedMor] [T2Space X.liftOne.ReducedMor]

set_option linter.unusedSectionVars false

/-- `(𝐗¹)^T = (𝐗^T)^1` when `T_R` of `X¹` is Hausdorff (2021 p. 350). -/
theorem nonEffectivePart_liftOne_eq_of_t2 :
    X.liftOne.nonEffectivePart = X.PMor.levelVal 1 ⁻¹' X.nonEffectivePart :=
  X.nonEffectivePart_liftOne_eq_of_isClosed X.liftOne.isClosed_nonEffectivePart_of_t2Space

/-- The level-`1` lift `𝐗¹ → (𝐗^R)¹` of `π : 𝐗 → 𝐗^R`. -/
def reducedπOne : X.PMor.Level 1 → X.reducedEpGroupoid.PMor.Level 1 :=
  MPolyfold.levelOneMap X.PMor X.reducedPolyfold X.reducedπ
    (X.isLocalScDiffeo_reducedπ.isScSmoothMap.mapsTo_levelSet 1)

@[simp]
theorem levelVal_reducedπOne (φ : X.PMor.Level 1) :
    X.reducedPolyfold.levelVal 1 (X.reducedπOne φ) = X.reducedπ (X.PMor.levelVal 1 φ) := rfl

/-- The lift `π¹` is a local sc-diffeomorphism `𝐗¹ → (𝐗^R)¹`. -/
theorem isLocalScDiffeo_reducedπOne :
    X.PMor.shift.IsLocalScDiffeo X.reducedPolyfold.shift X.reducedπOne :=
  X.isLocalScDiffeo_reducedπ.levelOne

/-- **The natural map `(𝐗¹)^R → (𝐗^R)¹`**, `[φ]₁ ↦ [φ]` (2021 p. 350). -/
def reducedRaise : X.liftOne.ReducedMor → X.reducedEpGroupoid.PMor.Level 1 :=
  Quot.lift X.reducedπOne fun _ _ h => MPolyfold.level_ext
    ((X.liftOne_reducedπ_eq_iff X.nonEffectivePart_liftOne_eq_of_t2).1 (Quot.sound h))

@[simp]
theorem reducedRaise_π (φ : X.PMor.Level 1) :
    X.reducedRaise (X.liftOne.reducedπ φ) = X.reducedπOne φ := rfl

theorem injective_reducedRaise : Injective X.reducedRaise := by
  intro a b h
  obtain ⟨φ, rfl⟩ := X.liftOne.surjective_reducedπ a
  obtain ⟨ψ, rfl⟩ := X.liftOne.surjective_reducedπ b
  exact (X.liftOne_reducedπ_eq_iff X.nonEffectivePart_liftOne_eq_of_t2).2
    (congrArg (X.reducedPolyfold.levelVal 1) h)

/-- Every point of `(𝐗^R)¹` is `π¹(φ)` for some `φ ∈ 𝐗¹`. -/
theorem surjective_reducedπOne : Surjective X.reducedπOne := by
  intro p
  obtain ⟨φ, hφ⟩ := X.surjective_reducedπ (X.reducedPolyfold.levelVal 1 p)
  have h1 : φ ∈ X.PMor.levelSet 1 :=
    (X.isLocalScDiffeo_reducedπ.mem_levelSet_iff φ 1).1 (hφ ▸ MPolyfold.levelVal_mem p)
  exact ⟨X.PMor.levelMk 1 φ h1, MPolyfold.level_ext hφ⟩

theorem surjective_reducedRaise : Surjective X.reducedRaise := fun p => by
  obtain ⟨φ, rfl⟩ := X.surjective_reducedπOne p
  exact ⟨_, X.reducedRaise_π φ⟩

theorem bijective_reducedRaise : Bijective X.reducedRaise :=
  ⟨X.injective_reducedRaise, X.surjective_reducedRaise⟩

/-- The inverse `(𝐗^R)¹ → (𝐗¹)^R`. -/
def reducedRaiseInv : X.reducedEpGroupoid.PMor.Level 1 → X.liftOne.ReducedMor :=
  (Equiv.ofBijective _ X.bijective_reducedRaise).symm

theorem reducedRaise_inv (p : X.reducedEpGroupoid.PMor.Level 1) :
    X.reducedRaise (X.reducedRaiseInv p) = p :=
  (Equiv.ofBijective _ X.bijective_reducedRaise).apply_symm_apply p

theorem reducedRaiseInv_raise (q : X.liftOne.ReducedMor) :
    X.reducedRaiseInv (X.reducedRaise q) = q :=
  (Equiv.ofBijective _ X.bijective_reducedRaise).symm_apply_apply q

theorem reducedRaiseInv_π (φ : X.PMor.Level 1) :
    X.reducedRaiseInv (X.reducedπOne φ) = X.liftOne.reducedπ φ := by
  rw [← X.reducedRaise_π, reducedRaiseInv_raise]

/-- `[φ]₁ ↦ [φ]` is sc-smooth `(𝐗¹)^R → (𝐗^R)¹`: near `π₁(φ)` it is `π¹ ∘ (π₁|U)⁻¹`. -/
theorem isScSmoothMap_reducedRaise :
    X.liftOne.reducedPolyfold.IsScSmoothMap X.reducedPolyfold.shift X.reducedRaise := by
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun q _ => ?_
  obtain ⟨φ, rfl⟩ := X.liftOne.surjective_reducedπ q
  obtain ⟨W, V, σ, hφ, hd⟩ := X.liftOne.isLocalScDiffeo_reducedπ φ
  refine ⟨V, hd.isScSmoothOn_inv.isOpen, hd.mapsTo hφ, subset_univ _, ?_⟩
  have hL : X.PMor.shift.IsScSmoothMap X.reducedPolyfold.shift X.reducedπOne :=
    X.isLocalScDiffeo_reducedπOne.isScSmoothMap
  refine (MPolyfold.IsScSmoothOn.comp hL hd.isScSmoothOn_inv (mapsTo_univ _ _)).congr
    fun q' hq' => ?_
  change X.reducedπOne (σ q') = X.reducedRaise q'
  conv_rhs => rw [← hd.right_inv q' hq']
  rfl

/-- The inverse `(𝐗^R)¹ → (𝐗¹)^R` is sc-smooth: near `π¹(φ)` it is `π₁ ∘ (π¹|U)⁻¹`. -/
theorem isScSmoothMap_reducedRaiseInv :
    X.reducedPolyfold.shift.IsScSmoothMap X.liftOne.reducedPolyfold X.reducedRaiseInv := by
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun p _ => ?_
  obtain ⟨φ, rfl⟩ := X.surjective_reducedπOne p
  obtain ⟨W, V, k, hφ, hd⟩ := X.isLocalScDiffeo_reducedπOne φ
  refine ⟨V, hd.isScSmoothOn_inv.isOpen, hd.mapsTo hφ, subset_univ _, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp X.liftOne.isScSmoothMap_reducedπ hd.isScSmoothOn_inv
    (mapsTo_univ _ _)).congr
    fun p' hp' => ?_
  change X.liftOne.reducedπ (k p') = X.reducedRaiseInv p'
  conv_rhs => rw [← hd.right_inv p' hp']
  rw [reducedRaiseInv_π]

/-- **`[φ]₁ ↦ [φ]` is an sc-diffeomorphism** from the morphism M-polyfold `(𝐗¹)^R` of `(X¹)_R` onto
the morphism M-polyfold `(𝐗^R)¹` of `(X_R)¹` (2021 p. 350, Theorem 7.6.7). -/
theorem isScDiffeoOn_reducedRaise :
    X.liftOne.reducedEpGroupoid.PMor.IsScDiffeoOn X.reducedEpGroupoid.liftOne.PMor
      X.reducedRaise X.reducedRaiseInv univ univ :=
  ⟨X.isScSmoothMap_reducedRaise, X.isScSmoothMap_reducedRaiseInv, mapsTo_univ _ _,
    mapsTo_univ _ _, fun q _ => X.reducedRaiseInv_raise q, fun p _ => X.reducedRaise_inv p⟩

theorem src_reducedRaise (q : X.liftOne.ReducedMor) :
    X.reducedEpGroupoid.liftOne.src (X.reducedRaise q) = X.liftOne.reducedEpGroupoid.src q := by
  obtain ⟨φ, rfl⟩ := X.liftOne.surjective_reducedπ q
  exact MPolyfold.level_ext rfl

theorem tgt_reducedRaise (q : X.liftOne.ReducedMor) :
    X.reducedEpGroupoid.liftOne.tgt (X.reducedRaise q) = X.liftOne.reducedEpGroupoid.tgt q := by
  obtain ⟨φ, rfl⟩ := X.liftOne.surjective_reducedπ q
  exact MPolyfold.level_ext rfl

theorem reducedRaise_unit (x : X.PObj.Level 1) :
    X.reducedRaise (X.liftOne.reducedEpGroupoid.unit x) = X.reducedEpGroupoid.liftOne.unit x :=
  MPolyfold.level_ext rfl

theorem reducedRaise_comp (a b : X.liftOne.ReducedMor)
    (h : X.liftOne.reducedEpGroupoid.src a = X.liftOne.reducedEpGroupoid.tgt b) :
    X.reducedRaise (X.liftOne.reducedEpGroupoid.comp a b) =
      X.reducedEpGroupoid.liftOne.comp (X.reducedRaise a) (X.reducedRaise b) := by
  obtain ⟨φ, rfl⟩ := X.liftOne.surjective_reducedπ a
  obtain ⟨ψ, rfl⟩ := X.liftOne.surjective_reducedπ b
  have h₁ : X.liftOne.src φ = X.liftOne.tgt ψ := h
  have h₀ : X.src (X.PMor.levelVal 1 φ) = X.tgt (X.PMor.levelVal 1 ψ) :=
    congrArg (X.PObj.levelVal 1) h₁
  have h₂ : X.reducedEpGroupoid.liftOne.src (X.reducedRaise (X.liftOne.reducedπ φ)) =
      X.reducedEpGroupoid.liftOne.tgt (X.reducedRaise (X.liftOne.reducedπ ψ)) := by
    rw [src_reducedRaise, tgt_reducedRaise]; exact h
  have e₁ : X.liftOne.reducedEpGroupoid.comp (X.liftOne.reducedπ φ) (X.liftOne.reducedπ ψ) =
      X.liftOne.reducedπ (X.liftOne.comp φ ψ) := X.liftOne.reducedComp_π h₁
  refine MPolyfold.level_ext ?_
  rw [e₁, X.reducedEpGroupoid.liftOne_comp_val h₂]
  change X.reducedπ (X.PMor.levelVal 1 (X.liftOne.comp φ ψ)) =
    X.reducedComp (X.reducedπ (X.PMor.levelVal 1 φ)) (X.reducedπ (X.PMor.levelVal 1 ψ))
  rw [X.liftOne_comp_val h₁, X.reducedComp_π h₀]

/-- **The identification `(X¹)_R → (X_R)¹`** as a morphism of `EP`: the identity on objects and
`[φ]₁ ↦ [φ]` on morphisms. -/
def raiseReducedFunctor : EpFunctor X.liftOne.reducedEpGroupoid X.reducedEpGroupoid.liftOne where
  obj := id
  mor := X.reducedRaise
  src_mor := X.src_reducedRaise
  tgt_mor := X.tgt_reducedRaise
  mor_comp := X.reducedRaise_comp
  mor_unit := X.reducedRaise_unit
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor := X.isScSmoothMap_reducedRaise

/-- **The inverse identification `(X_R)¹ → (X¹)_R`** as a morphism of `EP`. -/
def raiseReducedFunctorInv :
    EpFunctor X.reducedEpGroupoid.liftOne X.liftOne.reducedEpGroupoid where
  obj := id
  mor := X.reducedRaiseInv
  src_mor p := by
    rw [← X.src_reducedRaise, X.reducedRaise_inv]; rfl
  tgt_mor p := by
    rw [← X.tgt_reducedRaise, X.reducedRaise_inv]; rfl
  mor_comp p p' h := by
    have h' : X.liftOne.reducedEpGroupoid.src (X.reducedRaiseInv p) =
        X.liftOne.reducedEpGroupoid.tgt (X.reducedRaiseInv p') := by
      rw [← X.src_reducedRaise, ← X.tgt_reducedRaise, X.reducedRaise_inv, X.reducedRaise_inv]
      exact h
    apply X.injective_reducedRaise
    rw [X.reducedRaise_comp _ _ h', X.reducedRaise_inv, X.reducedRaise_inv, X.reducedRaise_inv]
  mor_unit x := by
    apply X.injective_reducedRaise
    rw [X.reducedRaise_inv]
    exact (X.reducedRaise_unit x).symm
  isScSmoothMap_obj := MPolyfold.isScSmoothMap_id
  isScSmoothMap_mor := X.isScSmoothMap_reducedRaiseInv

/-- **2021 Theorem 7.6.7, p. 351, for `i = 1`** (new in the 2021 edition): if `T_R` is Hausdorff for
`X` and for `X¹` (equivalently, `X` and `X¹` have (LUC), Theorem 7.2.22), the natural identification
between `(X¹)_R` and `(X_R)¹` (the identity on the common object M-polyfold `X¹`, `[φ]₁ ↦ [φ]` on
morphisms) is an sc-diffeomorphism on the object spaces and on the morphism spaces, and the two
functors are inverse isomorphisms of ep-groupoids. -/
theorem theorem_7_6_7_one :
    X.liftOne.reducedEpGroupoid.PObj = X.reducedEpGroupoid.liftOne.PObj ∧
    (∀ φ, X.reducedEpGroupoid.PMor.levelVal 1 (X.reducedRaise (X.liftOne.reducedπ φ)) =
      X.reducedπ (X.PMor.levelVal 1 φ)) ∧
    X.liftOne.reducedEpGroupoid.PMor.IsScDiffeoOn X.reducedEpGroupoid.liftOne.PMor
      X.reducedRaise X.reducedRaiseInv univ univ ∧
    (X.raiseReducedFunctorInv.comp X.raiseReducedFunctor = EpFunctor.id _ ∧
      X.raiseReducedFunctor.comp X.raiseReducedFunctorInv = EpFunctor.id _) :=
  ⟨rfl, fun _ => rfl, X.isScDiffeoOn_reducedRaise,
    EpFunctor.ext rfl (funext X.reducedRaiseInv_raise),
    EpFunctor.ext rfl (funext X.reducedRaise_inv)⟩

end RaiseOne

end EpGroupoid

namespace EP

open EpGroupoid

/-- The bundled reduced ep-groupoid `X_R` of an ep-groupoid with (LUC) (`T_R` Hausdorff by
Theorem 7.2.22). -/
def reducedOfLUC (A : EP.{u}) (h : A.X.IsLUC) : EP.{u} :=
  letI := A.X.t2Space_reducedMor_of_isLUC h
  { Obj := A.Obj, Mor := A.X.ReducedMor, X := A.X.reducedEpGroupoid }

/-- **`(X¹)_R ≅ (X_R)¹` in `EP`** (Theorem 7.6.7 for `i = 1`), for `X` and `X¹` with (LUC). -/
def raiseReducedIso (A : EP.{u}) (h₀ : A.X.IsLUC) (h₁ : A.liftOne.X.IsLUC) :
    A.liftOne.reducedOfLUC h₁ ≅ (A.reducedOfLUC h₀).liftOne :=
  letI := A.X.t2Space_reducedMor_of_isLUC h₀
  letI := A.X.liftOne.t2Space_reducedMor_of_isLUC h₁
  { hom := A.X.raiseReducedFunctor
    inv := A.X.raiseReducedFunctorInv
    hom_inv_id := A.X.theorem_7_6_7_one.2.2.2.1
    inv_hom_id := A.X.theorem_7_6_7_one.2.2.2.2 }

/-- An isomorphism `X ≅ Y` in `EP` lifts to `X¹ ≅ Y¹` (`EpFunctor.liftOne`). -/
def liftOneIso {A B : EP.{u}} (e : A ≅ B) : A.liftOne ≅ B.liftOne where
  hom := EpFunctor.liftOne e.hom
  inv := EpFunctor.liftOne e.inv
  hom_inv_id := by
    have h₁ := congrArg (fun F : EpFunctor A.X A.X => F.obj) e.hom_inv_id
    have h₂ := congrArg (fun F : EpFunctor A.X A.X => F.mor) e.hom_inv_id
    refine EpFunctor.ext (funext fun x => MPolyfold.level_ext ?_)
      (funext fun φ => MPolyfold.level_ext ?_)
    · exact congrFun h₁ (A.X.PObj.levelVal 1 x)
    · exact congrFun h₂ (A.X.PMor.levelVal 1 φ)
  inv_hom_id := by
    have h₁ := congrArg (fun F : EpFunctor B.X B.X => F.obj) e.inv_hom_id
    have h₂ := congrArg (fun F : EpFunctor B.X B.X => F.mor) e.inv_hom_id
    refine EpFunctor.ext (funext fun x => MPolyfold.level_ext ?_)
      (funext fun φ => MPolyfold.level_ext ?_)
    · exact congrFun h₁ (B.X.PObj.levelVal 1 x)
    · exact congrFun h₂ (B.X.PMor.levelVal 1 φ)

/-- The isomorphisms `(Xⁱ)_R ≅ (X_R)ⁱ` under (SLUC), by recursion on `i` (2021 p. 351). -/
def raiseReducedIsoLift (A : EP.{u}) (h : A.IsSLUC) :
    ∀ i : ℕ, (A.lift i).reducedOfLUC (h i) ≅ (A.reducedOfLUC (h 0)).lift i
  | 0 => Iso.refl _
  | i + 1 => (A.lift i).raiseReducedIso (h i) (h (i + 1)) ≪≫
      liftOneIso (A.raiseReducedIsoLift h i)

/-- **2021 Theorem 7.6.7, p. 351 (new in the 2021 edition)**: under (SLUC), for every `i` the
ep-groupoids `(Xⁱ)_R` and `(X_R)ⁱ` are isomorphic in `EP`: there are sc-smooth functors between them
inverse to each other, so the identification is an sc-diffeomorphism on the object spaces and on the
morphism spaces.  For `i = 1` it is the natural identification (`theorem_7_6_7_one`); for `i ≥ 2`
the composite `(Xⁱ)_R = ((X^{i-1})¹)_R ≅ ((X^{i-1})_R)¹ ≅ … ≅ (X_R)ⁱ` of the text's proof. -/
theorem theorem_7_6_7 (A : EP.{u}) (h : A.IsSLUC) (i : ℕ) :
    Nonempty ((A.lift i).reducedOfLUC (h i) ≅ (A.reducedOfLUC (h 0)).lift i) :=
  ⟨A.raiseReducedIsoLift h i⟩

/-- **2021 Corollary 7.6.8, p. 351 (new in the 2021 edition)**: under (ZHOU), for every `i` the
ep-groupoids `(X_R)ⁱ` and `(Xⁱ)_R` are naturally identified (isomorphic in `EP`), since (ZHOU)
implies (SLUC) (Theorem 7.4.13, `theorem_7_4_13_all_of_isZhou`). -/
theorem corollary_7_6_8 (A : EP.{u}) (hZ : A.X.IsZhou) (i : ℕ) :
    Nonempty ((A.lift i).reducedOfLUC (A.theorem_7_4_13_all_of_isZhou hZ i) ≅
      (A.reducedOfLUC (A.theorem_7_4_13_all_of_isZhou hZ 0)).lift i) :=
  A.theorem_7_6_7 (A.theorem_7_4_13_all_of_isZhou hZ) i

end EP

namespace EpGroupoid.Examples

/-- **The hypothesis (SLUC) of Theorem 7.6.7 is satisfiable**: for the point ep-groupoid
(`isSLUC_pointEP`), `(Xⁱ)_R ≅ (X_R)ⁱ` for every `i`. -/
theorem theorem_7_6_7_pointEP (i : ℕ) :
    Nonempty ((pointEP.lift i).reducedOfLUC (isSLUC_pointEP i) ≅
      (pointEP.reducedOfLUC (isSLUC_pointEP 0)).lift i) :=
  pointEP.theorem_7_6_7 isSLUC_pointEP i

end EpGroupoid.Examples

end Polyfold
