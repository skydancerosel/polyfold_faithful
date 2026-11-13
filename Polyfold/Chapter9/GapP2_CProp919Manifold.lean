import Polyfold.Chapter9.GapP2_CProp919
import Polyfold.Chapter9.GapP2_CDescentPolyfold
import Polyfold.Chapter7.NaturalRep
import Polyfold.Chapter7.NaturalAction
import Polyfold.Chapter7.OrbitTopology

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, Chapter 9,
§9.1, **Proposition 9.1.9 (1)** (p. 405; 2017: Proposition 9.1 (1), p. 295).

# The manifold structure on `|supp(Θ)|` for `Θ` of manifold-type

## The text, paraphrased

(Proposition 9.1.9 (1)) For `Θ` of manifold-type (values in `{0, 1}`, at most one morphism
between two objects of `supp(Θ)`), `X` induces on `Z = |supp(Θ)|` a natural smooth manifold
structure.  *Proof* (text): `G_x = {1_x}` for `x ∈ supp(Θ)`, so `Ψ_x : M_x → Z`, `w ↦ |w|`, is
injective; if `Ψ_x(w) = Ψ_{x'}(w')` there is a morphism `φ : w → w'`, and
`f = t ∘ (s|U(φ))⁻¹` maps `M_x` to `M_{x'}` near `w` with `f = Ψ_{x'}⁻¹ ∘ Ψ_x`; the charts of the
`M_x` pushed forward by the `Ψ_x` are compatible and give the manifold structure on `Z`.

## What is formalized

With `A = supp(Θ)`, an ep-subgroupoid (`GapP2_CProp919.lean`), `Y = subEpGroupoid hA` its
ep-groupoid, and `p : A → Z`, `a ↦ |a|`:

* `EpGroupoid.subsingleton_isotropy_of_isManifoldType`: the isotropy groups of `Y` are trivial.
* `EpGroupoid.injOn_π_of_subsingleton_isotropy`: for an ep-groupoid with trivial isotropy at `x`,
  `π` is injective on the domain `U(x)` of a natural representation (the text's "`Ψ_x` is
  injective").
* `EpGroupoid.isDescentMap_orbitSupp`: `p` satisfies the hypotheses of the descent of
  `GapP2_CDescentPolyfold.lean` (open, surjective, locally injective, and the transition maps are
  the sc-smooth maps `t ∘ (s|U(φ))⁻¹`).
* **`EpGroupoid.proposition_9_1_9_one`**: `supp(Θ)` is a smooth finite-dimensional submanifold of
  `X`, and `Z = |supp(Θ)| ⊆ |X|` (with the induced topology) carries an M-polyfold structure for
  which `p : supp(Θ) → Z` is a local sc-diffeomorphism.  So `Z` is locally sc-diffeomorphic to a
  smooth finite-dimensional submanifold of `X`: a manifold in the M⁺-polyfold sense of
  Remark 9.1.10.

## How it relates to the text

The text's charts `Ψ_x` on the sheets `M_x` are the descended charts of `MPolyfold.descend` on the
pieces `M_x ∩ U(x)` of `supp(Θ)`; the structure is "natural" in that `p` is a local
sc-diffeomorphism (it is determined by this property).  The paracompactness of `Z` used to make it
an M-polyfold is part of Definition 9.1.2 (1); the hypothesis that `|X|` is paracompact is not
used.  Remark 9.1.10's classical structure (`d_{|X|} = 0` on `Z`) and the independence of choices
are not formalized here.
-/

open Set Function Topology TopologicalSpace

noncomputable section

namespace Polyfold

universe u

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]

/-- **Trivial isotropy gives injectivity on `U(x)`** (the text: "every `Ψ_x` is injective"): if
`G_x = {1}`, two points of `U(x)` with the same orbit coincide, the morphism between them being
`Γ(1, y) = 1_y`. -/
theorem injOn_π_of_subsingleton_isotropy (Y : EpGroupoid Obj Mor) {x : Obj}
    [Subsingleton (Y.Isotropy x)] (R : Y.NaturalRep x) : InjOn Y.π R.U := by
  intro y hy y' hy' h
  obtain ⟨φ, rfl, rfl⟩ := (Y.π_eq_π_iff).1 h
  obtain ⟨g, hg, -⟩ := R.existsUnique_Γ φ hy hy'
  rw [Subsingleton.elim g 1, R.Γ_one hy] at hg
  rw [← hg, Y.tgt_unit]
  exact Y.src_unit _

variable {X : EpGroupoid Obj Mor} {Θ : Obj → ℚ}

/-- For `Θ` of manifold-type, the isotropy groups of the full subcategory on `supp(Θ)` are trivial
(the text: "`G_x = {1_x}`"). -/
theorem subsingleton_isotropy_of_isManifoldType (hm : X.IsManifoldType Θ)
    (hA : X.IsEpSubgroupoid (supp Θ)) [ParacompactSpace (supp Θ)] (a : supp Θ) :
    Subsingleton ((subEpGroupoid hA).Isotropy a) := by
  refine ⟨fun g h => GroupoidStr.Isotropy.ext (Subtype.ext ?_)⟩
  have hgs : X.src g.val.1 = a.1 := congrArg Subtype.val g.src_val
  have hgt : X.tgt g.val.1 = a.1 := congrArg Subtype.val g.tgt_val
  have hhs : X.src h.val.1 = a.1 := congrArg Subtype.val h.src_val
  have hht : X.tgt h.val.1 = a.1 := congrArg Subtype.val h.tgt_val
  exact hm.2 _ _ (hgs ▸ a.2) (hgt ▸ a.2) (hgs.trans hhs.symm) (hgt.trans hht.symm)

/-- The map `p : supp(Θ) → |supp(Θ)|`, `a ↦ |a|`. -/
def orbitSuppProj (X : EpGroupoid Obj Mor) (Θ : Obj → ℚ) (a : supp Θ) : X.orbitSupp Θ :=
  ⟨X.π a.1, a.1, a.2, rfl⟩

theorem orbitSuppProj_eq (hA : X.IsEpSubgroupoid (supp Θ)) [ParacompactSpace (supp Θ)] :
    X.orbitSuppProj Θ = orbitSuppHomeomorph hA ∘ (subEpGroupoid hA).π := rfl

/-- **The hypotheses of the descent hold for `p : supp(Θ) → |supp(Θ)|`** when `Θ` is of
manifold-type. -/
theorem isDescentMap_orbitSupp (hm : X.IsManifoldType Θ) (hA : X.IsEpSubgroupoid (supp Θ))
    [ParacompactSpace (supp Θ)] :
    (subEpGroupoid hA).PObj.IsDescentMap (X.orbitSuppProj Θ) := by
  set Y := subEpGroupoid hA
  set e := orbitSuppHomeomorph hA
  have hp : X.orbitSuppProj Θ = e ∘ Y.π := rfl
  have hpeq : ∀ a b, X.orbitSuppProj Θ a = X.orbitSuppProj Θ b → Y.π a = Y.π b := fun a b h =>
    e.injective h
  refine ⟨?_, ?_, ?_, fun a => ?_, fun a b hab => ?_⟩
  · rw [hp]; exact e.continuous.comp Y.continuous_π
  · rw [hp]; exact e.isOpenMap.comp Y.proposition_7_1_8
  · rw [hp]; exact e.surjective.comp Y.surjective_π
  · obtain ⟨R, -⟩ := Y.theorem_7_1_13 a isOpen_univ (mem_univ _)
    have := subsingleton_isotropy_of_isManifoldType hm hA a
    exact ⟨R.U, R.isOpen_U, R.mem_U, fun y hy y' hy' h =>
      injOn_π_of_subsingleton_isotropy Y R hy hy' (hpeq y y' h)⟩
  · obtain ⟨φ, rfl, rfl⟩ := (Y.π_eq_π_iff).1 (hpeq a b hab)
    obtain ⟨U', V', σ, hφ, hd⟩ := Y.isLocalScDiffeo_src φ
    refine ⟨V', Y.tgt ∘ σ, hd.isScSmoothOn_inv.isOpen, hd.mapsTo hφ, ?_, ?_, fun y hy => ?_⟩
    · exact MPolyfold.IsScSmoothOn.comp Y.isLocalScDiffeo_tgt.isScSmoothMap hd.isScSmoothOn_inv
        (mapsTo_univ _ _)
    · change Y.tgt (σ (Y.src φ)) = Y.tgt φ
      rw [hd.left_inv φ hφ]
    · rw [hp]
      change e (Y.π (Y.tgt (σ y))) = e (Y.π y)
      refine congrArg e ((Y.π_eq_π_iff).2 ⟨σ y, hd.right_inv y hy, rfl⟩).symm

/-- **2021 Proposition 9.1.9 (1)**, p. 405 (2017: Proposition 9.1 (1), p. 295): for a branched
ep⁺-subgroupoid `Θ` of manifold-type, `supp(Θ)` is a smooth finite-dimensional submanifold of `X`
and an ep-subgroupoid, and `X` induces on `Z = |supp(Θ)|` (the subspace of `|X|`) an M-polyfold
structure `PZ` for which `p : supp(Θ) → Z`, `a ↦ |a|`, is a local sc-diffeomorphism (the charts
of the text, `Ψ_x` on the sheets `M_x`).  `Z` is thus locally sc-diffeomorphic to a smooth
finite-dimensional submanifold: a smooth manifold in the M⁺-polyfold sense (Remark 9.1.10). -/
theorem proposition_9_1_9_one (hΘ : X.IsBranchedEpSubgroupoid Θ) (hm : X.IsManifoldType Θ) :
    ∃ hA : X.IsEpSubgroupoid (supp Θ), X.PObj.IsSmoothSubmanifold (supp Θ) ∧
      haveI := X.PObj.paracompactSpace_subtype (supp Θ)
      haveI := hΘ.paracompactSpace_orbitSupp
      ∃ PZ : MPolyfold (X.orbitSupp Θ),
        (subEpGroupoid hA).PObj.IsLocalScDiffeo PZ (X.orbitSuppProj Θ) := by
  have hA := isEpSubgroupoid_supp_of_isOrbifoldType hΘ hm.1
  have := X.PObj.paracompactSpace_subtype (supp Θ)
  have := hΘ.paracompactSpace_orbitSupp
  exact ⟨hA, isSmoothSubmanifold_supp_of_isOrbifoldType hΘ hm.1, _,
    MPolyfold.isLocalScDiffeo_descend (isDescentMap_orbitSupp hm hA)⟩

end EpGroupoid

end Polyfold
