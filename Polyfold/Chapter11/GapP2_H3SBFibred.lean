import Polyfold.Chapter11.GapP2_H3SBPullback

/-!
# The strong bundle version of Theorem 11.6.6 (2021 Remark 11.6.9)

**2021 Remark 11.6.9, pp. 563–566 (2017: Remark 11.27)**: the localization `SBPC[E⁻¹_SBPC]` is
to be carried out as for `PC` (pp. 561–563), whose composition of diagrams rests on Theorem
11.6.6.  Here is the strong bundle version of Theorem 11.6.6, in the category `SBPC` of
`GapP2_H2SBPC.lean`.

## The construction

For an equivalence `Γ = (a, b) : (A, F) → (A', F')` of `SBPC` and a morphism
`Λ = (c, d) : (A'', F'') → (A', F')`, the weak fibred products of strong bundles
(`SBWeakFibredProduct.wfpSEP`, Chapter 10) are `W ×_{W'} W'' = π_{Y''}*W''` over
`P = Y ×_{Y'} Y''` and `V ×_{V'} V'' = π_{X''}*V''` over `Q = X ×_{X'} X''`, and the strong bundle
map between them is `((y, ψ', y''), w'') ↦ (H(y, ψ', y''), A''(w''))`, covering the functor `H` of
Theorem 11.6.6 (`SEP.pullbackCovering`).

## Main declarations

* `SBPC.equivalences_iff`: `E_SBPC` is "both components are strong bundle equivalences"; the
  condition on the base face in H2's definition is automatic (`isEquivalence_iff`).
* `SBPC.NatTrans` (natural transformations of morphisms of `SBPC`: one of strong bundle functors
  on each level, Definition 10.4.8, with (11.20) for their bases), `NaturallyEquivalent`,
  `refl`, `symm`, `trans`, `whiskerLeft`, `whiskerRight`, `NatTrans.comm_total` (the top face
  commutes as well).
* `SBPC.fibred Γ hΓ Λ`, `fibredFst`, `fibredSnd`, `fibredNatTrans`.
* **`SBPC.theorem_11_6_6`**: (1) `(fibred).A` is a proper strong bundle covering functor
  covering `H` (Definition 8.5.9); (2) `fibredSnd` lies in `E_SBPC`; (3) `Γ ∘ fibredFst ≃ Λ ∘
  fibredSnd`; tameness of the bases when `X''` is tame; `fibredFst ∈ E_SBPC` when `Λ` is in
  `E_SBPC`.
-/

set_option maxSynthPendingDepth 3

open Set Function CategoryTheory

noncomputable section

namespace Polyfold

universe u

/-! ### Natural transformations of `SEP` morphisms from a base transformation -/

namespace SEP

open EpStrongBundle

variable {A A' : SEP.{u}}

/-- A natural transformation `f → g` of strong bundle functors covering a given `τ : ϕ_f → ϕ_g`,
when `g(w) = μ'(τ(P w), f(w))` (Definition 10.4.10, `w ↦ (τ(P w), f(w))`). -/
def natTransOfEq (f g : A ⟶ A') (τ : EpNatTrans (Hom.ϕ f) (Hom.ϕ g))
    (h : ∀ w, (Hom.Φ g).obj w = A'.E.μ (transportPair (Hom.isStrongBundleFunctor f) τ w)) :
    A.E.StrongBundleNatTrans A'.E (Hom.ϕ f) (Hom.ϕ g) (Hom.Φ f) (Hom.Φ g) :=
  IsStrongBundleNatTransMap.toNatTrans
    ⟨fun _ => rfl, isStrongBundleMap_transportPair (Hom.isStrongBundleFunctor f) τ, h⟩
    (Hom.isStrongBundleFunctor f) (Hom.isStrongBundleFunctor g)

/-- A morphism of `SEP` commutes with the structure maps: `f(μ(γ, w)) = μ'(ϕ(γ), f(w))`. -/
theorem Hom.obj_μ (f : A ⟶ A') (q : pullbackSpace A.P A.X.src) :
    (Hom.Φ f).obj (A.E.μ q) = A'.E.μ ⟨((Hom.ϕ f).mor q.1.1, (Hom.Φ f).obj q.1.2),
      ((Hom.isStrongBundleFunctor f).isStrongBundleMap_obj.covers _).trans
        ((congrArg (Hom.ϕ f).obj q.2).trans ((Hom.ϕ f).src_mor _).symm)⟩ := by
  obtain ⟨⟨γ, w⟩, h⟩ := q
  exact (Hom.isStrongBundleFunctor f).isMap.map_μ γ w h

@[simp] theorem natTransOfEq_τ (f g : A ⟶ A') (τ : EpNatTrans (Hom.ϕ f) (Hom.ϕ g)) (h) :
    (natTransOfEq f g τ h).τ = τ := rfl

end SEP

namespace SBPC

open ProperCoveringHom

variable {S S' S'' S''' : SBPC.{u}}

/-! ### The class `E_SBPC` -/

/-- **`E_SBPC` is the class of cubes whose two components are strong bundle equivalences**: the
base face of such a cube is an equivalence of proper coverings (Definition 11.6.4 (2)), the fibre
condition being automatic for proper coverings (`isEquivalence_iff`). -/
theorem equivalences_iff (f : S ⟶ S') :
    equivalences f ↔ SEP.equivalences (Hom.a f) ∧ SEP.equivalences (Hom.b f) :=
  ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2,
    (isEquivalence_iff S.isProper.isProperCovering S'.isProper.isProperCovering _).2
      ⟨h.1.isEquivalence_base, h.2.isEquivalence_base⟩⟩⟩

/-- **Two out of three for `E_SBPC`**: if `G` and `L ≫ G` are in `E_SBPC`, so is `L`. -/
theorem equivalences_of_comp_left {L : S ⟶ S'} {G : S' ⟶ S''} (hG : equivalences G)
    (hGL : equivalences (L ≫ G)) : equivalences L :=
  (equivalences_iff L).2
    ⟨EpStrongBundle.IsStrongBundleEquivalence.of_comp_left hG.1
      (SEP.Hom.isStrongBundleFunctor (Hom.a L)) hGL.1,
    EpStrongBundle.IsStrongBundleEquivalence.of_comp_left hG.2.1
      (SEP.Hom.isStrongBundleFunctor (Hom.b L)) hGL.2.1⟩

/-! ### Natural transformations -/

/-- **A natural transformation `f → g` of morphisms of `SBPC`** (2021 Remark 11.6.9; not defined
in the text): natural transformations of strong bundle functors `θa : a_f → a_g` (on `W`) and
`θb : b_f → b_g` (on `V`), Definition 10.4.8, whose base transformations satisfy (11.20),
`τ_b(F(y)) = F'(τ_a(y))`, i.e. form a natural transformation of the base faces
(Definition 11.6.5).  The top face then commutes as well (`comm_total`). -/
structure NatTrans (f g : S ⟶ S') where
  /-- The transformation on the bundles over `Y`. -/
  θa : S.W.E.StrongBundleNatTrans S'.W.E (SEP.Hom.ϕ (Hom.a f)) (SEP.Hom.ϕ (Hom.a g))
    (SEP.Hom.Φ (Hom.a f)) (SEP.Hom.Φ (Hom.a g))
  /-- The transformation on the bundles over `X`. -/
  θb : S.V.E.StrongBundleNatTrans S'.V.E (SEP.Hom.ϕ (Hom.b f)) (SEP.Hom.ϕ (Hom.b g))
    (SEP.Hom.Φ (Hom.b f)) (SEP.Hom.Φ (Hom.b g))
  comm : ∀ y, θb.τ.app ((SEP.Hom.ϕ S.A).obj y) = (SEP.Hom.ϕ S'.A).mor (θa.τ.app y)

/-- Natural equivalence of morphisms of `SBPC`. -/
def NaturallyEquivalent (f g : S ⟶ S') : Prop := Nonempty (NatTrans f g)

namespace NatTrans

variable {f g k : S ⟶ S'}

/-- The base faces of a natural transformation: a natural transformation of functors between
proper coverings (Definition 11.6.5). -/
def toPC (θ : NatTrans f g) : ProperCoveringHom.NatTrans (forget.map f) (forget.map g) :=
  ⟨θ.θa.τ, θ.θb.τ, θ.comm⟩

/-- **The top face commutes**: `A'(θa(w)) = θb(A(w))` as morphisms of the total ep-groupoid of
`V'` (both are `(τ_b(F(P w)), b(A(w)))`). -/
theorem comm_total (θ : NatTrans f g) (w : S.W.W) :
    (SEP.Hom.Φ S'.A).mor (θ.θa.T w) = θ.θb.T ((SEP.Hom.Φ S.A).obj w) := by
  apply Subtype.ext
  rw [(SEP.Hom.isStrongBundleFunctor S'.A).mor_val, θ.θa.T_val, θ.θb.T_val,
    (SEP.Hom.isStrongBundleFunctor S.A).isStrongBundleMap_obj.covers, θ.comm]
  exact Prod.ext rfl (SBPC.comm_total f w).symm

variable (f) in
/-- The identity transformation. -/
def refl : NatTrans f f :=
  ⟨EpStrongBundle.StrongBundleNatTrans.refl (SEP.Hom.isStrongBundleFunctor (Hom.a f)),
    EpStrongBundle.StrongBundleNatTrans.refl (SEP.Hom.isStrongBundleFunctor (Hom.b f)),
    (ProperCoveringHom.NatTrans.refl (forget.map f)).comm⟩

/-- The inverse transformation. -/
def symm (θ : NatTrans f g) : NatTrans g f :=
  ⟨θ.θa.symm (SEP.Hom.isStrongBundleFunctor (Hom.a f)),
    θ.θb.symm (SEP.Hom.isStrongBundleFunctor (Hom.b f)), θ.toPC.symm.comm⟩

/-- The composite transformation. -/
def trans (θ : NatTrans f g) (θ' : NatTrans g k) : NatTrans f k :=
  ⟨θ.θa.trans θ'.θa (SEP.Hom.isStrongBundleFunctor (Hom.a f))
      (SEP.Hom.isStrongBundleFunctor (Hom.a g)),
    θ.θb.trans θ'.θb (SEP.Hom.isStrongBundleFunctor (Hom.b f))
      (SEP.Hom.isStrongBundleFunctor (Hom.b g)), (θ.toPC.trans θ'.toPC).comm⟩

/-- Whiskering on the left: `K ≫ f → K ≫ g`. -/
def whiskerLeft (θ : NatTrans f g) (K : S'' ⟶ S) : NatTrans (K ≫ f) (K ≫ g) :=
  ⟨θ.θa.whiskerLeft (SEP.Hom.isStrongBundleFunctor (Hom.a f))
      (SEP.Hom.isStrongBundleFunctor (Hom.a K)),
    θ.θb.whiskerLeft (SEP.Hom.isStrongBundleFunctor (Hom.b f))
      (SEP.Hom.isStrongBundleFunctor (Hom.b K)), (θ.toPC.whiskerLeft (forget.map K)).comm⟩

/-- Whiskering on the right: `f ≫ K → g ≫ K`. -/
def whiskerRight (θ : NatTrans f g) (K : S' ⟶ S'') : NatTrans (f ≫ K) (g ≫ K) :=
  ⟨θ.θa.whiskerRight (SEP.Hom.isStrongBundleFunctor (Hom.a f))
      (SEP.Hom.isStrongBundleFunctor (Hom.a K)),
    θ.θb.whiskerRight (SEP.Hom.isStrongBundleFunctor (Hom.b f))
      (SEP.Hom.isStrongBundleFunctor (Hom.b K)), (θ.toPC.whiskerRight (forget.map K)).comm⟩

end NatTrans

theorem naturallyEquivalent_equivalence :
    Equivalence (NaturallyEquivalent (S := S) (S' := S')) :=
  ⟨fun f => ⟨NatTrans.refl f⟩, fun ⟨θ⟩ => ⟨θ.symm⟩, fun ⟨θ⟩ ⟨θ'⟩ => ⟨θ.trans θ'⟩⟩

theorem NaturallyEquivalent.comp_left {f g : S ⟶ S'} (h : NaturallyEquivalent f g)
    (K : S'' ⟶ S) : NaturallyEquivalent (K ≫ f) (K ≫ g) :=
  let ⟨θ⟩ := h
  ⟨θ.whiskerLeft K⟩

theorem NaturallyEquivalent.comp_right {f g : S ⟶ S'} (h : NaturallyEquivalent f g)
    (K : S' ⟶ S'') : NaturallyEquivalent (f ≫ K) (g ≫ K) :=
  let ⟨θ⟩ := h
  ⟨θ.whiskerRight K⟩

theorem NaturallyEquivalent.of_eq {f g f' g' : S ⟶ S'} (h : NaturallyEquivalent f' g')
    (h₁ : f = f') (h₂ : g = g') : NaturallyEquivalent f g := h₁ ▸ h₂ ▸ h

/-! ### The weak fibred product in `SBPC` -/

open WeakFibredProduct SBWeakFibredProduct

variable (Γ : S ⟶ S') (hΓ : equivalences Γ) (Λ : S'' ⟶ S')

/-- The base `P = Y ×_{Y'} Y''` of `W ×_{W'} W''`. -/
abbrev baseW : EP.{u} := baseEP hΓ.1 (Hom.a Λ)

/-- The base `Q = X ×_{X'} X''` of `V ×_{V'} V''`. -/
abbrev baseV : EP.{u} := baseEP hΓ.2.1 (Hom.b Λ)

/-- **The functor `H : P → Q`** of Theorem 11.6.6, for the base faces of `Γ` and `Λ`. -/
def fibredH : EpFunctor (baseW Γ hΓ Λ).X (baseV Γ hΓ Λ).X :=
  hFunctor (forget.map Γ) (forget.map Λ) (admissible hΓ.1 (Hom.a Λ)) (admissible hΓ.2.1 (Hom.b Λ))

theorem fibred_comm :
    (SEP.Hom.ϕ S''.A).comp (projRight (SEP.Hom.ϕ (Hom.a Γ)) (SEP.Hom.ϕ (Hom.a Λ))
      (admissible hΓ.1 (Hom.a Λ))) =
    (projRight (SEP.Hom.ϕ (Hom.b Γ)) (SEP.Hom.ϕ (Hom.b Λ)) (admissible hΓ.2.1 (Hom.b Λ))).comp
      (fibredH Γ hΓ Λ) :=
  EpFunctor.ext rfl rfl

/-- **Theorem 11.6.6 for the base faces** (with the admissibility proofs of `wfpSEP`). -/
theorem fibred_base :
    (fibredH Γ hΓ Λ).IsProperCovering ∧
    (projRightHom (forget.map Γ) (forget.map Λ) (admissible hΓ.1 (Hom.a Λ))
      (admissible hΓ.2.1 (Hom.b Λ))).IsEquivalence ∧
    (S''.V.X.IsTame → (baseW Γ hΓ Λ).X.IsTame ∧ (baseV Γ hΓ Λ).X.IsTame) := by
  obtain ⟨h1, h2, -, h4, -⟩ := theorem_11_6_6 (forget.map Γ) (forget.map Λ)
    S.isProper.isProperCovering S'.isProper.isProperCovering S''.isProper.isProperCovering hΓ.2.2
  exact ⟨h1, h2, h4⟩

/-- **The weak fibred product `(A, F) ×_{(A', F')} (A'', F'')` in `SBPC`**:
`W ×_{W'} W'' → V ×_{V'} V''`, `(p, w'') ↦ (H(p), A''(w''))`, a proper strong bundle covering
covering `H`
(`isProperStrongBundleCovering2021_pullbackCovering_of_isEquivalence`, with the equivalence
`(π_{Y''}, π_{X''}) : H → F''` of Theorem 11.6.6 (2)). -/
def fibred : SBPC.{u} where
  W := wfpSEP hΓ.1 (Hom.a Λ)
  V := wfpSEP hΓ.2.1 (Hom.b Λ)
  A := SEP.pullbackCovering S''.A (fibredH Γ hΓ Λ) _ _ (fibred_comm Γ hΓ Λ)
  isProper := SEP.isProperStrongBundleCovering2021_pullbackCovering_of_isEquivalence _
    S''.isProper (fibred_base Γ hΓ Λ).1 (fibred_base Γ hΓ Λ).2.1

theorem fibred_A_ϕ : SEP.Hom.ϕ (fibred Γ hΓ Λ).A = fibredH Γ hΓ Λ := rfl

/-- `π_{(A'', F'')} : (A, F) ×_{(A', F')} (A'', F'') → (A'', F'')`, `(ΠZ, ΠZ)`. -/
def fibredSnd : fibred Γ hΓ Λ ⟶ S'' :=
  (⟨projZ hΓ.1 (Hom.a Λ), projZ hΓ.2.1 (Hom.b Λ),
    SEP.pullbackCovering_comp_pullbackHom _ _ _ _ (fibred_comm Γ hΓ Λ)⟩ : Hom _ _)

@[simp] theorem fibredSnd_a : Hom.a (fibredSnd Γ hΓ Λ) = projZ hΓ.1 (Hom.a Λ) := rfl
@[simp] theorem fibredSnd_b : Hom.b (fibredSnd Γ hΓ Λ) = projZ hΓ.2.1 (Hom.b Λ) := rfl

/-- The top face of `fibredFst` commutes: `A(ΠX(p, w'')) = ΠX(H(p), A''(w''))`. -/
theorem fibredFst_comm :
    (fibred Γ hΓ Λ).A ≫ projX hΓ.2.1 (Hom.b Λ) = projX hΓ.1 (Hom.a Λ) ≫ S.A := by
  refine SEP.Hom.ext_obj (EpFunctor.ext rfl rfl) (funext fun m => ?_)
  change (SEP.Hom.Φ (projX hΓ.2.1 (Hom.b Λ))).obj ((SEP.Hom.Φ (fibred Γ hΓ Λ).A).obj m) =
    (SEP.Hom.Φ S.A).obj ((SEP.Hom.Φ (projX hΓ.1 (Hom.a Λ))).obj m)
  have hA := SEP.Hom.isStrongBundleFunctor S.A
  have hA' := SEP.Hom.isStrongBundleFunctor S'.A
  refine SEP.coneHom_obj_eq hΓ.2.1 (Hom.b Λ) (Y := baseV Γ hΓ Λ)
    (projRight (SEP.Hom.ϕ (Hom.b Γ)) (SEP.Hom.ϕ (Hom.b Λ)) (admissible hΓ.2.1 (Hom.b Λ)))
    (projLeft (SEP.Hom.ϕ (Hom.b Γ)) (SEP.Hom.ϕ (Hom.b Λ)) (admissible hΓ.2.1 (Hom.b Λ)))
    (natTrans (SEP.Hom.ϕ (Hom.b Γ)) (SEP.Hom.ϕ (Hom.b Λ)) (admissible hΓ.2.1 (Hom.b Λ))).symm
    ((hA.isStrongBundleMap_obj.covers _).trans (congrArg (SEP.Hom.ϕ S.A).obj
      (SEP.P_coneHom hΓ.1 (Hom.a Λ) (Y := baseW Γ hΓ Λ) _ _ _ m))) ?_
  refine (comm_total Γ _).trans ?_
  refine (congrArg (SEP.Hom.Φ S'.A).obj
    (SEP.obj_coneHom hΓ.1 (Hom.a Λ) (Y := baseW Γ hΓ Λ) _ _ _ m)).trans ?_
  refine (SEP.Hom.obj_μ S'.A _).trans (S'.V.E.μ_congr (Prod.ext ?_ ?_))
  · exact GroupoidFunctor.mor_inv (SEP.Hom.ϕ S'.A).toGroupoidFunctor m.1.1.φ
  · exact (comm_total Λ m.1.2).symm

/-- `π_{(A, F)} : (A, F) ×_{(A', F')} (A'', F'') → (A, F)`, `(ΠX, ΠX)`. -/
def fibredFst : fibred Γ hΓ Λ ⟶ S :=
  (⟨projX hΓ.1 (Hom.a Λ), projX hΓ.2.1 (Hom.b Λ), fibredFst_comm Γ hΓ Λ⟩ : Hom _ _)

@[simp] theorem fibredFst_a : Hom.a (fibredFst Γ hΓ Λ) = projX hΓ.1 (Hom.a Λ) := rfl
@[simp] theorem fibredFst_b : Hom.b (fibredFst Γ hΓ Λ) = projX hΓ.2.1 (Hom.b Λ) := rfl

/-- `Γ ∘ π_{(A, F)} → Λ ∘ π_{(A'', F'')}`: on each level `w ↦ (φ, Γ(ΠX(w)))` over
`τ(x, φ, z) = φ` (Theorem 10.2.2), the base faces being `natTransProj` (Theorem 11.6.6 (3)). -/
def fibredNatTrans : NatTrans (fibredFst Γ hΓ Λ ≫ Γ) (fibredSnd Γ hΓ Λ ≫ Λ) where
  θa := SEP.natTransOfEq _ _ (natTrans (SEP.Hom.ϕ (Hom.a Γ)) (SEP.Hom.ϕ (Hom.a Λ))
      (admissible hΓ.1 (Hom.a Λ))) fun m => by
    have hm : S'.W.P ((SEP.Hom.Φ (Hom.a Λ)).obj m.1.2) = S'.W.X.src (S'.W.X.inv m.1.1.φ) := by
      rw [S'.W.X.src_inv, m.1.1.tgt_φ,
        (SEP.Hom.isStrongBundleFunctor (Hom.a Λ)).isStrongBundleMap_obj.covers, m.2]
      rfl
    exact (EpStrongBundle.μ_eq_of_eq_μ_inv _ hm
      (SEP.obj_coneHom hΓ.1 (Hom.a Λ) (Y := baseW Γ hΓ Λ) _ _ _ m)).symm
  θb := SEP.natTransOfEq _ _ (natTrans (SEP.Hom.ϕ (Hom.b Γ)) (SEP.Hom.ϕ (Hom.b Λ))
      (admissible hΓ.2.1 (Hom.b Λ))) fun m => by
    have hm : S'.V.P ((SEP.Hom.Φ (Hom.b Λ)).obj m.1.2) = S'.V.X.src (S'.V.X.inv m.1.1.φ) := by
      rw [S'.V.X.src_inv, m.1.1.tgt_φ,
        (SEP.Hom.isStrongBundleFunctor (Hom.b Λ)).isStrongBundleMap_obj.covers, m.2]
      rfl
    exact (EpStrongBundle.μ_eq_of_eq_μ_inv _ hm
      (SEP.obj_coneHom hΓ.2.1 (Hom.b Λ) (Y := baseV Γ hΓ Λ) _ _ _ m)).symm
  comm _ := rfl

/-- **The strong bundle version of 2021 Theorem 11.6.6, p. 555 (2017: Theorem 11.10)**, as used
in Remark 11.6.9: for an equivalence `Γ : (A, F) → (A', F')` of `SBPC` and a morphism
`Λ : (A'', F'') → (A', F')`, with `W ×_{W'} W''` over `P = Y ×_{Y'} Y''`, `V ×_{V'} V''` over
`Q = X ×_{X'} X''` and `(p, w'') ↦ (H(p), A''(w''))` between them: (1) this map is a proper strong
bundle covering functor covering `H` (Definition 8.5.9), (2) `π_{(A'', F'')}` is an equivalence
of `SBPC`, (3) `Γ ∘ π_{(A, F)}` and `Λ ∘ π_{(A'', F'')}` are naturally equivalent; if `X''` is
tame, so are `P` and `Q`; if `Λ` is an equivalence, so is `π_{(A, F)}`. -/
theorem theorem_11_6_6 :
    (fibred Γ hΓ Λ).W.E.IsProperStrongBundleCovering2021 (fibred Γ hΓ Λ).V.E (fibredH Γ hΓ Λ)
      (SEP.Hom.Φ (fibred Γ hΓ Λ).A).obj ∧
    equivalences (fibredSnd Γ hΓ Λ) ∧
    NaturallyEquivalent (fibredFst Γ hΓ Λ ≫ Γ) (fibredSnd Γ hΓ Λ ≫ Λ) ∧
    (S''.V.X.IsTame → (baseW Γ hΓ Λ).X.IsTame ∧ (baseV Γ hΓ Λ).X.IsTame) ∧
    (equivalences Λ → equivalences (fibredFst Γ hΓ Λ)) :=
  ⟨(fibred Γ hΓ Λ).isProper,
    (equivalences_iff _).2 ⟨(theorem_10_2_2 hΓ.1 (Hom.a Λ)).1, (theorem_10_2_2 hΓ.2.1 (Hom.b Λ)).1⟩,
    ⟨fibredNatTrans Γ hΓ Λ⟩, (fibred_base Γ hΓ Λ).2.2,
    fun hΛ => (equivalences_iff _).2
      ⟨theorem_10_2_2_right hΓ.1 (Hom.a Λ) hΛ.1, theorem_10_2_2_right hΓ.2.1 (Hom.b Λ) hΛ.2.1⟩⟩

theorem equivalences_fibredSnd : equivalences (fibredSnd Γ hΓ Λ) :=
  (theorem_11_6_6 Γ hΓ Λ).2.1

end SBPC

end Polyfold

end
