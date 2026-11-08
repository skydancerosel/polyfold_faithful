import Polyfold.Chapter10.WeakFibredProduct
import Polyfold.Chapter10.EquivalenceExamples

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 10, §10.2 "The Weak Fibered Product" (pp. 477–483; 2017: pp. 343–347):
**Theorem 10.2.2** (2017: Theorem 10.2) apart from its first claim, and **Remark 10.2.3** (2017:
Remark 10.2).  The ep-groupoid `WeakFibredProduct.epGroupoid` itself (Definition 10.2.1 and the
first claim of Theorem 10.2.2) is built in `WeakFibredProduct.lean`.

# The projections of the weak fibred product

## The text, paraphrased

(Theorem 10.2.2, p. 477 (2017: Theorem 10.2, p. 343)) Let `F : X → Y` be an equivalence and
`G : Z → Y` sc-smooth.  Then `X ×_Y Z` is an ep-groupoid, the projection `πZ` is an equivalence,
`F ∘ πX` and `G ∘ πZ` are naturally equivalent, `d_{X ×_Y Z}(x, ϕ, z) = d_Z(z)`, and if `Z` is tame
or has a paracompact orbit space, so has `X ×_Y Z`.  If `G` is an equivalence instead, `πX` is an
equivalence and `d_{X ×_Y Z}(x, ϕ, z) = d_X(x)`; if both are, `d_X(x) = d_{X ×_Y Z}(x, ϕ, z) =
d_Z(z)`.  The M-polyfold structures are in both cases the sub-M-polyfold structures.

*Proof (text, pp. 481–482)*: `πZ` is surjective and a local sc-diffeomorphism; for `k : z → z'`
there is a unique `h : x → x'` with `F(h)` the morphism `F(x) → F(x')` obtained from `ϕ`, `G(k)`,
`ϕ'`, and `(h, ϕ, k)` is the unique morphism over `k`, so `πZ` is full and faithful; for `z ∈ Z`
an `x` and an isomorphism `ϕ : F(x) → G(z)` exist, so `πZ` is essentially surjective, and Lemma
10.1.2 applies.  `σ(x, ϕ, z) = ϕ` is a natural transformation `F ∘ πX → G ∘ πZ`.  Tameness and
paracompactness of the orbit space pass along the local sc-diffeomorphism `πZ` and the
homeomorphism `|πZ|`, and `d(x, ϕ, z) = d_Z(z)` since `πZ` is a local sc-diffeomorphism.

(Remark 10.2.3, pp. 482–483 (2017: Remark 10.2, p. 347)) For equivalences `F : A → X` and
`H : B → X` the weak fibred product `A ×_X B` is an ep-groupoid, both projections are
equivalences, and `τ(a, ϕ, b) = ϕ` is a natural equivalence `F ∘ πA ≃ H ∘ πB`.

## What is formalized (namespace `Polyfold.WeakFibredProduct`)

* General facts about an equivalence `F : X → Y` (the text's argument in the paragraph after the
  theorem): `EpFunctor.IsEquivalence.degIndex_obj` (`d_Y(F(x)) = d_X(x)`),
  `EpFunctor.IsEquivalence.isTame_of_isTame`, `EpFunctor.IsEquivalence.hasParacompactOrbitSpace`.
* `Admissible.of_isEquivalence_left`, `Admissible.of_isEquivalence_right`: an equivalence `F` or
  `G` makes `epGroupoid F G` available.
* **The reusable API**: the projections `projLeft F G h = πX`, `projRight F G h = πZ`
  (sc-smooth functors), the 2-commutativity natural transformation
  `natTrans F G h : F ∘ πX → G ∘ πZ` (`natTrans_app : σ(x, ϕ, z) = ϕ`), `naturallyEquivalent`,
  and the equivalence statements `isEquivalence_projRight` (`F` an equivalence) and
  `isEquivalence_projLeft` (`G` an equivalence); `degIndex_eq_z`, `degIndex_eq_x`.
* **Theorem 10.2.2**: `theorem_10_2_2` (the case `F` an equivalence, all claims after the first),
  `theorem_10_2_2_right` (the case `G` an equivalence), `theorem_10_2_2_both` (the degeneracy
  indices when both are).
* **Remark 10.2.3**: `remark_10_2_3`.
* Witnesses (namespace `Polyfold.WeakFibredProduct.Examples`): `theorem_10_2_2_pairToPoint`, the
  weak fibred product of `pairToPoint` (the pair groupoid of `ℤ` over the point) with the identity
  of the point, a nonempty ep-groupoid with `πZ` an equivalence; `remark_10_2_3_negFunctor`, the
  weak fibred product of the identity and `-id` of `ℤ/2 ⋉ ℝ²` (`negFunctor`, from
  `EquivalenceExamples.lean`), nonempty, both projections equivalences.

## What the text leaves implicit, and the choices made

* Every statement takes the admissibility proof `h : Admissible F G` as an argument or supplies it
  by `Admissible.of_isEquivalence_left` (resp. `_right`); it is a proposition, so the ep-groupoid
  does not depend on it, which is the text's "in both cases the natural sub-M-polyfold
  structures": for two equivalences the structures of the two cases are the same.
* **Fullness.**  The text writes the morphism `F(x) → F(x')` as `ϕ' ∘ G(k) ∘ ϕ⁻¹`; with
  `ϕ : F(x) → G(z)` and `ϕ' : F(x') → G(z')` the composite which has these ends is
  `ϕ'⁻¹ ∘ G(k) ∘ ϕ` (possible misprint), and this is what we use.  For `G` an equivalence the
  morphism `G(z) → G(z')` is `ϕ' ∘ F(h) ∘ ϕ⁻¹`.
* **Essential surjectivity** of `πZ`: the text uses that `|F|` is a bijection; we use the essential
  surjectivity of `F` (`IsEquivalence.exists_iso`), which is that bijectivity.
* Tameness of an ep-groupoid is `EpGroupoid.IsTame` (Definition 7.1.6: its object M-polyfold is
  tame), a paracompact orbit space is `EpGroupoid.HasParacompactOrbitSpace` (Definition 7.5.1),
  and the degeneracy index is that of the object M-polyfold.  For the case `G` an equivalence the
  text states only the equivalence and the degeneracy index; `theorem_10_2_2_right` adds the
  natural equivalence and the transfer of tameness and of paracompactness, by the same argument.
* The closing sentences of Remark 10.2.3 (an equivalence `A → X` as a "smaller model" of `X`) are
  an interpretation and are not formalized.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u v w

/-! ### Invariants transported along an equivalence -/

namespace EpFunctor.IsEquivalence

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'} {F : EpFunctor X Y}

/-- An equivalence preserves the degeneracy index: `d_Y(F(x)) = d_X(x)` (2021 p. 478, the
argument after Theorem 10.2.2: `F` is a local sc-diffeomorphism on objects). -/
theorem degIndex_obj (hF : F.IsEquivalence) (x : Obj) :
    Y.PObj.degIndex (F.obj x) = X.PObj.degIndex x :=
  hF.isLocalScDiffeo_obj.degIndex_eq x

/-- If `F : X → Y` is an equivalence and `Y` is tame, so is `X` (2021 p. 478: "tameness is
invariant under sc-diffeomorphisms"). -/
theorem isTame_of_isTame (hF : F.IsEquivalence) (hY : Y.IsTame) : X.IsTame :=
  hF.isLocalScDiffeo_obj.isTame hY

/-- If `F : X → Y` is an equivalence and `|Y|` is paracompact, so is `|X|` (2021 p. 478: `|F|` is
a homeomorphism). -/
theorem hasParacompactOrbitSpace (hF : F.IsEquivalence) (hY : Y.HasParacompactOrbitSpace) :
    X.HasParacompactOrbitSpace := by
  let _ : ParacompactSpace Y.OrbitSpace := hY
  exact (IsHomeomorph.homeomorph _ hF.isHomeomorph_orbitMap).isClosedEmbedding.paracompactSpace

end EpFunctor.IsEquivalence

section WFPTheorem

variable {ObjX MorX : Type u} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY MorY : Type v} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjZ MorZ : Type w} [TopologicalSpace ObjZ] [T2Space ObjZ] [ParacompactSpace ObjZ]
  [TopologicalSpace MorZ] [T2Space MorZ] [ParacompactSpace MorZ]
  {X : EpGroupoid ObjX MorX} {Y : EpGroupoid ObjY MorY} {Z : EpGroupoid ObjZ MorZ}
  {F : EpFunctor X Y} {G : EpFunctor Z Y}

namespace WeakFibredProduct

/-- If `F` is an equivalence, the weak fibred product of `F` and any `G` is an ep-groupoid. -/
theorem Admissible.of_isEquivalence_left (hF : F.IsEquivalence) : Admissible F G :=
  Or.inl hF.isLocalScDiffeo_obj

/-- If `G` is an equivalence, the weak fibred product of any `F` and `G` is an ep-groupoid. -/
theorem Admissible.of_isEquivalence_right (hG : G.IsEquivalence) : Admissible F G :=
  Or.inr hG.isLocalScDiffeo_obj

/-! ### The projections and the natural transformation -/

variable (F G) in
/-- The projection `πX : X ×_Y Z → X`, `(x, ϕ, z) ↦ x`, `(h, ϕ, k) ↦ h` (2021 Theorem 10.2.2,
p. 477). -/
def projLeft (h : Admissible F G) : EpFunctor (epGroupoid F G h) X where
  obj := Obj.x
  mor := Mor.h
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ hc := h_comp hc
  mor_unit _ := rfl
  isScSmoothMap_obj := isScSmoothMap_x h
  isScSmoothMap_mor := isScSmoothMap_h h

variable (F G) in
/-- The projection `πZ : X ×_Y Z → Z`, `(x, ϕ, z) ↦ z`, `(h, ϕ, k) ↦ k` (2021 Theorem 10.2.2,
p. 477). -/
def projRight (h : Admissible F G) : EpFunctor (epGroupoid F G h) Z where
  obj := Obj.z
  mor := Mor.k
  src_mor _ := rfl
  tgt_mor _ := rfl
  mor_comp _ _ hc := k_comp hc
  mor_unit _ := rfl
  isScSmoothMap_obj := isScSmoothMap_z h
  isScSmoothMap_mor := isScSmoothMap_k h

@[simp] theorem projLeft_obj (h : Admissible F G) (p : Obj F G) : (projLeft F G h).obj p = p.x :=
  rfl
@[simp] theorem projLeft_mor (h : Admissible F G) (m : Mor F G) : (projLeft F G h).mor m = m.h :=
  rfl
@[simp] theorem projRight_obj (h : Admissible F G) (p : Obj F G) :
    (projRight F G h).obj p = p.z :=
  rfl
@[simp] theorem projRight_mor (h : Admissible F G) (m : Mor F G) :
    (projRight F G h).mor m = m.k :=
  rfl

variable (F G) in
/-- **The 2-commutativity of the square** (2021 proof of Theorem 10.2.2, p. 482):
`σ(x, ϕ, z) = ϕ` is a natural transformation `F ∘ πX → G ∘ πZ`; naturality is
`ϕ' ∘ F(h) = G(k) ∘ ϕ` for `(h, ϕ, k) : (x, ϕ, z) → (x', ϕ', z')`. -/
def natTrans (h : Admissible F G) :
    EpNatTrans (F.comp (projLeft F G h)) (G.comp (projRight F G h)) where
  app := Obj.φ
  isScSmoothMap_app := isScSmoothMap_φ h
  src_app p := p.src_φ
  tgt_app p := p.tgt_φ
  naturality m := conj_comp_mor m.src_φ m.tgt_φ

@[simp] theorem natTrans_app (h : Admissible F G) (p : Obj F G) : (natTrans F G h).app p = p.φ :=
  rfl

/-- `F ∘ πX ≃ G ∘ πZ`, for any `F` and `G` for which the weak fibred product is defined. -/
theorem naturallyEquivalent (h : Admissible F G) :
    (F.comp (projLeft F G h)).NaturallyEquivalent (G.comp (projRight F G h)) :=
  ⟨natTrans F G h⟩

/-! ### `πZ` and `πX` are equivalences -/

/-- **`πZ` is an equivalence when `F` is one** (2021 proof of Theorem 10.2.2, pp. 481–482): full
and faithful (the unique morphism over `k : z → z'` is `(h, ϕ, k)` with
`F(h) = ϕ'⁻¹ ∘ G(k) ∘ ϕ`), essentially surjective, and a local sc-diffeomorphism on objects, so
Lemma 10.1.2 applies. -/
theorem isEquivalence_projRight (hF : F.IsEquivalence) (h : Admissible F G) :
    (projRight F G h).IsEquivalence := by
  refine EpFunctor.lemma_10_1_2 _ { faithful := ?_, full := ?_, essSurj := ?_ }
    (isLocalScDiffeo_z h hF.isLocalScDiffeo_obj)
  · refine (GroupoidFunctor.faithful_iff _).2 fun m m' hs ht he => ?_
    have hx : X.src m.h = X.src m'.h := congrArg Obj.x hs
    have hφ : m.φ = m'.φ := congrArg Obj.φ hs
    have hx' : X.tgt m.h = X.tgt m'.h := congrArg Obj.x ht
    have hc : conj F G m.h m.φ m.k = conj F G m'.h m'.φ m'.k := congrArg Obj.φ ht
    have hk : m.k = m'.k := he
    have a₁ : Y.src (conj F G m.h m.φ m.k) = Y.tgt (F.mor m.h) := by
      rw [src_conj m.src_φ m.tgt_φ, F.tgt_mor]
    have a₂ : Y.src (conj F G m.h m.φ m.k) = Y.tgt (F.mor m'.h) := by
      rw [src_conj m.src_φ m.tgt_φ, F.tgt_mor, hx']
    have he' : Y.comp (conj F G m.h m.φ m.k) (F.mor m.h) =
        Y.comp (conj F G m.h m.φ m.k) (F.mor m'.h) := by
      rw [conj_comp_mor m.src_φ m.tgt_φ, hc, conj_comp_mor m'.src_φ m'.tgt_φ, hk, hφ]
    exact Mor.ext (hF.mor_injective hx hx' (GroupoidStr.comp_left_cancel a₁ a₂ he')) hφ hk
  · refine (GroupoidFunctor.full_iff _).2 fun p p' k hs ht => ?_
    have hs : Z.src k = p.z := hs
    have ht : Z.tgt k = p'.z := ht
    have e₁ : Y.src (Y.inv p'.φ) = Y.tgt (G.mor k) := by
      rw [Y.src_inv, G.tgt_mor, ht, p'.tgt_φ]
    have e₂ : Y.src (G.mor k) = Y.tgt p.φ := by rw [G.src_mor, hs, p.tgt_φ]
    have e₃ : Y.src (Y.comp (Y.inv p'.φ) (G.mor k)) = Y.tgt p.φ := by
      rw [Y.src_comp _ _ e₁, e₂]
    have e₄ : Y.src p'.φ = Y.tgt (Y.comp (Y.inv p'.φ) (G.mor k)) := by
      rw [Y.tgt_comp _ _ e₁, Y.tgt_inv]
    have hψs : Y.src (Y.comp (Y.comp (Y.inv p'.φ) (G.mor k)) p.φ) = F.obj p.x := by
      rw [Y.src_comp _ _ e₃, p.src_φ]
    have hψt : Y.tgt (Y.comp (Y.comp (Y.inv p'.φ) (G.mor k)) p.φ) = F.obj p'.x := by
      rw [Y.tgt_comp _ _ e₃, Y.tgt_comp _ _ e₁, Y.tgt_inv, p'.src_φ]
    obtain ⟨h₀, h₀s, h₀t, h₀e⟩ := hF.exists_mor_eq hψs hψt
    have h₁ : Y.src p.φ = F.obj (X.src h₀) := by rw [h₀s, p.src_φ]
    have h₂ : Y.tgt p.φ = G.obj (Z.src k) := by rw [hs, p.tgt_φ]
    refine ⟨Mor.mk F G h₀ p.φ k h₁ h₂, Obj.ext h₀s rfl hs, Obj.ext h₀t ?_ ht, rfl⟩
    have hcancel : Y.comp p'.φ (Y.comp (Y.inv p'.φ) (G.mor k)) = G.mor k := by
      have := GroupoidStr.inv_comp_cancel_left (G := Y.toGroupoidStr) (φ := Y.inv p'.φ) e₁
      rwa [GroupoidStr.inv_inv] at this
    change conj F G h₀ p.φ k = p'.φ
    refine GroupoidStr.comp_right_cancel (G := Y.toGroupoidStr) (φ := F.mor h₀) ?_ ?_ ?_
    · rw [src_conj h₁ h₂, F.tgt_mor]
    · rw [F.tgt_mor, h₀t, p'.src_φ]
    · rw [conj_comp_mor h₁ h₂, h₀e, ← Y.comp_assoc _ _ _ e₄ e₃, hcancel]
  · refine (GroupoidFunctor.essSurj_iff _).2 fun z => ?_
    obtain ⟨x, ψ, hs, ht⟩ := hF.exists_iso (G.obj z)
    exact ⟨Obj.mk F G x ψ z hs ht, Z.unit z, Z.src_unit z, Z.tgt_unit z⟩

/-- **`πX` is an equivalence when `G` is one** (2021 p. 478, the case "`G` an equivalence
instead"): the unique morphism over `h : x → x'` is `(h, ϕ, k)` with `G(k) = ϕ' ∘ F(h) ∘ ϕ⁻¹`. -/
theorem isEquivalence_projLeft (hG : G.IsEquivalence) (h : Admissible F G) :
    (projLeft F G h).IsEquivalence := by
  refine EpFunctor.lemma_10_1_2 _ { faithful := ?_, full := ?_, essSurj := ?_ }
    (isLocalScDiffeo_x h hG.isLocalScDiffeo_obj)
  · refine (GroupoidFunctor.faithful_iff _).2 fun m m' hs ht he => ?_
    have hz : Z.src m.k = Z.src m'.k := congrArg Obj.z hs
    have hφ : m.φ = m'.φ := congrArg Obj.φ hs
    have hz' : Z.tgt m.k = Z.tgt m'.k := congrArg Obj.z ht
    have hc : conj F G m.h m.φ m.k = conj F G m'.h m'.φ m'.k := congrArg Obj.φ ht
    have hh : m.h = m'.h := he
    have a₁ : Y.src (G.mor m.k) = Y.tgt m.φ := by rw [G.src_mor, m.tgt_φ]
    have a₂ : Y.src (G.mor m'.k) = Y.tgt m.φ := by rw [G.src_mor, m.tgt_φ, hz]
    have he' : Y.comp (G.mor m.k) m.φ = Y.comp (G.mor m'.k) m.φ := by
      rw [← conj_comp_mor m.src_φ m.tgt_φ, hc, hh, conj_comp_mor m'.src_φ m'.tgt_φ, hφ]
    exact Mor.ext hh hφ (hG.mor_injective hz hz' (GroupoidStr.comp_right_cancel a₁ a₂ he'))
  · refine (GroupoidFunctor.full_iff _).2 fun p p' k hs ht => ?_
    have hs : X.src k = p.x := hs
    have ht : X.tgt k = p'.x := ht
    have e₁ : Y.src p'.φ = Y.tgt (F.mor k) := by rw [F.tgt_mor, ht, p'.src_φ]
    have e₂ : Y.src (Y.comp p'.φ (F.mor k)) = Y.tgt (Y.inv p.φ) := by
      rw [Y.src_comp _ _ e₁, F.src_mor, hs, Y.tgt_inv, p.src_φ]
    have hψs : Y.src (Y.comp (Y.comp p'.φ (F.mor k)) (Y.inv p.φ)) = G.obj p.z := by
      rw [Y.src_comp _ _ e₂, Y.src_inv, p.tgt_φ]
    have hψt : Y.tgt (Y.comp (Y.comp p'.φ (F.mor k)) (Y.inv p.φ)) = G.obj p'.z := by
      rw [Y.tgt_comp _ _ e₂, Y.tgt_comp _ _ e₁, p'.tgt_φ]
    obtain ⟨k₀, k₀s, k₀t, k₀e⟩ := hG.exists_mor_eq hψs hψt
    have h₁ : Y.src p.φ = F.obj (X.src k) := by rw [hs, p.src_φ]
    have h₂ : Y.tgt p.φ = G.obj (Z.src k₀) := by rw [k₀s, p.tgt_φ]
    refine ⟨Mor.mk F G k p.φ k₀ h₁ h₂, Obj.ext hs rfl k₀s, Obj.ext ht ?_ k₀t, rfl⟩
    have hcancel : Y.comp (Y.comp (Y.comp p'.φ (F.mor k)) (Y.inv p.φ)) p.φ =
        Y.comp p'.φ (F.mor k) := by
      have := GroupoidStr.comp_inv_cancel_right (G := Y.toGroupoidStr) (φ := Y.inv p.φ) e₂
      rwa [GroupoidStr.inv_inv] at this
    change conj F G k p.φ k₀ = p'.φ
    refine GroupoidStr.comp_right_cancel (G := Y.toGroupoidStr) (φ := F.mor k) ?_ e₁ ?_
    · rw [src_conj h₁ h₂, F.tgt_mor]
    · rw [conj_comp_mor h₁ h₂, k₀e, hcancel]
  · refine (GroupoidFunctor.essSurj_iff _).2 fun x => ?_
    obtain ⟨z, ψ, hs, ht⟩ := hG.exists_iso (F.obj x)
    have h₁ : Y.src (Y.inv ψ) = F.obj x := by rw [Y.src_inv, ht]
    have h₂ : Y.tgt (Y.inv ψ) = G.obj z := by rw [Y.tgt_inv, hs]
    exact ⟨Obj.mk F G x (Y.inv ψ) z h₁ h₂, X.unit x, X.src_unit x, X.tgt_unit x⟩

/-- `d_{X ×_Y Z}(x, ϕ, z) = d_Z(z)` when `F` is an equivalence (2021 p. 482). -/
theorem degIndex_eq_z (hF : F.IsEquivalence) (h : Admissible F G) (p : Obj F G) :
    (epGroupoid F G h).PObj.degIndex p = Z.PObj.degIndex p.z :=
  ((isEquivalence_projRight hF h).degIndex_obj p).symm

/-- `d_{X ×_Y Z}(x, ϕ, z) = d_X(x)` when `G` is an equivalence (2021 p. 478). -/
theorem degIndex_eq_x (hG : G.IsEquivalence) (h : Admissible F G) (p : Obj F G) :
    (epGroupoid F G h).PObj.degIndex p = X.PObj.degIndex p.x :=
  ((isEquivalence_projLeft hG h).degIndex_obj p).symm

/-! ### Theorem 10.2.2 and Remark 10.2.3 -/

/-- **2021 Theorem 10.2.2, p. 477 (2017: Theorem 10.2, p. 343)**, the claims after the first
(the first, that `X ×_Y Z` is an ep-groupoid, is `epGroupoid`): for an equivalence `F : X → Y` and
an sc-smooth functor `G : Z → Y`, the projection `πZ` is an equivalence, `F ∘ πX ≃ G ∘ πZ`,
`d_{X ×_Y Z}(x, ϕ, z) = d_Z(z)`, and if `Z` is tame, or has a paracompact orbit space, so has
`X ×_Y Z`. -/
theorem theorem_10_2_2 (hF : F.IsEquivalence) :
    (projRight F G (.of_isEquivalence_left hF)).IsEquivalence ∧
    (F.comp (projLeft F G (.of_isEquivalence_left hF))).NaturallyEquivalent
      (G.comp (projRight F G (.of_isEquivalence_left hF))) ∧
    (∀ p : Obj F G,
      (epGroupoid F G (.of_isEquivalence_left hF)).PObj.degIndex p = Z.PObj.degIndex p.z) ∧
    (Z.IsTame → (epGroupoid F G (.of_isEquivalence_left hF)).IsTame) ∧
    (Z.HasParacompactOrbitSpace →
      (epGroupoid F G (.of_isEquivalence_left hF)).HasParacompactOrbitSpace) :=
  ⟨isEquivalence_projRight hF _, naturallyEquivalent _, degIndex_eq_z hF _,
    (isEquivalence_projRight hF _).isTame_of_isTame,
    (isEquivalence_projRight hF _).hasParacompactOrbitSpace⟩

/-- **2021 Theorem 10.2.2, p. 478 (2017: Theorem 10.2, p. 343), the case `G` an equivalence**:
`X ×_Y Z` is an ep-groupoid, `πX` is an equivalence and `d_{X ×_Y Z}(x, ϕ, z) = d_X(x)`; as for
`F`, also `F ∘ πX ≃ G ∘ πZ`, and tameness and a paracompact orbit space pass from `X`. -/
theorem theorem_10_2_2_right (hG : G.IsEquivalence) :
    (projLeft F G (.of_isEquivalence_right hG)).IsEquivalence ∧
    (F.comp (projLeft F G (.of_isEquivalence_right hG))).NaturallyEquivalent
      (G.comp (projRight F G (.of_isEquivalence_right hG))) ∧
    (∀ p : Obj F G,
      (epGroupoid F G (.of_isEquivalence_right hG)).PObj.degIndex p = X.PObj.degIndex p.x) ∧
    (X.IsTame → (epGroupoid F G (.of_isEquivalence_right hG)).IsTame) ∧
    (X.HasParacompactOrbitSpace →
      (epGroupoid F G (.of_isEquivalence_right hG)).HasParacompactOrbitSpace) :=
  ⟨isEquivalence_projLeft hG _, naturallyEquivalent _, degIndex_eq_x hG _,
    (isEquivalence_projLeft hG _).isTame_of_isTame,
    (isEquivalence_projLeft hG _).hasParacompactOrbitSpace⟩

/-- **2021 Theorem 10.2.2, p. 478 (2017: Theorem 10.2, p. 343), the case of two equivalences**:
`d_X(x) = d_{X ×_Y Z}(x, ϕ, z) = d_Z(z)`. -/
theorem theorem_10_2_2_both (hF : F.IsEquivalence) (hG : G.IsEquivalence) (p : Obj F G) :
    X.PObj.degIndex p.x = (epGroupoid F G (.of_isEquivalence_left hF)).PObj.degIndex p ∧
      (epGroupoid F G (.of_isEquivalence_left hF)).PObj.degIndex p = Z.PObj.degIndex p.z :=
  ⟨(degIndex_eq_x hG _ p).symm, degIndex_eq_z hF _ p⟩

/-- **2021 Remark 10.2.3, pp. 482–483 (2017: Remark 10.2, p. 347)**: for equivalences
`F : A → X` and `H : B → X` (here `F : X → Y` and `G : Z → Y`) the weak fibred product is an
ep-groupoid, both projections are equivalences, and `τ(a, ϕ, b) = ϕ` is a natural transformation
`F ∘ πA → H ∘ πB`. -/
theorem remark_10_2_3 (hF : F.IsEquivalence) (hG : G.IsEquivalence) :
    (projLeft F G (.of_isEquivalence_left hF)).IsEquivalence ∧
    (projRight F G (.of_isEquivalence_left hF)).IsEquivalence ∧
    ∃ τ : EpNatTrans (F.comp (projLeft F G (.of_isEquivalence_left hF)))
      (G.comp (projRight F G (.of_isEquivalence_left hF))), ∀ p, τ.app p = p.φ :=
  ⟨isEquivalence_projLeft hG _, isEquivalence_projRight hF _, natTrans F G _, fun _ => rfl⟩

end WeakFibredProduct

end WFPTheorem

/-! ### Witnesses -/

namespace WeakFibredProduct.Examples

open EpGroupoid.Examples

/-- **Witness for Theorem 10.2.2**: the weak fibred product of the equivalence `pairToPoint`
(the pair groupoid of `ℤ` over the point) and the identity of the point is a nonempty
ep-groupoid, and its projection to the point is an equivalence. -/
theorem theorem_10_2_2_pairToPoint :
    Nonempty (Obj pairToPoint (EpFunctor.id pointEpGroupoid)) ∧
    (projRight pairToPoint (EpFunctor.id pointEpGroupoid)
      (.of_isEquivalence_left isEquivalence_pairToPoint)).IsEquivalence :=
  ⟨⟨Obj.mk _ _ (0 : ℤ) () () rfl rfl⟩, (theorem_10_2_2 isEquivalence_pairToPoint).1⟩

/-- **Witness for Remark 10.2.3**: the weak fibred product of the identity and of `-id`
(`negFunctor`) of `ℤ/2 ⋉ ℝ²` is nonempty, and both projections are equivalences. -/
theorem remark_10_2_3_negFunctor :
    Nonempty (Obj (EpFunctor.id pointReflectionEpGroupoid) negFunctor) ∧
    (projLeft (EpFunctor.id pointReflectionEpGroupoid) negFunctor
      (.of_isEquivalence_left (EpFunctor.IsEquivalence.id _))).IsEquivalence ∧
    (projRight (EpFunctor.id pointReflectionEpGroupoid) negFunctor
      (.of_isEquivalence_left (EpFunctor.IsEquivalence.id _))).IsEquivalence := by
  obtain ⟨h₁, h₂, -⟩ := remark_10_2_3 (EpFunctor.IsEquivalence.id pointReflectionEpGroupoid)
    isEquivalence_negFunctor
  refine ⟨⟨Obj.mk _ _ 0 (pointReflectionEpGroupoid.unit 0) 0
    (pointReflectionEpGroupoid.src_unit 0) ?_⟩, h₁, h₂⟩
  exact (pointReflectionEpGroupoid.tgt_unit 0).trans neg_zero.symm

end WeakFibredProduct.Examples

end Polyfold
