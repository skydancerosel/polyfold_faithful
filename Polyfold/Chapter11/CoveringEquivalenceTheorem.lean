import Polyfold.Chapter11.CoveringEquivalence

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021; 2017 arXiv 1707.08941),
Part II, Chapter 11, §11.6 "Coverings and Equivalences" (pp. 553–561; 2017: pp. 405–410):
**Theorem 11.6.6** (2017: Theorem 11.10) with its proof, steps (A)–(E).

# The weak fibred product of proper coverings

## The text, paraphrased

(Theorem 11.6.6, p. 555 (2017: Theorem 11.10, p. 405)) Let `Γ = (Ψ, Φ) : F → F'` be an
equivalence of proper coverings and `(ζ, ξ) : F'' → F'` an sc-smooth functor of proper
coverings, `P = Y ×_{Y'} Y''`, `Q = X ×_{X'} X''` the weak fibred products of Theorem 10.2.2, and
`H : P → Q` given by `F`, `F'`, `F''` componentwise on objects and on morphisms.  Then (1) `H` is
well-defined and a proper covering functor; (2) `(π_{Y''}, π_{X''}) : H → F''` is an equivalence
of proper coverings; (3) `(Ψ ∘ π_Y, Φ ∘ π_X)` and `(ζ ∘ π_{Y''}, ξ ∘ π_{X''})` are naturally
equivalent.  If `X''` is tame, so are `P` and `Q`; if `(ζ, ξ)` is an equivalence, so is
`(π_Y, π_X)`.

*Proof (text, pp. 556–561)*: (A) `H` maps the object space of `P` onto that of `Q` (using that
`Ψ` maps `Y(x)` onto `Y'(Φ(x))`) and is a local sc-diffeomorphism on objects; (B) the map `α` of
`H` is an sc-diffeomorphism, its inverse built from those of `F` and `F''`; (C) fibres of `H` are
finite and evenly covered, by an argument with sequences and the properness of the ep-groupoid
`Y'`; (D) `π_{Y''}` maps the fibres `P(q)` bijectively onto `Y''(π_{X''}(q))`, and with Theorem
10.2.2 `(π_{Y''}, π_{X''})` is an equivalence; (E) `(y, ψ', y'') ↦ ψ'` and `(x, φ', x'') ↦ φ'` give
the natural equivalence (3); tameness follows as in Theorem 10.2.2.

## What is formalized

* `ProperCoveringHom.hFunctor Γ Λ hP hQ : P → Q` (`hObj`, `hMor`; well-defined by construction),
  for `Λ = (ζ, ξ)` and admissibility proofs `hP`, `hQ` of the weak fibred products.
* Step (A): `surjective_hObj`, `isLocalScDiffeo_hObj`.  Step (B): `isScDiffeo_fibredMap_hFunctor`.
  Step (C): `finite_fiber_hObj`, `isProperMap_hObj` (`H` is a proper map on objects), and the
  general facts `MPolyfold.IsLocalScDiffeo.evenlyCovered_of_isProperMap` (a proper local
  sc-diffeomorphism with finite fibre over `q` is evenly covered over a neighbourhood of `q`) and
  `EpFunctor.IsProperCovering.isProperMap` (the object map of a proper covering is a proper map).
  Together: `isProperCovering_hFunctor_of`.
* Steps (D), (E): `projLeftHom`, `projRightHom` (functors of proper coverings), `natTransProj`.
* **Theorem 11.6.6**: `ProperCoveringHom.theorem_11_6_6`, all claims: (1), (2), (3), tameness of
  `P` and `Q`, and the case `(ζ, ξ)` an equivalence.
* Witness (namespace `Polyfold.CoveringEquivalence.Examples`): `theorem_11_6_6_pairToPoint`: the
  equivalence `pairToPointCovering` and the identity of the identity covering of the point
  satisfy all hypotheses; `P` is nonempty and `H` is a proper covering.

## What the text leaves implicit, and the choices made

* Step (C) is proved without sequences: `H` is shown to be a proper map on objects (an
  ultrafilter argument from properness of the object maps of `F` and `F''` and continuity of the
  inverse of the map `α` of `F'`), and a proper local sc-diffeomorphism with finite fibres is
  evenly covered in general (Hausdorffness and closedness of proper maps).
* Step (D): the fibre bijection of `π_{Y''}` is not checked by hand; by
  `isFiberBijective_of_isEquivalence` (`CoveringEquivalence.lean`) it follows from `π_{Y''}` and
  `π_{X''}` being equivalences (Theorem 10.2.2, `isEquivalence_projRight`).
* Tameness of `Y''` from that of `X''` (the text's "trivially") is
  `IsLocalScDiffeo.isTame` applied to the object map of `F''`.
* The admissibility proofs are supplied by `Admissible.of_isEquivalence_left`; they are
  propositions, so the weak fibred products do not depend on them.
-/

set_option maxSynthPendingDepth 3

open Set Function Filter Topology CategoryTheory

noncomputable section

namespace Polyfold

universe u v w

/-- A map into a sub-M-polyfold which is sc-smooth into the ambient M-polyfold is sc-smooth
into it (a copy of the private lemma of `Chapter8/ProperCovering.lean`). -/
private theorem isScSmoothOn_subPolyfold_of_val' {M : Type*} [TopologicalSpace M] [T2Space M]
    [ParacompactSpace M] {PM : MPolyfold M} {N : Type*} [TopologicalSpace N] [T2Space N]
    [ParacompactSpace N] {PN : MPolyfold N} {A : Set N} (hA : PN.IsSubMPolyfold A)
    [ParacompactSpace A] {f : M → A} {U : Set M}
    (hf : PM.IsScSmoothOn PN (fun x => (f x : N)) U) :
    PM.IsScSmoothOn (MPolyfold.subPolyfold hA) f U := by
  refine MPolyfold.IsScSmoothOn.of_locally hf.isOpen fun x hx => ?_
  set d := hA.data (f x).2
  have hU' : IsOpen (U ∩ (fun x => (f x : N)) ⁻¹' d.V) :=
    hf.continuousOn.isOpen_inter_preimage hf.isOpen d.isOpen
  refine ⟨_, hU', ⟨hx, hA.mem_data_V (f x).2⟩, inter_subset_left, ?_⟩
  refine (MPolyfold.IsScSmoothOn.comp (MPolyfold.subPolyfold_retraction_isScSmooth hA d (f x))
    (hf.mono hU' inter_subset_left) fun y hy => hy.2).congr fun y hy => Subtype.ext ?_
  simp only [Function.comp_apply]
  rw [d.retractInto_val (f x) hy.2]
  exact d.apply_eq_self ⟨(f y).2, hy.2⟩

/-! ### Proper local sc-diffeomorphisms are evenly covered -/

section EvenlyCovered

variable {M : Type u} [TopologicalSpace M] [T2Space M] [ParacompactSpace M] {PM : MPolyfold M}
  {N : Type v} [TopologicalSpace N] [T2Space N] [ParacompactSpace N] {PN : MPolyfold N}

/-- An sc-diffeomorphism `U → V` restricts to `U ∩ f⁻¹(W) → W` for open `W ⊆ V`. -/
theorem MPolyfold.IsScDiffeoOn.restrictTarget {f : M → N} {g : N → M} {U : Set M} {V W : Set N}
    (h : PM.IsScDiffeoOn PN f g U V) (hW : IsOpen W) (hWV : W ⊆ V) :
    PM.IsScDiffeoOn PN f g (U ∩ f ⁻¹' W) W :=
  (h.symm.restrict hW hWV).symm

/-- **A proper local sc-diffeomorphism with a finite fibre is evenly covered there**: disjoint
sheets around the points of `f⁻¹(q)`, and a neighbourhood `U ∋ q` with `f⁻¹(U)` inside their
union (`f` is a closed map). -/
theorem MPolyfold.IsLocalScDiffeo.evenlyCovered_of_isProperMap {f : M → N}
    (hf : PM.IsLocalScDiffeo PN f) (hp : IsProperMap f) {q : N} (hfin : (f ⁻¹' {q}).Finite) :
    ∃ (U : Set N) (V : M → Set M) (σ : M → N → M), IsOpen U ∧ q ∈ U ∧
      (f ⁻¹' {q}).PairwiseDisjoint V ∧
      (∀ p ∈ f ⁻¹' {q}, p ∈ V p ∧ PM.IsScDiffeoOn PN f (σ p) (V p) U) ∧
      f ⁻¹' U = ⋃ p ∈ f ⁻¹' {q}, V p := by
  choose W W' g hpW hd using hf
  obtain ⟨D, hD, hdisj⟩ := hfin.t2_separation
  -- the sheets `A p = W p ∩ D p` and their images `B p`
  have hAo : ∀ p, IsOpen (W p ∩ D p) := fun p => (hd p).isOpen_source.inter (hD p).2
  have hdA : ∀ p, PM.IsScDiffeoOn PN f (g p) (W p ∩ D p) (W' p ∩ g p ⁻¹' (W p ∩ D p)) :=
    fun p => (hd p).restrict (hAo p) inter_subset_left
  have hqB : ∀ p ∈ f ⁻¹' {q}, q ∈ W' p ∩ g p ⁻¹' (W p ∩ D p) := fun p hp => by
    have hfp : f p = q := hp
    have h1 := (hd p).left_inv p (hpW p)
    rw [hfp] at h1
    refine ⟨?_, ?_⟩
    · rw [← hfp]
      exact (hd p).mapsTo (hpW p)
    · change g p q ∈ W p ∩ D p
      rw [h1]
      exact ⟨hpW p, (hD p).1⟩
  set O := ⋃ p ∈ f ⁻¹' {q}, W p ∩ D p
  have hO : IsOpen O := isOpen_biUnion fun p _ => hAo p
  have hK : IsClosed (f '' Oᶜ) := hp.isClosedMap _ hO.isClosed_compl
  have hqK : q ∉ f '' Oᶜ := by
    rintro ⟨w, hw, hwq⟩
    exact hw (mem_biUnion (x := w) hwq ⟨hpW w, (hD w).1⟩)
  set U := (⋂ p ∈ f ⁻¹' {q}, W' p ∩ g p ⁻¹' (W p ∩ D p)) ∩ (f '' Oᶜ)ᶜ
  have hUo : IsOpen U :=
    (hfin.isOpen_biInter fun p _ => (hdA p).isOpen_target).inter hK.isOpen_compl
  have hqU : q ∈ U := ⟨mem_iInter₂.2 hqB, hqK⟩
  have hUB : ∀ p ∈ f ⁻¹' {q}, U ⊆ W' p ∩ g p ⁻¹' (W p ∩ D p) := fun p hp _ hu =>
    (mem_iInter₂.1 hu.1) p hp
  refine ⟨U, fun p => (W p ∩ D p) ∩ f ⁻¹' U, g, hUo, hqU, ?_, fun p hp => ?_, ?_⟩
  · exact hdisj.mono fun p => inter_subset_left.trans inter_subset_right
  · refine ⟨⟨⟨hpW p, (hD p).1⟩, ?_⟩, (hdA p).restrictTarget hUo (hUB p hp)⟩
    change f p ∈ U
    rw [show f p = q from hp]
    exact hqU
  · ext w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · have hwO : w ∈ O := by
        by_contra hc
        exact hw.2 ⟨w, hc, rfl⟩
      obtain ⟨p, hp, hwp⟩ := mem_iUnion₂.1 hwO
      exact mem_iUnion₂.2 ⟨p, hp, hwp, hw⟩
    · obtain ⟨p, -, hwp⟩ := mem_iUnion₂.1 hw
      exact hwp.2

end EvenlyCovered

/-! ### Proper covering functors are proper maps on objects -/

section ProperMap

variable {ObjY MorY : Type u} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type v} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX} {F : EpFunctor Y X}

/-- **A proper covering functor is a proper map on objects**: an ultrafilter converging to `x`
after `F` contains one of the finitely many sheets `U(y)`, `y ∈ F⁻¹(x)`, and on it the identity is
`σ_y ∘ F`, so it converges to `σ_y(x) = y`. -/
theorem EpFunctor.IsProperCovering.isProperMap (hF : F.IsProperCovering) : IsProperMap F.obj := by
  refine isProperMap_iff_ultrafilter.2 ⟨hF.isLocalScDiffeo.continuous, fun 𝒰 x hx => ?_⟩
  obtain ⟨U, V, σ, hUo, hxU, -, hV, hcov⟩ := hF.evenlyCovered x
  have hU𝒰 : F.obj ⁻¹' U ∈ 𝒰 := hx (hUo.mem_nhds hxU)
  rw [hcov] at hU𝒰
  obtain ⟨y, hy, hy𝒰⟩ := (Ultrafilter.finite_biUnion_mem_iff (hF.finite_fiber x)).1 hU𝒰
  obtain ⟨hyV, hd⟩ := hV y hy
  have hyx : F.obj y = x := hy
  have hσy : σ y x = y := by rw [← hyx, hd.left_inv y hyV]
  refine ⟨y, hyx, ?_⟩
  have hc : Tendsto (σ y) (𝓝 x) (𝓝 (σ y x)) :=
    hd.isScSmoothOn_inv.continuousOn.continuousAt (hUo.mem_nhds hxU)
  have h1 : Tendsto (σ y ∘ F.obj) 𝒰 (𝓝 (σ y x)) := hc.comp hx
  rw [hσy] at h1
  have h2 : (σ y ∘ F.obj) =ᶠ[(𝒰 : Filter ObjY)] fun w => w :=
    Filter.mem_of_superset hy𝒰 fun w hw => (hd.left_inv w hw : _)
  exact (h1.congr' h2 : Tendsto (fun w => w) 𝒰 (𝓝 y))

end ProperMap

/-! ### The functor `H : Y ×_{Y'} Y'' → X ×_{X'} X''` -/

section HFunctor

universe u₁ u₂ u₃ u₄ u₅ u₆

variable {ObjY MorY : Type u₁} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type u₂} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY' MorY' : Type u₃} [TopologicalSpace ObjY'] [T2Space ObjY'] [ParacompactSpace ObjY']
  [TopologicalSpace MorY'] [T2Space MorY'] [ParacompactSpace MorY']
  {ObjX' MorX' : Type u₄} [TopologicalSpace ObjX'] [T2Space ObjX'] [ParacompactSpace ObjX']
  [TopologicalSpace MorX'] [T2Space MorX'] [ParacompactSpace MorX']
  {ObjY'' MorY'' : Type u₅} [TopologicalSpace ObjY''] [T2Space ObjY''] [ParacompactSpace ObjY'']
  [TopologicalSpace MorY''] [T2Space MorY''] [ParacompactSpace MorY'']
  {ObjX'' MorX'' : Type u₆} [TopologicalSpace ObjX''] [T2Space ObjX''] [ParacompactSpace ObjX'']
  [TopologicalSpace MorX''] [T2Space MorX''] [ParacompactSpace MorX'']
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}
  {Y' : EpGroupoid ObjY' MorY'} {X' : EpGroupoid ObjX' MorX'}
  {Y'' : EpGroupoid ObjY'' MorY''} {X'' : EpGroupoid ObjX'' MorX''}
  {F : EpFunctor Y X} {F' : EpFunctor Y' X'} {F'' : EpFunctor Y'' X''}
  (Γ : ProperCoveringHom F F') (Λ : ProperCoveringHom F'' F')

namespace ProperCoveringHom

open WeakFibredProduct

/-- `H(y, ψ', y'') = (F(y), F'(ψ'), F''(y''))` (11.18). -/
def hObj (p : Obj Γ.Ψ Λ.Ψ) : Obj Γ.Φ Λ.Φ :=
  Obj.mk Γ.Φ Λ.Φ (F.obj p.x) (F'.mor p.φ) (F''.obj p.z)
    (by rw [F'.src_mor, p.src_φ, ← Γ.comm_obj]) (by rw [F'.tgt_mor, p.tgt_φ, ← Λ.comm_obj])

/-- `H(h, ψ', h'') = (F(h), F'(ψ'), F''(h''))` (11.19). -/
def hMor (m : Mor Γ.Ψ Λ.Ψ) : Mor Γ.Φ Λ.Φ :=
  Mor.mk Γ.Φ Λ.Φ (F.mor m.h) (F'.mor m.φ) (F''.mor m.k)
    (by rw [F'.src_mor, m.src_φ, ← Γ.comm_obj, F.src_mor])
    (by rw [F'.tgt_mor, m.tgt_φ, ← Λ.comm_obj, F''.src_mor])

variable {Γ Λ}

@[simp] theorem hObj_x (p : Obj Γ.Ψ Λ.Ψ) : (hObj Γ Λ p).x = F.obj p.x := rfl
@[simp] theorem hObj_φ (p : Obj Γ.Ψ Λ.Ψ) : (hObj Γ Λ p).φ = F'.mor p.φ := rfl
@[simp] theorem hObj_z (p : Obj Γ.Ψ Λ.Ψ) : (hObj Γ Λ p).z = F''.obj p.z := rfl
@[simp] theorem hMor_h (m : Mor Γ.Ψ Λ.Ψ) : (hMor Γ Λ m).h = F.mor m.h := rfl
@[simp] theorem hMor_φ (m : Mor Γ.Ψ Λ.Ψ) : (hMor Γ Λ m).φ = F'.mor m.φ := rfl
@[simp] theorem hMor_k (m : Mor Γ.Ψ Λ.Ψ) : (hMor Γ Λ m).k = F''.mor m.k := rfl

/-- `F'` carries `ζ(h'') ∘ ψ' ∘ Ψ(h)⁻¹` to `ξ(F''(h'')) ∘ F'(ψ') ∘ Φ(F(h))⁻¹`. -/
theorem mor_conj {h : MorY} {φ : MorY'} {k : MorY''} (h₁ : Y'.src φ = Γ.Ψ.obj (Y.src h))
    (h₂ : Y'.tgt φ = Λ.Ψ.obj (Y''.src k)) :
    F'.mor (conj Γ.Ψ Λ.Ψ h φ k) = conj Γ.Φ Λ.Φ (F.mor h) (F'.mor φ) (F''.mor k) := by
  have e₁ : Y'.src (Λ.Ψ.mor k) = Y'.tgt φ := by rw [Λ.Ψ.src_mor, h₂]
  have e₂ : Y'.src (Y'.comp (Λ.Ψ.mor k) φ) = Y'.tgt (Y'.inv (Γ.Ψ.mor h)) := by
    rw [Y'.src_comp _ _ e₁, Y'.tgt_inv, Γ.Ψ.src_mor, h₁]
  unfold conj
  rw [F'.mor_comp _ _ e₂, F'.mor_comp _ _ e₁, GroupoidFunctor.mor_inv, ← Γ.comm_mor,
    ← Λ.comm_mor]

theorem hMor_src (m : Mor Γ.Ψ Λ.Ψ) : src (hMor Γ Λ m) = hObj Γ Λ (src m) :=
  Obj.ext (F.src_mor _) rfl (F''.src_mor _)

theorem hMor_tgt (m : Mor Γ.Ψ Λ.Ψ) : tgt (hMor Γ Λ m) = hObj Γ Λ (tgt m) :=
  Obj.ext (F.tgt_mor _) (mor_conj m.src_φ m.tgt_φ).symm (F''.tgt_mor _)

variable (Γ Λ)

/-- **The functor `H : P → Q`** of Theorem 11.6.6 (2021 p. 554), for `P = Y ×_{Y'} Y''` and
`Q = X ×_{X'} X''` built from `Ψ, ζ` and `Φ, ξ`. -/
def hFunctor (hP : Admissible Γ.Ψ Λ.Ψ) (hQ : Admissible Γ.Φ Λ.Φ) :
    EpFunctor (epGroupoid Γ.Ψ Λ.Ψ hP) (epGroupoid Γ.Φ Λ.Φ hQ) where
  obj := hObj Γ Λ
  mor := hMor Γ Λ
  src_mor := hMor_src
  tgt_mor := hMor_tgt
  mor_comp m m' hc := by
    have hc' : src (hMor Γ Λ m) = tgt (hMor Γ Λ m') := by
      rw [hMor_src, hMor_tgt]; exact congrArg _ hc
    change hMor Γ Λ (WeakFibredProduct.comp m m') =
      WeakFibredProduct.comp (hMor Γ Λ m) (hMor Γ Λ m')
    refine Mor.ext ?_ ?_ ?_
    · rw [h_comp hc', hMor_h, h_comp hc]
      exact F.mor_comp _ _ (src_eq_tgt_iff.1 hc).1
    · rw [φ_comp hc', hMor_φ, φ_comp hc]; rfl
    · rw [k_comp hc', hMor_k, k_comp hc]
      exact F''.mor_comp _ _ (src_eq_tgt_iff.1 hc).2.2
  mor_unit p := Mor.ext (F.mor_unit _) rfl (F''.mor_unit _)
  isScSmoothMap_obj := isScSmoothOn_obj_of hQ (F.isScSmoothMap_obj.comp (isScSmoothMap_x hP))
    (F'.isScSmoothMap_mor.comp (isScSmoothMap_φ hP))
    (F''.isScSmoothMap_obj.comp (isScSmoothMap_z hP))
  isScSmoothMap_mor := isScSmoothOn_mor_of hQ (F.isScSmoothMap_mor.comp (isScSmoothMap_h hP))
    (F'.isScSmoothMap_mor.comp (isScSmoothMap_mφ hP))
    (F''.isScSmoothMap_mor.comp (isScSmoothMap_k hP))


/-! ### `H` is a proper covering functor -/

section HProper

variable {Γ Λ}

/-- **Step (A)**: `H` is surjective on objects (Theorem 11.6.6, p. 556). -/
theorem surjective_hObj (hF'' : F''.IsProperCovering) (hF' : F'.IsProperCovering)
    (hΓ : ∀ x, SurjOn Γ.Ψ.obj (F.obj ⁻¹' {x}) (F'.obj ⁻¹' {Γ.Φ.obj x})) :
    Surjective (hObj Γ Λ) := by
  intro q
  obtain ⟨y'', hy''⟩ := hF''.surjective q.z
  have ht : X'.tgt q.φ = F'.obj (Λ.Ψ.obj y'') := by rw [q.tgt_φ, ← hy'', Λ.comm_obj]
  obtain ⟨ψ', ⟨hψm, hψt⟩, -⟩ := hF'.existsUnique_lift_tgt ht
  have hs : F'.obj (Y'.src ψ') = Γ.Φ.obj q.x := by rw [← F'.src_mor, hψm, q.src_φ]
  obtain ⟨y, hy, hyψ⟩ := hΓ q.x hs
  exact ⟨Obj.mk Γ.Ψ Λ.Ψ y ψ' y'' hyψ.symm hψt, Obj.ext hy hψm hy''⟩

/-- **Step (A)**: `H` is a local sc-diffeomorphism on objects (p. 556). -/
theorem isLocalScDiffeo_hObj (hP : Admissible Γ.Ψ Λ.Ψ) (hQ : Admissible Γ.Φ Λ.Φ)
    (hΨ : Y.PObj.IsLocalScDiffeo Y'.PObj Γ.Ψ.obj) (hΦ : X.PObj.IsLocalScDiffeo X'.PObj Γ.Φ.obj)
    (hF'' : F''.IsProperCovering) :
    (PObj Γ.Ψ Λ.Ψ hP).IsLocalScDiffeo (PObj Γ.Φ Λ.Φ hQ) (hObj Γ Λ) :=
  MPolyfold.IsLocalScDiffeo.of_comm (hFunctor Γ Λ hP hQ).continuous_obj'
    (isLocalScDiffeo_z hP hΨ) (isLocalScDiffeo_z hQ hΦ) hF''.isLocalScDiffeo fun _ => rfl

/-- **Step (C)**: the fibres of `H` on objects are finite (p. 559). -/
theorem finite_fiber_hObj (hF : F.IsProperCovering) (hF' : F'.IsProperCovering)
    (hF'' : F''.IsProperCovering) (q : Obj Γ.Φ Λ.Φ) : (hObj Γ Λ ⁻¹' {q}).Finite := by
  refine Finite.of_finite_image (f := fun p : Obj Γ.Ψ Λ.Ψ => (p.x, p.z))
    (((hF.finite_fiber q.x).prod (hF''.finite_fiber q.z)).subset ?_) ?_
  · rintro _ ⟨p, hp, rfl⟩
    have hp : hObj Γ Λ p = q := hp
    exact ⟨congrArg Obj.x hp, congrArg Obj.z hp⟩
  · intro p hp p' hp' he
    have hp : hObj Γ Λ p = q := hp
    have hp' : hObj Γ Λ p' = q := hp'
    have hx : p.x = p'.x := congrArg (fun a : ObjY × ObjY'' => a.1) he
    have hz : p.z = p'.z := congrArg (fun a : ObjY × ObjY'' => a.2) he
    have h₀ : X'.src (F'.mor p.φ) = F'.obj (Γ.Ψ.obj p.x) := by rw [F'.src_mor, p.src_φ]
    refine Obj.ext hx ((hF'.existsUnique_lift h₀).unique ⟨rfl, p.src_φ⟩ ⟨?_, ?_⟩) hz
    · exact (congrArg Obj.φ hp').trans (congrArg Obj.φ hp).symm
    · rw [p'.src_φ, hx]

/-- **Step (C)**: `H` is a proper map on objects. -/
theorem isProperMap_hObj (hF : F.IsProperCovering) (hF' : F'.IsProperCovering)
    (hF'' : F''.IsProperCovering) : IsProperMap (hObj Γ Λ) := by
  have hcont : Continuous (hObj Γ Λ) :=
    continuous_obj_of (F.continuous_obj'.comp continuous_x)
      (F'.continuous_mor.comp continuous_φ) (F''.continuous_obj'.comp continuous_z)
  refine isProperMap_iff_ultrafilter.2 ⟨hcont, fun 𝒰 q hq => ?_⟩
  -- the entries `y` and `y''`
  have hx : Tendsto F.obj (𝒰.map Obj.x : Filter ObjY) (𝓝 q.x) := by
    rw [Ultrafilter.coe_map, tendsto_map'_iff]
    exact (continuous_x.tendsto q).comp hq
  obtain ⟨y, hyq, hy⟩ := (isProperMap_iff_ultrafilter.1 hF.isProperMap).2 hx
  have hz : Tendsto F''.obj (𝒰.map Obj.z : Filter ObjY'') (𝓝 q.z) := by
    rw [Ultrafilter.coe_map, tendsto_map'_iff]
    exact (continuous_z.tendsto q).comp hq
  obtain ⟨y'', hy''q, hy''⟩ := (isProperMap_iff_ultrafilter.1 hF''.isProperMap).2 hz
  have hy : Tendsto Obj.x (𝒰 : Filter (Obj Γ.Ψ Λ.Ψ)) (𝓝 y) := by
    rw [Ultrafilter.coe_map] at hy; exact hy
  have hy'' : Tendsto Obj.z (𝒰 : Filter (Obj Γ.Ψ Λ.Ψ)) (𝓝 y'') := by
    rw [Ultrafilter.coe_map] at hy''; exact hy''
  -- the middle entry: `ψ' = α'⁻¹(F'(ψ'), s(ψ'))` depends continuously on `(F'(ψ'), Ψ(y))`
  let _ := MPolyfold.paracompactSpace_prod X'.PMor Y'.PObj
  let _ := (X'.PMor.prod Y'.PObj).paracompactSpace_subtype
    (MPolyfold.fibredProduct X'.src F'.obj)
  obtain ⟨g, hg⟩ := hF'.isScDiffeo_fibredMap
  have ha₀ : X'.src q.φ = F'.obj (Γ.Ψ.obj y) := by rw [q.src_φ, ← hyq, Γ.comm_obj]
  set a₀ : MPolyfold.fibredProduct X'.src F'.obj := ⟨(q.φ, Γ.Ψ.obj y), ha₀⟩
  have hgc : Continuous g := continuousOn_univ.1 hg.isScSmoothOn_inv.continuousOn
  have hfm : Tendsto (fun p : Obj Γ.Ψ Λ.Ψ => F'.fibredMap p.φ) 𝒰 (𝓝 a₀) := by
    refine tendsto_subtype_rng.2 ?_
    refine Tendsto.prodMk_nhds ((continuous_φ.tendsto q).comp hq) ?_
    exact ((Γ.Ψ.continuous_obj'.tendsto y).comp hy).congr fun p => p.src_φ.symm
  have hφ : Tendsto Obj.φ (𝒰 : Filter (Obj Γ.Ψ Λ.Ψ)) (𝓝 (g a₀)) :=
    ((hgc.tendsto a₀).comp hfm).congr fun p => hg.left_inv _ (mem_univ _)
  have hra := hg.right_inv a₀ (mem_univ _)
  have hψm : F'.mor (g a₀) = q.φ := congrArg (fun a => a.1.1) hra
  have hψs : Y'.src (g a₀) = Γ.Ψ.obj y := congrArg (fun a => a.1.2) hra
  have hψt : Y'.tgt (g a₀) = Λ.Ψ.obj y'' :=
    tendsto_nhds_unique (((Y'.continuous_tgt.tendsto _).comp hφ).congr fun p => p.tgt_φ)
      ((Λ.Ψ.continuous_obj'.tendsto y'').comp hy'')
  refine ⟨Obj.mk Γ.Ψ Λ.Ψ y (g a₀) y'' hψs hψt, Obj.ext hyq hψm hy''q, ?_⟩
  change Tendsto (fun p => p) _ _
  refine tendsto_subtype_rng.2 (Tendsto.prodMk_nhds hy (tendsto_subtype_rng.2 ?_))
  exact Tendsto.prodMk_nhds hφ hy''

/-- **Step (B)**: the map `α` of `H`, `(h, ψ', h'') ↦ (H(h, ψ', h''), s(h, ψ', h''))`, is an
sc-diffeomorphism onto the fibred product (p. 557). -/
theorem isScDiffeo_fibredMap_hFunctor (hP : Admissible Γ.Ψ Λ.Ψ) (hQ : Admissible Γ.Φ Λ.Φ)
    (hF : F.IsProperCovering) (hF'' : F''.IsProperCovering) :
    letI := MPolyfold.paracompactSpace_prod (epGroupoid Γ.Φ Λ.Φ hQ).PMor
      (epGroupoid Γ.Ψ Λ.Ψ hP).PObj
    letI :=
      ((epGroupoid Γ.Φ Λ.Φ hQ).PMor.prod (epGroupoid Γ.Ψ Λ.Ψ hP).PObj).paracompactSpace_subtype
      (MPolyfold.fibredProduct (epGroupoid Γ.Φ Λ.Φ hQ).src (hFunctor Γ Λ hP hQ).obj)
    ∃ g : MPolyfold.fibredProduct (epGroupoid Γ.Φ Λ.Φ hQ).src (hFunctor Γ Λ hP hQ).obj →
        Mor Γ.Ψ Λ.Ψ,
      (epGroupoid Γ.Ψ Λ.Ψ hP).PMor.IsScDiffeoOn (MPolyfold.subPolyfold
        (MPolyfold.isSubMPolyfold_fibredProduct (epGroupoid Γ.Φ Λ.Φ hQ).isLocalScDiffeo_src
          (hFunctor Γ Λ hP hQ).isScSmoothMap_obj)) (hFunctor Γ Λ hP hQ).fibredMap g univ univ := by
  set P := epGroupoid Γ.Ψ Λ.Ψ hP
  set Q := epGroupoid Γ.Φ Λ.Φ hQ
  set H := hFunctor Γ Λ hP hQ
  let _ := MPolyfold.paracompactSpace_prod Q.PMor P.PObj
  let _ := (Q.PMor.prod P.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct Q.src H.obj)
  let _ := MPolyfold.paracompactSpace_prod X.PMor Y.PObj
  let _ := (X.PMor.prod Y.PObj).paracompactSpace_subtype (MPolyfold.fibredProduct X.src F.obj)
  let _ := MPolyfold.paracompactSpace_prod X''.PMor Y''.PObj
  let _ := (X''.PMor.prod Y''.PObj).paracompactSpace_subtype
    (MPolyfold.fibredProduct X''.src F''.obj)
  have hB := MPolyfold.isSubMPolyfold_fibredProduct Q.isLocalScDiffeo_src H.isScSmoothMap_obj
  have hAF := MPolyfold.isSubMPolyfold_fibredProduct X.isLocalScDiffeo_src F.isScSmoothMap_obj
  have hAF'' :=
    MPolyfold.isSubMPolyfold_fibredProduct X''.isLocalScDiffeo_src F''.isScSmoothMap_obj
  obtain ⟨gF, hgF⟩ := hF.isScDiffeo_fibredMap
  obtain ⟨gF'', hgF''⟩ := hF''.isScDiffeo_fibredMap
  -- `((φ, φ', φ''), (y, ψ', y'')) ↦ (φ, y) ∈ X ₛ×_F Y` and `↦ (φ'', y'') ∈ X'' ₛ×_{F''} Y''`
  let aF : MPolyfold.fibredProduct Q.src H.obj → MPolyfold.fibredProduct X.src F.obj :=
    fun a => ⟨(a.1.1.h, a.1.2.x), congrArg Obj.x a.2⟩
  let aF'' : MPolyfold.fibredProduct Q.src H.obj → MPolyfold.fibredProduct X''.src F''.obj :=
    fun a => ⟨(a.1.1.k, a.1.2.z), congrArg Obj.z a.2⟩
  have haF : ∀ a, Y.src (gF (aF a)) = a.1.2.x := fun a =>
    congrArg (fun b : MPolyfold.fibredProduct X.src F.obj => b.1.2)
      (hgF.right_inv (aF a) (mem_univ _))
  have haF'' : ∀ a, Y''.src (gF'' (aF'' a)) = a.1.2.z := fun a =>
    congrArg (fun b : MPolyfold.fibredProduct X''.src F''.obj => b.1.2)
      (hgF''.right_inv (aF'' a) (mem_univ _))
  -- the inverse `(ψ, ψ', ψ'')` with `ψ = α_F⁻¹(φ, y)`, `ψ'' = α_{F''}⁻¹(φ'', y'')` (11.26), (11.27)
  let inv : MPolyfold.fibredProduct Q.src H.obj → Mor Γ.Ψ Λ.Ψ := fun a =>
    Mor.mk Γ.Ψ Λ.Ψ (gF (aF a)) a.1.2.φ (gF'' (aF'' a)) (by rw [haF]; exact a.1.2.src_φ)
      (by rw [haF'']; exact a.1.2.tgt_φ)
  have hval := MPolyfold.subPolyfold_inclusion_isScSmooth hB
  have h1 : (MPolyfold.subPolyfold hB).IsScSmoothMap Q.PMor fun a => a.1.1 :=
    (MPolyfold.isScSmoothMap_fst Q.PMor P.PObj).comp hval
  have h2 : (MPolyfold.subPolyfold hB).IsScSmoothMap P.PObj fun a => a.1.2 :=
    (MPolyfold.isScSmoothMap_snd Q.PMor P.PObj).comp hval
  have hasF : (MPolyfold.subPolyfold hB).IsScSmoothMap (MPolyfold.subPolyfold hAF) aF :=
    isScSmoothOn_subPolyfold_of_val' hAF (f := aF) (MPolyfold.IsScSmoothOn.prodMk
      ((isScSmoothMap_h hQ).comp h1) ((isScSmoothMap_x hP).comp h2))
  have hasF'' : (MPolyfold.subPolyfold hB).IsScSmoothMap (MPolyfold.subPolyfold hAF'') aF'' :=
    isScSmoothOn_subPolyfold_of_val' hAF'' (f := aF'') (MPolyfold.IsScSmoothOn.prodMk
      ((isScSmoothMap_k hQ).comp h1) ((isScSmoothMap_z hP).comp h2))
  refine ⟨inv, ?_, ?_, mapsTo_univ _ _, mapsTo_univ _ _, fun m _ => ?_, fun a _ => ?_⟩
  · exact isScSmoothOn_subPolyfold_of_val' hB
      (MPolyfold.IsScSmoothOn.prodMk H.isScSmoothMap_mor P.isScSmoothMap_src)
  · have e₁' := MPolyfold.IsScSmoothOn.comp hgF.isScSmoothOn_inv hasF (mapsTo_univ _ _)
    have e₃' := MPolyfold.IsScSmoothOn.comp hgF''.isScSmoothOn_inv hasF'' (mapsTo_univ _ _)
    have e₁ : (MPolyfold.subPolyfold hB).IsScSmoothOn Y.PMor (fun a => (inv a).h) univ := e₁'
    have e₂ : (MPolyfold.subPolyfold hB).IsScSmoothOn Y'.PMor (fun a => (inv a).φ) univ :=
      (isScSmoothMap_φ hP).comp h2
    have e₃ : (MPolyfold.subPolyfold hB).IsScSmoothOn Y''.PMor (fun a => (inv a).k) univ :=
      e₃'
    exact isScSmoothOn_mor_of hP (f := inv) e₁ e₂ e₃
  · refine Mor.ext ?_ rfl ?_
    · exact hgF.left_inv m.h (mem_univ _)
    · exact hgF''.left_inv m.k (mem_univ _)
  · refine Subtype.ext (Prod.ext (Mor.ext ?_ ?_ ?_) (Obj.ext (haF a) rfl (haF'' a)))
    · exact congrArg (fun b : MPolyfold.fibredProduct X.src F.obj => b.1.1)
        (hgF.right_inv (aF a) (mem_univ _))
    · exact (congrArg Obj.φ a.2).symm
    · exact congrArg (fun b : MPolyfold.fibredProduct X''.src F''.obj => b.1.1)
        (hgF''.right_inv (aF'' a) (mem_univ _))

/-- **Theorem 11.6.6 (1)**, the general form: `H` is a proper covering functor as soon as `Ψ` and
`Φ` are local sc-diffeomorphisms on objects and `Ψ : Y_x → Y'_{Φ(x)}` is onto. -/
theorem isProperCovering_hFunctor_of (hP : Admissible Γ.Ψ Λ.Ψ) (hQ : Admissible Γ.Φ Λ.Φ)
    (hΨ : Y.PObj.IsLocalScDiffeo Y'.PObj Γ.Ψ.obj) (hΦ : X.PObj.IsLocalScDiffeo X'.PObj Γ.Φ.obj)
    (hs : ∀ x, SurjOn Γ.Ψ.obj (F.obj ⁻¹' {x}) (F'.obj ⁻¹' {Γ.Φ.obj x}))
    (hF : F.IsProperCovering) (hF' : F'.IsProperCovering) (hF'' : F''.IsProperCovering) :
    (hFunctor Γ Λ hP hQ).IsProperCovering where
  surjective := surjective_hObj hF'' hF' hs
  isLocalScDiffeo := isLocalScDiffeo_hObj hP hQ hΨ hΦ hF''
  finite_fiber := finite_fiber_hObj hF hF' hF''
  evenlyCovered q := (isLocalScDiffeo_hObj hP hQ hΨ hΦ hF'').evenlyCovered_of_isProperMap
    (isProperMap_hObj hF hF' hF'') (finite_fiber_hObj hF hF' hF'' q)
  isScDiffeo_fibredMap := isScDiffeo_fibredMap_hFunctor hP hQ hF hF''

end HProper

end ProperCoveringHom

end HFunctor

/-! ### Theorem 11.6.6 -/

section Theorem

universe u₁ u₂ u₃ u₄ u₅ u₆

variable {ObjY MorY : Type u₁} [TopologicalSpace ObjY] [T2Space ObjY] [ParacompactSpace ObjY]
  [TopologicalSpace MorY] [T2Space MorY] [ParacompactSpace MorY]
  {ObjX MorX : Type u₂} [TopologicalSpace ObjX] [T2Space ObjX] [ParacompactSpace ObjX]
  [TopologicalSpace MorX] [T2Space MorX] [ParacompactSpace MorX]
  {ObjY' MorY' : Type u₃} [TopologicalSpace ObjY'] [T2Space ObjY'] [ParacompactSpace ObjY']
  [TopologicalSpace MorY'] [T2Space MorY'] [ParacompactSpace MorY']
  {ObjX' MorX' : Type u₄} [TopologicalSpace ObjX'] [T2Space ObjX'] [ParacompactSpace ObjX']
  [TopologicalSpace MorX'] [T2Space MorX'] [ParacompactSpace MorX']
  {ObjY'' MorY'' : Type u₅} [TopologicalSpace ObjY''] [T2Space ObjY''] [ParacompactSpace ObjY'']
  [TopologicalSpace MorY''] [T2Space MorY''] [ParacompactSpace MorY'']
  {ObjX'' MorX'' : Type u₆} [TopologicalSpace ObjX''] [T2Space ObjX''] [ParacompactSpace ObjX'']
  [TopologicalSpace MorX''] [T2Space MorX''] [ParacompactSpace MorX'']
  {Y : EpGroupoid ObjY MorY} {X : EpGroupoid ObjX MorX}
  {Y' : EpGroupoid ObjY' MorY'} {X' : EpGroupoid ObjX' MorX'}
  {Y'' : EpGroupoid ObjY'' MorY''} {X'' : EpGroupoid ObjX'' MorX''}
  {F : EpFunctor Y X} {F' : EpFunctor Y' X'} {F'' : EpFunctor Y'' X''}
  (Γ : ProperCoveringHom F F') (Λ : ProperCoveringHom F'' F')

namespace ProperCoveringHom

open WeakFibredProduct

variable (hP : Admissible Γ.Ψ Λ.Ψ) (hQ : Admissible Γ.Φ Λ.Φ)

/-- `(π_Y, π_X) : H → F`. -/
def projLeftHom : ProperCoveringHom (hFunctor Γ Λ hP hQ) F :=
  ⟨projLeft Γ.Ψ Λ.Ψ hP, projLeft Γ.Φ Λ.Φ hQ, fun _ => rfl, fun _ => rfl⟩

/-- `(π_{Y''}, π_{X''}) : H → F''`. -/
def projRightHom : ProperCoveringHom (hFunctor Γ Λ hP hQ) F'' :=
  ⟨projRight Γ.Ψ Λ.Ψ hP, projRight Γ.Φ Λ.Φ hQ, fun _ => rfl, fun _ => rfl⟩

/-- **Step (E) of the proof of Theorem 11.6.6** (p. 560): `τ_P(y, ψ', y'') = ψ'`,
`τ_Q(x, φ', x'') = φ'` is a natural transformation `(Ψ ∘ π_Y, Φ ∘ π_X) → (ζ ∘ π_{Y''}, ξ ∘ π_{X''})`
with `F' ∘ τ_P = τ_Q ∘ H`. -/
def natTransProj :
    NatTrans (Γ.comp (projLeftHom Γ Λ hP hQ)) (Λ.comp (projRightHom Γ Λ hP hQ)) where
  τY := natTrans Γ.Ψ Λ.Ψ hP
  τX := natTrans Γ.Φ Λ.Φ hQ
  comm _ := rfl

/-- **2021 Theorem 11.6.6, p. 555 (2017: Theorem 11.10, p. 405)**: let `Γ = (Ψ, Φ) : F → F'` be an
equivalence between proper covering functors and `(ζ, ξ) : F'' → F'` an sc-smooth functor
between proper coverings, `P = Y ×_{Y'} Y''`, `Q = X ×_{X'} X''` the weak fibred products and
`H : P → Q` the functor of (11.18), (11.19) (`hFunctor`, well-defined by construction).  Then
(1) `H` is a proper covering functor; (2) `(π_{Y''}, π_{X''}) : H → F''` is an equivalence of
proper covering functors; (3) `(Ψ ∘ π_Y, Φ ∘ π_X)` and `(ζ ∘ π_{Y''}, ξ ∘ π_{X''})` are naturally
equivalent functors `H → F'`; if `X''` is tame, so are `P` and `Q`; if `(ζ, ξ)` is an equivalence,
so is `(π_Y, π_X) : H → F`. -/
theorem theorem_11_6_6 (hF : F.IsProperCovering) (hF' : F'.IsProperCovering)
    (hF'' : F''.IsProperCovering) (hΓ : Γ.IsEquivalence) :
    (hFunctor Γ Λ (.of_isEquivalence_left hΓ.isEquivalence_Ψ)
      (.of_isEquivalence_left hΓ.isEquivalence_Φ)).IsProperCovering ∧
    (projRightHom Γ Λ (.of_isEquivalence_left hΓ.isEquivalence_Ψ)
      (.of_isEquivalence_left hΓ.isEquivalence_Φ)).IsEquivalence ∧
    (Γ.comp (projLeftHom Γ Λ (.of_isEquivalence_left hΓ.isEquivalence_Ψ)
      (.of_isEquivalence_left hΓ.isEquivalence_Φ))).NaturallyEquivalent
      (Λ.comp (projRightHom Γ Λ (.of_isEquivalence_left hΓ.isEquivalence_Ψ)
        (.of_isEquivalence_left hΓ.isEquivalence_Φ))) ∧
    (X''.IsTame → (epGroupoid Γ.Ψ Λ.Ψ (.of_isEquivalence_left hΓ.isEquivalence_Ψ)).IsTame ∧
      (epGroupoid Γ.Φ Λ.Φ (.of_isEquivalence_left hΓ.isEquivalence_Φ)).IsTame) ∧
    (Λ.IsEquivalence → (projLeftHom Γ Λ (.of_isEquivalence_left hΓ.isEquivalence_Ψ)
      (.of_isEquivalence_left hΓ.isEquivalence_Φ)).IsEquivalence) := by
  have hP : Admissible Γ.Ψ Λ.Ψ := .of_isEquivalence_left hΓ.isEquivalence_Ψ
  have hQ : Admissible Γ.Φ Λ.Φ := .of_isEquivalence_left hΓ.isEquivalence_Φ
  have hH : (hFunctor Γ Λ hP hQ).IsProperCovering :=
    isProperCovering_hFunctor_of hP hQ hΓ.isEquivalence_Ψ.isLocalScDiffeo_obj
      hΓ.isEquivalence_Φ.isLocalScDiffeo_obj (fun x => (hΓ.isFiberBijective x).surjOn) hF hF' hF''
  refine ⟨hH, (isEquivalence_iff hH hF'' _).2 ⟨isEquivalence_projRight hΓ.isEquivalence_Ψ hP,
    isEquivalence_projRight hΓ.isEquivalence_Φ hQ⟩, ⟨natTransProj Γ Λ hP hQ⟩, fun hX'' => ?_,
    fun hΛ => (isEquivalence_iff hH hF _).2 ⟨isEquivalence_projLeft hΛ.isEquivalence_Ψ hP,
      isEquivalence_projLeft hΛ.isEquivalence_Φ hQ⟩⟩
  exact ⟨(isEquivalence_projRight hΓ.isEquivalence_Ψ hP).isTame_of_isTame
      (hF''.isLocalScDiffeo.isTame hX''),
    (isEquivalence_projRight hΓ.isEquivalence_Φ hQ).isTame_of_isTame hX''⟩

end ProperCoveringHom

end Theorem

/-! ### Witness -/

namespace CoveringEquivalence.Examples

open EpGroupoid.Examples WeakFibredProduct

/-- **Witness for Theorem 11.6.6**: the equivalence `pairToPointCovering` and the identity of the
identity covering of the point satisfy its hypotheses; `P` is nonempty and `H` is a proper
covering. -/
theorem theorem_11_6_6_pairToPoint :
    Nonempty (Obj pairToPointCovering.Ψ
      (ProperCoveringHom.id (EpFunctor.id pointEpGroupoid)).Ψ) ∧
    (ProperCoveringHom.hFunctor pairToPointCovering
      (ProperCoveringHom.id (EpFunctor.id pointEpGroupoid))
      (.of_isEquivalence_left isEquivalence_pairToPoint)
      (.of_isEquivalence_left isEquivalence_pairToPoint)).IsProperCovering :=
  ⟨⟨Obj.mk _ _ (0 : ℤ) () () rfl rfl⟩,
    (ProperCoveringHom.theorem_11_6_6 _ _ EpFunctor.isProperCovering_id
      EpFunctor.isProperCovering_id EpFunctor.isProperCovering_id
      isEquivalence_pairToPointCovering).1⟩

end CoveringEquivalence.Examples

end Polyfold
