import Polyfold.Chapter11.EquivalenceFormsInfty

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part II, §8.2,
pp. 373–374: the averaging step and the extension step of the proof of **Proposition 8.2.3**
(2017: Proposition 8.1), in a form for arbitrary ep-groupoids (gap G.87).  Numbers and pages
are the 2021 text's.

# Averaging primitives over a finite group of symmetries

## The text, paraphrased

In the proof of Proposition 8.2.3 a primitive `τ` of a closed form `ω` on a neighbourhood
`V'(x)` invariant under the natural `G_x`-action is replaced by the average
`τ' = (1/#G_x) Σ_g g^*τ`, which is invariant under `G_x` and still satisfies `dτ' = ω`, since
`ω` is invariant.  Then `τ'` is extended to the saturation by `σ(y) = ψ^*τ'(x')` for a
morphism `ψ : x' → y`.

## What is formalized

For ep-groupoids `T` (the text's `G_x ⋉ V'(x)`) and `W` (the text's `V'(x)` without the
morphisms), an sc-smooth functor `J : W → T`, a finite nonempty family of sc-smooth functors
`Φ_g : W → W` (the text's `g ∗ ·`) and natural transformations `θ_g : J → J ∘ Φ_g` such that
`J` is a bijective local sc-diffeomorphism on objects, every morphism of `T` is a value of some
`θ_g`, and `Φ_h ∘ Φ_g = Φ_{σ_g(h)}` for permutations `σ_g` of the index set:
* `EP.exists_epForms_sum_pullback`: on each level `i`, for `ω ∈ Ωᵏ_ep(Wⁱ)` the sum
  `Σ_g (Φ_gⁱ)^*ω` is `(Jⁱ)^*τ` for a form `τ ∈ Ωᵏ_ep(Tⁱ)` (**the average is compatible with the
  morphisms of `T`**).
* `EP.injective_epFormsInftyPullback_of_surjective`: `J^*` is injective on `Ω*_{ep,∞}(T)`.
* **`EP.exists_primitive_of_average`**: if `c ∈ Ωᵏ⁺¹_{ep,∞}(T)` and `β ∈ Ωᵏ_{ep,∞}(W)` satisfy
  `dβ = J^*c`, then `c = dτ` for some `τ ∈ Ωᵏ_{ep,∞}(T)` (the text's `τ'`).
* **`EP.exists_primitive_of_equivalence`** (the extension step): if `E : T → Z` is an
  equivalence and `E^*a = dτ` for `τ ∈ Ωᵏ_{ep,∞}(T)`, then `a = d(E_*τ)` (the text's `σ`; `E_*`
  is the push-forward of Definition 11.2.3).

The application to `T = G_x ⋉ U(x)`, `W = U(x)` and `Z = X|π⁻¹(π(U(x)))` is in
`TranslationAverage.lean`, `SubGroupoidModel.lean` and
`EpPoincareLemma.lean` (`EP.proposition_8_2_3`).
-/

set_option maxSynthPendingDepth 3

open Set Function

noncomputable section

namespace Polyfold

open MPolyfold

universe u v

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {P : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {Q : MPolyfold Y} {k : ℕ}

/-- **The pull-backs by a jointly surjective family of local sc-diffeomorphisms are jointly
injective** on the families of alternating forms. -/
theorem formPullback_injective_of_family {ι : Type*} {q : ι → X → Y}
    (hq : ∀ g, P.IsLocalScDiffeo Q (q g)) (hq' : ∀ g, P.IsScSmoothMap Q (q g))
    (hs : ∀ y, ∃ g x, q g x = y) {τ τ' : ∀ y : Q.Level 1, Q.tangentFiber y [⋀^Fin k]→ₗ[ℝ] ℝ}
    (h : ∀ g, formPullback (hq' g) τ = formPullback (hq' g) τ') : τ = τ' := by
  funext y
  ext β
  obtain ⟨g, z, hz⟩ := hs (Q.levelVal 1 y)
  have hz1 : z ∈ P.levelSet 1 := ((hq g).mem_levelSet_iff z 1).1 (hz ▸ levelVal_mem y)
  have hxy : q g (P.levelVal 1 (P.levelMk 1 z hz1)) = Q.levelVal 1 y := by
    rw [levelVal_levelMk]; exact hz
  have hl := fun i => (hq g).tangentFiber_subset_image (P.levelMk 1 z hz1) y hxy (β i).2
  choose a ha hab using hl
  rw [← formPullback_eq (hq' g) τ (fun i => ⟨a i, ha i⟩) hxy β hab,
    ← formPullback_eq (hq' g) τ' (fun i => ⟨a i, ha i⟩) hxy β hab, h g]

end MPolyfold

namespace EP

variable {T W : EP.{u}}

/-! ### The index raises of the data -/

/-- The index raises of a functor which is a local sc-diffeomorphism on objects. -/
theorem isLocalScDiffeo_liftFunctor_obj {J : EpFunctor W.X T.X}
    (hJ : W.X.PObj.IsLocalScDiffeo T.X.PObj J.obj) :
    ∀ i : ℕ, (W.lift i).X.PObj.IsLocalScDiffeo (T.lift i).X.PObj (liftFunctor J i).obj
  | 0 => hJ
  | i + 1 => (isLocalScDiffeo_liftFunctor_obj hJ i).levelOne

theorem injective_liftFunctor_obj {J : EpFunctor W.X T.X} (hJ : Injective J.obj) :
    ∀ i : ℕ, Injective (liftFunctor J i).obj
  | 0 => hJ
  | i + 1 => fun _ _ h => MPolyfold.level_ext
      (injective_liftFunctor_obj hJ i (congrArg ((T.lift i).X.PObj.levelVal 1) h))

theorem surjective_liftFunctor_obj {J : EpFunctor W.X T.X}
    (hJ : W.X.PObj.IsLocalScDiffeo T.X.PObj J.obj) (hs : Surjective J.obj) :
    ∀ i : ℕ, Surjective (liftFunctor J i).obj
  | 0 => hs
  | i + 1 => fun y => by
    obtain ⟨x, hx⟩ := surjective_liftFunctor_obj hJ hs i ((T.lift i).X.PObj.levelVal 1 y)
    have hx1 : x ∈ (W.lift i).X.PObj.levelSet 1 :=
      ((isLocalScDiffeo_liftFunctor_obj hJ i).mem_levelSet_iff x 1).1
        (hx ▸ MPolyfold.levelVal_mem y)
    exact ⟨(W.lift i).X.PObj.levelMk 1 x hx1, MPolyfold.level_ext (by
      change (liftFunctor J i).obj ((W.lift i).X.PObj.levelVal 1 _) = _
      rw [MPolyfold.levelVal_levelMk, hx])⟩

/-- The component map of the index raise of a natural transformation `θ : J → J'` is a local
sc-diffeomorphism when `J` is one on objects (`s ∘ θ = J`). -/
theorem isLocalScDiffeo_liftNatTrans_app {J J' : EpFunctor W.X T.X} (θ : EpNatTrans J J')
    (hJ : W.X.PObj.IsLocalScDiffeo T.X.PObj J.obj) (i : ℕ) :
    (W.lift i).X.PObj.IsLocalScDiffeo (T.lift i).X.PMor (liftNatTrans θ i).app := fun x => by
  have hcomp : (T.lift i).X.src ∘ (liftNatTrans θ i).app = (liftFunctor J i).obj :=
    funext fun z => (liftNatTrans θ i).src_app z
  refine MPolyfold.IsLocalScDiffeoAt.of_comp_left ((T.lift i).X.isLocalScDiffeo_src _)
    (continuousOn_univ.1 (liftNatTrans θ i).isScSmoothMap_app.continuousOn) ?_
  rw [hcomp]
  exact isLocalScDiffeo_liftFunctor_obj hJ i x

/-- If every morphism of `T` is a value of some `θ_g`, the same holds on every level. -/
theorem exists_liftNatTrans_app_eq {G : Type*} {J : EpFunctor W.X T.X}
    {J' : G → EpFunctor W.X T.X} (θ : ∀ g, EpNatTrans J (J' g))
    (hJ : W.X.PObj.IsLocalScDiffeo T.X.PObj J.obj) (hθ : ∀ m : T.Mor, ∃ g y, (θ g).app y = m) :
    ∀ (i : ℕ) (m : (T.lift i).Mor), ∃ g y, (liftNatTrans (θ g) i).app y = m
  | 0, m => hθ m
  | i + 1, m => by
    obtain ⟨g, y, hy⟩ := exists_liftNatTrans_app_eq θ hJ hθ i ((T.lift i).X.PMor.levelVal 1 m)
    have hy1 : y ∈ (W.lift i).X.PObj.levelSet 1 :=
      ((isLocalScDiffeo_liftNatTrans_app (θ g) hJ i).mem_levelSet_iff y 1).1
        (hy ▸ MPolyfold.levelVal_mem m)
    exact ⟨g, (W.lift i).X.PObj.levelMk 1 y hy1, MPolyfold.level_ext (by
      change (liftNatTrans (θ g) i).app ((W.lift i).X.PObj.levelVal 1 _) = _
      rw [MPolyfold.levelVal_levelMk, hy])⟩

/-! ### The average on one level -/

section Level

variable (J : EpFunctor W.X T.X) {G : Type*} [Fintype G] (Φ : G → EpFunctor W.X W.X)
  (θ : ∀ g, EpNatTrans J (J.comp (Φ g)))
  (hJ : W.X.PObj.IsLocalScDiffeo T.X.PObj J.obj) (hJi : Injective J.obj)
  (hJs : Surjective J.obj) (hθ : ∀ m : T.Mor, ∃ g y, (θ g).app y = m)
  (σ : G → G ≃ G) (hΦ : ∀ g h, (Φ h).comp (Φ g) = Φ (σ g h))

include hΦ in
/-- The sum `Σ_h (Φ_hⁱ)^*ω` is invariant under every `(Φ_gⁱ)^*`. -/
theorem epFormsPullback_sum_epFormsPullback (k i : ℕ) (ω : W.epForms k i) (g : G) :
    epFormsPullback (Φ g) k i (∑ h, epFormsPullback (Φ h) k i ω) =
      ∑ h, epFormsPullback (Φ h) k i ω := by
  rw [map_sum, ← Equiv.sum_comp (σ g) fun h => epFormsPullback (Φ h) k i ω]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← hΦ g h, epFormsPullback_comp]

include θ hJ hJi hJs hθ hΦ in
/-- **The average is compatible with the morphisms**: for `ω ∈ Ωᵏ_ep(Wⁱ)` the sum
`Σ_g (Φ_gⁱ)^*ω` is the pull-back by `Jⁱ` of a form of the ep-groupoid `Tⁱ`. -/
theorem exists_epForms_sum_pullback (k i : ℕ) (ω : W.epForms k i) :
    ∃ τ : T.epForms k i, epFormsPullback J k i τ = ∑ g, epFormsPullback (Φ g) k i ω := by
  set η : W.epForms k i := ∑ g, epFormsPullback (Φ g) k i ω with hηdef
  have hq := isLocalScDiffeo_liftFunctor_obj hJ i
  have hqi := injective_liftFunctor_obj hJi i
  have hqs := surjective_liftFunctor_obj hJ hJs i
  have e : formPullback (liftFunctor J i).isScSmoothMap_obj (formDescend hq hqs η.1) = η.1 := by
    refine formPullback_formDescend hq hqs _ fun x x' hxx α α' hα => ?_
    obtain rfl : x = x' := MPolyfold.level_ext (hqi hxx)
    congr 1
    funext j
    exact Subtype.ext (hq.injOn_tangentFiber x (α j).2 (α' j).2 (hα j))
  have hinv : ∀ g, formPullback (liftFunctor (Φ g) i).isScSmoothMap_obj η.1 = η.1 := fun g =>
    congrArg Subtype.val (epFormsPullback_sum_epFormsPullback Φ σ hΦ k i ω g)
  refine ⟨⟨formDescend hq hqs η.1, isScForm_of_formPullback hq hqs _ (e ▸ η.2.1),
    (T.lift i).X.isMorCompatible_iff_formPullback.2 ?_⟩, Subtype.ext e⟩
  refine formPullback_injective_of_family
    (fun g => isLocalScDiffeo_liftNatTrans_app (θ g) hJ i)
    (fun g => (liftNatTrans (θ g) i).isScSmoothMap_app)
    (fun m => exists_liftNatTrans_app_eq θ hJ hθ i m) fun g => ?_
  have h1 : formPullback (liftNatTrans (θ g) i).isScSmoothMap_app
      (formPullback (T.lift i).X.isScSmoothMap_src (formDescend hq hqs η.1)) = η.1 :=
    (formPullback_comp (T.lift i).X.isScSmoothMap_src (liftNatTrans (θ g) i).isScSmoothMap_app
      _).symm.trans ((formPullback_congr _ (liftFunctor J i).isScSmoothMap_obj
        (fun x => (liftNatTrans (θ g) i).src_app x) _).trans e)
  have h2 : formPullback (liftNatTrans (θ g) i).isScSmoothMap_app
      (formPullback (T.lift i).X.isScSmoothMap_tgt (formDescend hq hqs η.1)) = η.1 :=
    (formPullback_comp (T.lift i).X.isScSmoothMap_tgt (liftNatTrans (θ g) i).isScSmoothMap_app
      _).symm.trans ((formPullback_congr _ ((liftFunctor J i).isScSmoothMap_obj.comp
        (liftFunctor (Φ g) i).isScSmoothMap_obj)
        (fun x => ((liftNatTrans (θ g) i).tgt_app x).trans (liftFunctor_comp_obj J (Φ g) i x))
        _).trans ((formPullback_comp _ _ _).trans ((congrArg _ e).trans (hinv g))))
  exact h1.trans h2.symm

end Level

/-! ### `Ω*_{ep,∞}` -/

/-- **The pull-back by a functor which is a surjective local sc-diffeomorphism on objects is
injective on `Ω*_{ep,∞}`.** -/
theorem injective_epFormsInftyPullback_of_surjective (J : EpFunctor W.X T.X)
    (hJ : W.X.PObj.IsLocalScDiffeo T.X.PObj J.obj) (hJs : Surjective J.obj) (k : ℕ) :
    Injective (epFormsInftyPullback J k) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro a ha
  obtain ⟨i, ω, rfl⟩ := T.exists_epFormsInftyOf_eq k a
  rw [LinearMap.mem_ker, epFormsInftyPullback_of] at ha
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact ha
  have h0 : epFormsPullback J k j (T.epFormsMap k i j hij ω) = 0 := by
    rw [epFormsPullback_epFormsMap]; exact hj
  have h1 : T.epFormsMap k i j hij ω = 0 :=
    Subtype.ext (formPullback_injective_of_isLocalScDiffeo
      (isLocalScDiffeo_liftFunctor_obj hJ j) (surjective_liftFunctor_obj hJ hJs j)
      (liftFunctor J j).isScSmoothMap_obj (congrArg Subtype.val h0))
  rw [← T.epFormsInftyOf_epFormsMap k hij ω, h1, map_zero]

/-- **2021 Proposition 8.2.3, the averaging step (p. 374)**, for ep-groupoids `T`, `W` with an
sc-smooth functor `J : W → T` which is a bijective local sc-diffeomorphism on objects, a finite
nonempty family of sc-smooth functors `Φ_g : W → W` closed under composition up to the
permutations `σ_g` (`Φ_h ∘ Φ_g = Φ_{σ_g(h)}`), and natural transformations `θ_g : J → J ∘ Φ_g`
whose values exhaust the morphisms of `T`: if `J^*c = dβ` for some `β ∈ Ωᵏ_{ep,∞}(W)`, then
`c = dτ` for some `τ ∈ Ωᵏ_{ep,∞}(T)`.  (`τ` is the text's average `(1/#G) Σ_g g^*β`, a form of
the ep-groupoid `T`.) -/
theorem exists_primitive_of_average (J : EpFunctor W.X T.X) {G : Type*} [Fintype G] [Nonempty G]
    (Φ : G → EpFunctor W.X W.X) (θ : ∀ g, EpNatTrans J (J.comp (Φ g)))
    (hJ : W.X.PObj.IsLocalScDiffeo T.X.PObj J.obj) (hJi : Injective J.obj)
    (hJs : Surjective J.obj) (hθ : ∀ m : T.Mor, ∃ g y, (θ g).app y = m)
    (σ : G → G ≃ G) (hΦ : ∀ g h, (Φ h).comp (Φ g) = Φ (σ g h))
    (k : ℕ) (c : T.epFormsInfty (k + 1)) (β : W.epFormsInfty k)
    (hβ : W.epFormsInftyD k β = epFormsInftyPullback J (k + 1) c) :
    ∃ τ : T.epFormsInfty k, T.epFormsInftyD k τ = c := by
  -- the average of `β` is `J^*τ₀`
  obtain ⟨i, ω, rfl⟩ := W.exists_epFormsInftyOf_eq k β
  obtain ⟨τi, hτi⟩ := exists_epForms_sum_pullback J Φ θ hJ hJi hJs hθ σ hΦ k i ω
  have hinv : ∀ (g : G) (j : ℕ) (b : T.epFormsInfty j),
      epFormsInftyPullback (Φ g) j (epFormsInftyPullback J j b) = epFormsInftyPullback J j b :=
    fun g j b => (LinearMap.congr_fun (epFormsInftyPullback_comp (Φ g) j J) b).symm.trans
      (LinearMap.congr_fun (epFormsInftyPullback_eq_of_natTrans j ⟨θ g⟩) b).symm
  have h1 : epFormsInftyPullback J k (T.epFormsInftyOf k i τi) =
      ∑ g, epFormsInftyPullback (Φ g) k (W.epFormsInftyOf k i ω) :=
    (epFormsInftyPullback_of J k i τi).trans ((congrArg (W.epFormsInftyOf k i) hτi).trans
      ((map_sum (W.epFormsInftyOf k i) _ _).trans
        (Finset.sum_congr rfl fun g _ => (epFormsInftyPullback_of (Φ g) k i ω).symm)))
  have e1 : W.epFormsInftyD k (epFormsInftyPullback J k (T.epFormsInftyOf k i τi)) =
      epFormsInftyPullback J (k + 1) (T.epFormsInftyD k (T.epFormsInftyOf k i τi)) :=
    LinearMap.congr_fun (epFormsInftyD_comp_epFormsInftyPullback J k) (T.epFormsInftyOf k i τi)
  have e2 : ∀ g : G, W.epFormsInftyD k (epFormsInftyPullback (Φ g) k (W.epFormsInftyOf k i ω)) =
      epFormsInftyPullback J (k + 1) c := fun g =>
    have e3 : W.epFormsInftyD k (epFormsInftyPullback (Φ g) k (W.epFormsInftyOf k i ω)) =
        epFormsInftyPullback (Φ g) (k + 1) (W.epFormsInftyD k (W.epFormsInftyOf k i ω)) :=
      LinearMap.congr_fun (epFormsInftyD_comp_epFormsInftyPullback (Φ g) k)
        (W.epFormsInftyOf k i ω)
    e3.trans ((congrArg (epFormsInftyPullback (Φ g) (k + 1)) hβ).trans (hinv g (k + 1) c))
  have h4 : ∀ x : W.epFormsInfty (k + 1), (∑ _g : G, x) = (Fintype.card G : ℝ) • x := fun x => by
    rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have h2 : epFormsInftyPullback J (k + 1) (T.epFormsInftyD k (T.epFormsInftyOf k i τi)) =
      epFormsInftyPullback J (k + 1) ((Fintype.card G : ℝ) • c) :=
    e1.symm.trans ((congrArg (W.epFormsInftyD k) h1).trans
      ((map_sum (W.epFormsInftyD k) _ _).trans ((Finset.sum_congr rfl fun g _ => e2 g).trans
        ((h4 _).trans (map_smul (epFormsInftyPullback J (k + 1)) _ c).symm))))
  have h3 : T.epFormsInftyD k (T.epFormsInftyOf k i τi) = (Fintype.card G : ℝ) • c :=
    injective_epFormsInftyPullback_of_surjective J hJ hJs (k + 1) h2
  have hcard : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨(Fintype.card G : ℝ)⁻¹ • T.epFormsInftyOf k i τi, ?_⟩
  refine (map_smul (T.epFormsInftyD k) _ _).trans ((congrArg _ h3).trans ?_)
  rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- **2021 Proposition 8.2.3, the extension step (p. 374)**: if `E : T → Z` is an equivalence of
ep-groupoids and `E^*a = dτ` with `τ ∈ Ωᵏ_{ep,∞}(T)`, then `a = d(E_*τ)`, with `E_*` the
push-forward of Definition 11.2.3 (the text's `σ(y) = ψ^*τ'(x')`). -/
theorem exists_primitive_of_equivalence {Z : EP.{v}} {E : EpFunctor T.X Z.X}
    (hE : E.IsEquivalence) (k : ℕ) (a : Z.epFormsInfty (k + 1)) (τ : T.epFormsInfty k)
    (hτ : T.epFormsInftyD k τ = epFormsInftyPullback E (k + 1) a) :
    Z.epFormsInftyD k (epFormsInftyPush hE k τ) = a := by
  have e := LinearMap.congr_fun (epFormsInftyD_comp_epFormsInftyPush hE k) τ
  simp only [LinearMap.comp_apply] at e
  rw [e, hτ, epFormsInftyPush_epFormsInftyPullback]

end EP

end Polyfold
