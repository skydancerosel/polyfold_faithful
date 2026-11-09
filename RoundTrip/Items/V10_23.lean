import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_23

/-! Round trip for V10_23 (2021 §10.4, the pull-back and the push-forward of section functors
along a strong bundle equivalence, (10.15)–(10.17) and (10.22)).

The item lists the definitions `pullback`, `preObj`, `preMor`, `pushforward` (vocabulary) and ten
theorems; `A` is the conjunction of their types, universes at `0`: `obj_pullback`, `pullback_eq`,
`isFunctorialSection_pullback`, `pushforward_eq` ((10.22)), `isFunctorialSection_pushforward`,
`pullback_pushforward`, `pushforward_pullback`, and three general lemmas `μ_injective_snd`,
`exists_μ_eq_of_orbitMap_eq`, `orbitMap_eq_of_forall_exists`.  The project's theorems are stated
for **all** sections, resp. all functorial sections (`IsSection`, `IsFunctorialSection`), not only
for sc-smooth ones.

`B` (blind): for a strong bundle equivalence in the text's sense (`IsSBEquivB`, V10_22), (a) the
fibre maps `Φ_x` are bijective, (b) the blind pull-back `pullB` of an sc-smooth section functor is
`Φ_x⁻¹ ∘ f' ∘ ϕ` and an sc-smooth section functor, (c) every `x'` receives a `σ : ϕ(x) → x'`,
(d) the blind push-forward `pushB` is `μ'(σ, Φ(f(x)))` for *every* choice (10.22) and an sc-smooth
section functor, (e) they are mutually inverse — all on sc-smooth section functors.

* `A_to_B`: `ofB` (V10_22's `←`), `pullB = h.pullback` (by `A`'s `pullback_eq`, `obj_pullback`),
  `pushB = h.pushforward` (by `A`'s `pushforward_eq`), then `A`'s functoriality and inverse
  theorems, the project's sc-smoothness lemmas `isScSmoothSection_pullback`,
  `isScSmoothSection_pushforward` (not item theorems), `eq_of_obj_eq` and `fiberEquiv` for (a).
* `B ⇒ A` fails for a genuine reason: `A`'s theorems are about arbitrary (functorial) sections,
  `B` only about sc-smooth section functors.  `B_to_A_sections` derives the five
  pull-back/push-forward theorems of `A` restricted to `Γ(P, μ)`, `Γ(P', μ')` from `B` (with
  `pullB = h.pullback` from `B`'s fibrewise injectivity, `pushB = h.pushforward` from `B`'s (d));
  `#rt_check` OK.  The three general lemmas are not about pull-backs at all. -/

set_option maxSynthPendingDepth 3

namespace RoundTrip.V10_23
open Polyfold Set Function

/-! The project's statement (universes at `0`). -/
def A1 : Prop := type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.obj_pullback.{0}
def A2 : Prop := type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_eq.{0}
def A3 : Prop :=
  type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isFunctorialSection_pullback.{0}
def A4 : Prop := type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_eq.{0}
def A5 : Prop :=
  type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isFunctorialSection_pushforward.{0}
def A6 : Prop :=
  type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_pushforward.{0}
def A7 : Prop :=
  type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_pullback.{0}
def A8 : Prop := type_of% @Polyfold.EpStrongBundle.μ_injective_snd.{0}
def A9 : Prop := type_of% @Polyfold.EpStrongBundle.exists_μ_eq_of_orbitMap_eq.{0}
def A10 : Prop := type_of% @Polyfold.EpStrongBundle.orbitMap_eq_of_forall_exists.{0}

/-- The project's statement. -/
def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A6 ∧ A7 ∧ A8 ∧ A9 ∧ A10

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.IsStrongBundleEquivalence.obj_pullback.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_eq.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isFunctorialSection_pullback.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_eq.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isFunctorialSection_pushforward.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_pushforward.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_pullback.{0},
    @Polyfold.EpStrongBundle.μ_injective_snd.{0},
    @Polyfold.EpStrongBundle.exists_μ_eq_of_orbitMap_eq.{0},
    @Polyfold.EpStrongBundle.orbitMap_eq_of_forall_exists.{0}⟩

section Glue
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {ϕ : EpFunctor X X'}
  {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}

/-- The project's strong bundle equivalences are the blind ones (V10_22, `→`). -/
theorem toB (h : E.IsStrongBundleEquivalence E' ϕ Φ) : IsSBEquivB E E' ϕ Φ := by
  refine ⟨h.isStrongBundleFunctor, h.isEquivalence_base, h.isEquivalence,
    ⟨h.isStrongBundleFunctor.isStrongBundleMap_obj.mapsTo_oneSet, h.isLocalScDiffeo_one, ?_, ?_,
      ?_⟩, h.isLocalStrongBundleIso_obj, h.isLocalStrongBundleIso_mor⟩
  · intro m m' _ hs ht he
    exact h.isEquivalence.mor_injective hs ht he
  · intro w₁ w₂ _ _ m' hs ht
    exact h.isEquivalence.exists_mor_eq hs ht
  · exact ⟨h.isHomeomorph_oneOrbitMap.homeomorph, fun a => rfl⟩

/-- The blind strong bundle equivalences are the project's (V10_22, `←`). -/
theorem ofB (h : IsSBEquivB E E' ϕ Φ) : E.IsStrongBundleEquivalence E' ϕ Φ := by
  obtain ⟨hF, hϕ, hΦ, ⟨hmap, -, -, -, e, he⟩, hobj, hmor⟩ := h
  refine ⟨hF, hϕ, hΦ, ?_, hobj, hmor⟩
  have : E.oneOrbitMap E' Φ hF.isStrongBundleMap_obj.mapsTo_oneSet = e := by
    funext q
    induction q using Quot.ind with
    | mk a => exact (he a).symm
  rw [this]
  exact e.isHomeomorph

omit [ParacompactSpace (pullbackSpace P X.src)] in
/-- The blind sc-smooth section functors are `Γ(P, μ)`. -/
theorem mem_sectionFunctors_iff (f : Obj → W) :
    IsScSmoothSectionFunctorB E f ↔ f ∈ E.sectionFunctors := by
  constructor
  · rintro ⟨hs, hsm, hfun⟩
    exact ⟨⟨hs, hsm⟩, fun φ => hfun φ _ _ rfl rfl (hs (X.src φ))⟩
  · rintro ⟨⟨hs, hsm⟩, hfun⟩
    refine ⟨hs, hsm, fun φ x y hx hy h => ?_⟩
    subst hx hy
    exact hfun φ

/-- `Φ(Φ*(f')(x)) = f'(ϕ(x))` for sections: the definition of `pullback` through `fiberEquiv`
(the project's three-line proof; used only in `B_to_A_sections`). -/
theorem obj_pullback' (h : E.IsStrongBundleEquivalence E' ϕ Φ) {f' : Obj' → W'}
    (hf' : IsSection P' f') (x : Obj) : Φ.obj (h.pullback f' x) = f' (ϕ.obj x) := by
  unfold EpStrongBundle.IsStrongBundleEquivalence.pullback
  rw [dif_pos (hf' _)]
  exact congrArg Subtype.val ((h.fiberEquiv x).apply_symm_apply ⟨f' (ϕ.obj x), hf' _⟩)

/-- A choice for the push-forward exists for every section (the project's `preObj`, `preMor`). -/
theorem exists_choice (h : E.IsStrongBundleEquivalence E' ϕ Φ) {f : Obj → W}
    (hf : IsSection P f) (x' : Obj') :
    ∃ q : Obj × Mor', X'.src q.2 = ϕ.obj q.1 ∧ X'.tgt q.2 = x' ∧
      P' (Φ.obj (f q.1)) = X'.src q.2 :=
  ⟨(h.preObj x', h.preMor x'), h.src_preMor x', h.tgt_preMor x', by
    rw [h.covers, hf, h.src_preMor]⟩

/-- The project's `isScSmoothSection_pullback`, with its use of `pullback_eq` (an item theorem)
replaced by a hypothesis `hpe` (`A`'s `pullback_eq` in `A_to_B`). -/
theorem isScSmoothSection_pullback' (h : E.IsStrongBundleEquivalence E' ϕ Φ)
    (hpe : ∀ {f' : Obj' → W'}, IsSection P' f' → ∀ {x : Obj} {w : W}, P w = x →
      Φ.obj w = f' (ϕ.obj x) → h.pullback f' x = w)
    {f' : Obj' → W'} (hf' : B'.IsScSmoothSection f') : B.IsScSmoothSection (h.pullback f') := by
  refine ⟨h.isSection_pullback f', MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x _ => ?_⟩
  obtain ⟨U, U', hxU, hi⟩ := h.isLocalStrongBundleIso_obj x
  obtain ⟨g, hg⟩ := hi.isScDiffeoOn_base
  obtain ⟨Ψ, hΨ⟩ := hi.isScDiffeoOn_zero
  have hmaps : MapsTo (f' ∘ ϕ.obj) U (P' ⁻¹' U') := fun z hz => by
    change P' (f' (ϕ.obj z)) ∈ U'; rw [hf'.1 (ϕ.obj z)]; exact hg.mapsTo hz
  have heq : EqOn (Ψ ∘ f' ∘ ϕ.obj) (h.pullback f') U := fun z hz => by
    have hm : P' (f' (ϕ.obj z)) ∈ U' := by rw [hf'.1 (ϕ.obj z)]; exact hg.mapsTo hz
    refine (hpe hf'.1 ?_ (hΨ.right_inv _ hm)).symm
    rw [StrongBundle.IsStrongBundleIsoOn.P_inv (h := h.isStrongBundleFunctor.isStrongBundleMap_obj)
      hg hΨ hm, hf'.1 (ϕ.obj z), hg.left_inv z hz]
  refine ⟨U, hg.isOpen_source, hxU, subset_univ _, ?_⟩
  exact (MPolyfold.IsScSmoothOn.comp hΨ.isScSmoothOn_inv
    (MPolyfold.IsScSmoothOn.comp hf'.2 hg.isScSmoothOn (mapsTo_univ _ _)) hmaps).congr heq

/-- The project's `isScSmoothSection_pushforward`, with its use of `pushforward_eq` (an item
theorem) replaced by a hypothesis `hpe` (`A`'s `pushforward_eq` in `A_to_B`). -/
theorem isScSmoothSection_pushforward' (h : E.IsStrongBundleEquivalence E' ϕ Φ) {f : Obj → W}
    (hf : B.IsScSmoothSection f)
    (hpe : ∀ {x' : Obj'} {y : Obj} {σ' : Mor'} (hs : X'.src σ' = ϕ.obj y) (_ : X'.tgt σ' = x'),
      h.pushforward f x' =
        E'.μ ⟨(σ', Φ.obj (f y)), (h.covers _).trans ((congrArg ϕ.obj (hf.1 y)).trans hs.symm)⟩) :
    B'.IsScSmoothSection (h.pushforward f) := by
  classical
  refine ⟨h.isSection_pushforward f, MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun x₀ _ => ?_⟩
  obtain ⟨T, V, τ, U₁, U₁', g₁, hτ, hg₁, hx₀, hNo⟩ := h.exists_pushforward_local x₀
  set N : Set Obj' := V ∩ τ ⁻¹' (X'.src ⁻¹' U₁') with hN
  let b : Obj' → W' := fun x' => Φ.obj (f (g₁ (X'.src (τ x'))))
  have hb : ∀ x' ∈ N, P' (b x') = X'.src (τ x') := fun x' hx' => by
    change P' (Φ.obj (f (g₁ (X'.src (τ x'))))) = _
    rw [h.covers, hf.1, hg₁.right_inv _ hx'.2]
  let ι : Obj' → pullbackSpace P' X'.src := fun x' =>
    if hx : P' (b x') = X'.src (τ x') then ⟨(τ x', b x'), hx⟩
    else ⟨(X'.unit (P' (b x')), b x'), (X'.src_unit _).symm⟩
  have hι : ∀ x' (hx' : x' ∈ N), ι x' = ⟨(τ x', b x'), hb x' hx'⟩ := fun x' hx' =>
    dif_pos (hb x' hx')
  have heq : EqOn (E'.μ ∘ ι) (h.pushforward f) N := fun x' hx' => by
    have hs : X'.src (τ x') = ϕ.obj (g₁ (X'.src (τ x'))) := (hg₁.right_inv _ hx'.2).symm
    change E'.μ (ι x') = h.pushforward f x'
    rw [hι x' hx', hpe hs (hτ.right_inv x' hx'.1)]
  have hτN : X'.PObj.IsScSmoothOn X'.PMor τ N := hτ.isScSmoothOn_inv.mono hNo inter_subset_left
  have hgN : X'.PObj.IsScSmoothOn X.PObj (g₁ ∘ X'.src ∘ τ) N :=
    MPolyfold.IsScSmoothOn.comp hg₁.isScSmoothOn_inv
      (MPolyfold.IsScSmoothOn.comp X'.isScSmoothMap_src hτN (mapsTo_univ _ _)) fun x' hx' => hx'.2
  have hbN : X'.PObj.IsScSmoothOn B'.toMPolyfold0 b N :=
    MPolyfold.IsScSmoothOn.comp h.isStrongBundleFunctor.isStrongBundleMap_obj.isScSmoothMap
      (MPolyfold.IsScSmoothOn.comp hf.2 hgN (mapsTo_univ _ _)) (mapsTo_univ _ _)
  have hιN := B'.isScSmoothOn_to_pullback_of_eqOn X'.isScSmoothMap_src (ι := ι) hτN hbN
    fun v hv => by rw [hι v hv]
  exact ⟨N, hNo, hx₀, subset_univ _,
    (MPolyfold.IsScSmoothOn.comp E'.isStrongBundleMap.isScSmoothMap hιN (mapsTo_univ _ _)).congr
      heq⟩

end Glue

theorem A_to_B : A → B := by
  rintro ⟨hobj, hpeq, hfunpull, hpeqpush, hfunpush, hpp, hpp', -, -, -⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
    E E' ϕ Φ hB
  have h := ofB hB
  have hpull : ∀ f' : Obj' → W', IsSection P' f' → pullB ϕ Φ f' = h.pullback f' := by
    intro f' hf'
    funext x
    have hex : ∃ w : W, P w = x ∧ Φ.obj w = f' (ϕ.obj x) :=
      ⟨h.pullback f' x, h.P_pullback f' x, hobj h hf' x⟩
    unfold pullB
    rw [dif_pos hex]
    exact (hpeq h hf' hex.choose_spec.1 hex.choose_spec.2).symm
  have hpush : ∀ (f : Obj → W) (hf : IsSection P f), E.IsFunctorialSection hf →
      pushB E' ϕ Φ f = h.pushforward f := by
    intro f hf hfun
    funext x'
    have hex := exists_choice h hf x'
    unfold pushB
    rw [dif_pos hex, hpeqpush h hf hfun hex.choose_spec.1 hex.choose_spec.2.1]
  refine ⟨fun w₁ w₂ hP he => h.eq_of_obj_eq hP he, fun x w' hw' => ?_, fun f' hf' => ?_,
    fun x' => h.isEquivalence_base.exists_iso x', fun f hf => ?_, fun f hf => ?_,
    fun f' hf' => ?_⟩
  · -- (a) surjectivity of `Φ_x`
    refine ⟨(h.fiberEquiv x).symm ⟨w', hw'⟩, ((h.fiberEquiv x).symm ⟨w', hw'⟩).2, ?_⟩
    exact congrArg Subtype.val ((h.fiberEquiv x).apply_symm_apply ⟨w', hw'⟩)
  · -- (b) the pull-back
    obtain ⟨⟨hs, hsm⟩, hfun⟩ := (mem_sectionFunctors_iff f').1 hf'
    rw [hpull f' hs]
    refine ⟨fun x => ⟨h.P_pullback f' x, hobj h hs x⟩, (mem_sectionFunctors_iff _).2 ?_⟩
    exact ⟨isScSmoothSection_pullback' h (fun hf' _ _ hw he => hpeq h hf' hw he) ⟨hs, hsm⟩,
      hfunpull h hs hfun⟩
  · -- (d) the push-forward
    obtain ⟨⟨hs, hsm⟩, hfun⟩ := (mem_sectionFunctors_iff f).1 hf
    rw [hpush f hs hfun]
    refine ⟨fun x x' σ hσs hσt hP => hpeqpush h hs hfun hσs hσt, (mem_sectionFunctors_iff _).2 ?_⟩
    exact ⟨isScSmoothSection_pushforward' h ⟨hs, hsm⟩
      (fun hσs hσt => hpeqpush h hs hfun hσs hσt), hfunpush h hs hfun⟩
  · -- (e) `Φ*(Φ_* f) = f`
    obtain ⟨⟨hs, _⟩, hfun⟩ := (mem_sectionFunctors_iff f).1 hf
    rw [hpush f hs hfun, hpull _ (h.isSection_pushforward f)]
    exact hpp h hs hfun
  · -- (e) `Φ_*(Φ* f') = f'`
    obtain ⟨⟨hs, _⟩, hfun⟩ := (mem_sectionFunctors_iff f').1 hf'
    rw [hpull f' hs, hpush _ (h.isSection_pullback f') (hfunpull h hs hfun)]
    exact hpp' h hs hfun

/-- **`B` gives `A`'s pull-back and push-forward theorems on sc-smooth section functors**
(`isFunctorialSection_pullback`, `pushforward_eq`, `isFunctorialSection_pushforward`,
`pullback_pushforward`, `pushforward_pullback`, restricted to `Γ(P, μ)`, `Γ(P', μ')`). -/
theorem B_to_A_sections (hB : B) {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj]
    [ParacompactSpace Obj] [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
    {X : EpGroupoid Obj Mor} {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W]
    {P : W → Obj} [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    {B : StrongBundle X.PObj P} [ParacompactSpace (pullbackSpace P X.src)]
    {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
    [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
    {W' : Type} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
    [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
    [ParacompactSpace (pullbackSpace P' X'.src)]
    {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {ϕ : EpFunctor X X'}
    {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid} (h : E.IsStrongBundleEquivalence E' ϕ Φ) :
    (∀ f' ∈ E'.sectionFunctors, E.IsFunctorialSection (h.isSection_pullback f')) ∧
    (∀ f ∈ E.sectionFunctors, ∀ (hf : IsSection P f) {x' : Obj'} {y : Obj} {σ' : Mor'}
      (hs : X'.src σ' = ϕ.obj y) (_ : X'.tgt σ' = x'),
      h.pushforward f x' =
        E'.μ ⟨(σ', Φ.obj (f y)), (h.covers _).trans ((congrArg ϕ.obj (hf y)).trans hs.symm)⟩) ∧
    (∀ f ∈ E.sectionFunctors, E'.IsFunctorialSection (h.isSection_pushforward f)) ∧
    (∀ f ∈ E.sectionFunctors, h.pullback (h.pushforward f) = f) ∧
    (∀ f' ∈ E'.sectionFunctors, h.pushforward (h.pullback f') = f') := by
  obtain ⟨hinj, -, hpb, -, hpf, hpp, hpp'⟩ :=
    hB Obj Mor X W P B Obj' Mor' X' W' P' B' E E' ϕ Φ (toB h)
  -- `pullB = h.pullback` on sections, by `B`'s fibrewise injectivity
  have hpull : ∀ f' : Obj' → W', IsSection P' f' → pullB ϕ Φ f' = h.pullback f' := by
    intro f' hf'
    funext x
    have hex : ∃ w : W, P w = x ∧ Φ.obj w = f' (ϕ.obj x) :=
      ⟨h.pullback f' x, h.P_pullback f' x, obj_pullback' h hf' x⟩
    unfold pullB
    rw [dif_pos hex]
    exact hinj _ _ (hex.choose_spec.1.trans (h.P_pullback f' x).symm)
      (hex.choose_spec.2.trans (obj_pullback' h hf' x).symm)
  -- `pushB = h.pushforward` on `Γ(P, μ)`, by `B`'s (d) for the choice `(preObj, preMor)`
  have hpush : ∀ f ∈ E.sectionFunctors, pushB E' ϕ Φ f = h.pushforward f := by
    intro f hf
    have hfB := (mem_sectionFunctors_iff f).2 hf
    funext x'
    rw [(hpf f hfB).1 (h.preObj x') x' (h.preMor x') (h.src_preMor x') (h.tgt_preMor x')
      (by rw [h.covers, hfB.1, h.src_preMor]), h.pushforward_def hfB.1]
  refine ⟨fun f' hf' => ?_, fun f hf hs x' y σ' hσs hσt => ?_, fun f hf => ?_, fun f hf => ?_,
    fun f' hf' => ?_⟩
  · have hf'B := (mem_sectionFunctors_iff f').2 hf'
    have hmem : h.pullback f' ∈ E.sectionFunctors := by
      rw [← hpull f' hf'B.1]; exact (mem_sectionFunctors_iff _).1 (hpb f' hf'B).2
    obtain ⟨_, hfun⟩ := hmem
    exact hfun
  · rw [← hpush f hf]
    exact (hpf f ((mem_sectionFunctors_iff f).2 hf)).1 y x' σ' hσs hσt _
  · have hmem : h.pushforward f ∈ E'.sectionFunctors := by
      rw [← hpush f hf]
      exact (mem_sectionFunctors_iff _).1 (hpf f ((mem_sectionFunctors_iff f).2 hf)).2
    obtain ⟨_, hfun⟩ := hmem
    exact hfun
  · have := hpp f ((mem_sectionFunctors_iff f).2 hf)
    rwa [hpush f hf, hpull _ (h.isSection_pushforward f)] at this
  · have hf'B := (mem_sectionFunctors_iff f').2 hf'
    have hmem : h.pullback f' ∈ E.sectionFunctors := by
      rw [← hpull f' hf'B.1]; exact (mem_sectionFunctors_iff _).1 (hpb f' hf'B).2
    have := hpp' f' hf'B
    rwa [hpull f' hf'B.1, hpush _ hmem] at this

#rt_check RoundTrip.V10_23.A_to_B
  [Polyfold.EpStrongBundle.IsStrongBundleEquivalence.obj_pullback,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_eq,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isFunctorialSection_pullback,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_eq,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isFunctorialSection_pushforward,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_pushforward,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_pullback,
  Polyfold.EpStrongBundle.μ_injective_snd,
  Polyfold.EpStrongBundle.exists_μ_eq_of_orbitMap_eq,
  Polyfold.EpStrongBundle.orbitMap_eq_of_forall_exists]
#rt_check RoundTrip.V10_23.B_to_A_sections
  [Polyfold.EpStrongBundle.IsStrongBundleEquivalence.obj_pullback,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_eq,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isFunctorialSection_pullback,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_eq,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isFunctorialSection_pushforward,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_pushforward,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_pullback,
  Polyfold.EpStrongBundle.μ_injective_snd,
  Polyfold.EpStrongBundle.exists_μ_eq_of_orbitMap_eq,
  Polyfold.EpStrongBundle.orbitMap_eq_of_forall_exists]
#rt_overlap RoundTrip.V10_23.B_to_A_sections
  [Polyfold.EpStrongBundle.IsStrongBundleEquivalence.obj_pullback,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_eq,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isFunctorialSection_pullback,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_eq,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.isFunctorialSection_pushforward,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pullback_pushforward,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_pullback,
  Polyfold.EpStrongBundle.μ_injective_snd,
  Polyfold.EpStrongBundle.exists_μ_eq_of_orbitMap_eq,
  Polyfold.EpStrongBundle.orbitMap_eq_of_forall_exists]

end RoundTrip.V10_23
