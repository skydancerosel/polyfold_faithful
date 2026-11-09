import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V8_22

/-! Round trip for V8_22 (after Definition 8.3.1 = 2017 Definition 8.4, 2017 pp. 271–272: the
functorial picture, the ep-groupoid `(W, 𝐖)`).

The item lists the definitions `morInv`, `morComp`, `toGroupoidStr`, `toEpGroupoid`, `projFunctor`
(vocabulary) and nine theorems.  `A` is the conjunction of their types, universe `0` (B lives in
`Type`; the functorial picture has `W` in the universe of `X`): `morComp_val` (the composition
formula on composable pairs), `μ_morComp` (`t_𝐖` of a composite), `exists_isProperMap_tgt` and
`isScSmoothCompSheet_toGroupoidStr` (Definition 7.3 (3), (4) for `(W, 𝐖)`),
`isStrongBundleMap_src`, `isStrongBundleMap_tgt` (`s_𝐖`, `t_𝐖` strong bundle maps covering `s`,
`t`), `exists_isomorphic_of_isomorphic` (the orbit of `w` covers that of `P w`),
`surjective_orbitMap_projFunctor`, `continuous_orbitMap_projFunctor` (`|P|`).

`B` (a) the project's `E.toEpGroupoid` has the M-polyfolds `W[0]`, `𝐖[0]` and the text's
structure maps (composition on composable pairs); (b) `s_𝐖`, `t_𝐖` cover `s`, `t`, are local
sc-diffeomorphisms and linear on the fibres; (c) `(P, π₁)` is an `EpFunctor`; (d) `P` maps the
orbit of `w` onto the orbit of `P w`; (e) `|P|` exists, is surjective and continuous.

* `A ⇒ B`: (a) is `rfl` except the composition, `morComp_val`; (b) local sc-diffeomorphisms from
  Part I's `isLocalScDiffeo_pullbackProj'` and the field `isLocalScDiffeo`, fibre linearity from
  `isStrongBundleMap_src/tgt`; (c) the functor is built here from `morComp_val` (not the item's
  `projFunctor`); (d) `⊆` from the covering property, `⊇` is `exists_isomorphic_of_isomorphic`;
  (e) `f = E.projFunctor.orbitMap` with A's surjectivity and continuity.
* `B ⇒ A`: `morComp_val` is B (a); `μ_morComp` from it and the field `μ_comp` (Definition 8.3.1
  (3)); `exists_isomorphic_of_isomorphic` from B (d); surjectivity and continuity of `|P|` from
  B (e) (B's `f` equals `E.projFunctor.orbitMap` on every class).  The other four conjuncts are
  re-proved outright: B's "`(W, 𝐖)` is an ep-groupoid" is carried only by the *type* of the
  project's `E.toEpGroupoid`, so B gives Definition 7.3 (3), (4) only through the fields of that
  construction, whose values are the banned `exists_isProperMap_tgt` and
  `isScSmoothCompSheet_toGroupoidStr`; we do not use those fields and copy the project's proofs
  (with B's composition formula in place of `morComp_val`).  `isStrongBundleMap_src/tgt` are
  stronger than B (b): a strong bundle map in the project's sense is also sc-smooth on the
  `[1]`-levels and maps `[1]` into `[1]`, which B (b) (the text's "fibrewise linear local
  sc-diffeomorphisms") does not say; they are Part I's `isStrongBundleMap_pullbackProj'` and the
  field `isStrongBundleMap` of `E`.
-/

namespace RoundTrip.V8_22
open Polyfold Set Function Filter Topology

/-- The project's statement (universe `0`). -/
def A : Prop :=
  (type_of% @Polyfold.EpStrongBundle.morComp_val.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.μ_morComp.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.exists_isProperMap_tgt.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isScSmoothCompSheet_toGroupoidStr.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isStrongBundleMap_src.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.isStrongBundleMap_tgt.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.exists_isomorphic_of_isomorphic.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.surjective_orbitMap_projFunctor.{0}) ∧
  (type_of% @Polyfold.EpStrongBundle.continuous_orbitMap_projFunctor.{0})

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.morComp_val.{0}, @Polyfold.EpStrongBundle.μ_morComp.{0},
    @Polyfold.EpStrongBundle.exists_isProperMap_tgt.{0},
    @Polyfold.EpStrongBundle.isScSmoothCompSheet_toGroupoidStr.{0},
    @Polyfold.EpStrongBundle.isStrongBundleMap_src.{0},
    @Polyfold.EpStrongBundle.isStrongBundleMap_tgt.{0},
    @Polyfold.EpStrongBundle.exists_isomorphic_of_isomorphic.{0},
    @Polyfold.EpStrongBundle.surjective_orbitMap_projFunctor.{0},
    @Polyfold.EpStrongBundle.continuous_orbitMap_projFunctor.{0}⟩

section Glue
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {SB : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]

/-- The functor `(P, π₁) : (W, 𝐖) → (X, 𝐗)`, built from the composition formula `hcv`. -/
def projF (E : EpStrongBundle X SB)
    (hcv : ∀ {q' q : pullbackSpace P X.src}, (q' : Mor × W).2 = E.μ q →
      (EpStrongBundle.morComp q' q : Mor × W) =
        (X.comp (q' : Mor × W).1 (q : Mor × W).1, (q : Mor × W).2)) :
    EpFunctor E.toEpGroupoid X where
  obj := P
  mor := fun p => (p : Mor × W).1
  src_mor q := (q.2 : P (q : Mor × W).2 = X.src (q : Mor × W).1).symm
  tgt_mor q := (E.P_μ q).symm
  mor_comp φ ψ h := by
    change (EpStrongBundle.morComp φ ψ : Mor × W).1 = X.comp (φ : Mor × W).1 (ψ : Mor × W).1
    rw [hcv h]
  mor_unit _ := rfl
  isScSmoothMap_obj := SB.isScSmoothMap_proj
  isScSmoothMap_mor := SB.isScSmoothMap_pullbackProj X.isScSmoothMap_src

end Glue

theorem A_to_B : A → B := by
  intro hA Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ SB _ hs E
  obtain ⟨hcv, -, -, -, hsrc, htgt, hiso, hsurj, hcont⟩ := hA
  refine ⟨⟨rfl, rfl, fun p => rfl, fun p => rfl, fun w => rfl, fun p => rfl,
    fun p q h => hcv (E := E) h⟩, ?_, ⟨projF E (hcv (E := E)), rfl, rfl⟩, ?_, ?_⟩
  · refine ⟨fun p => p.2, fun p => (htgt E).covers p, ?_, E.isLocalScDiffeo, fun ψ => ?_,
      fun ψ => ?_⟩
    · exact SB.isLocalScDiffeo_pullbackProj' hs X.isLocalScDiffeo_src
    · exact (hsrc E).fiber_linear ψ
    · exact (htgt E).fiber_linear ψ
  · intro w
    ext x
    constructor
    · rintro ⟨_, ⟨φ, rfl, rfl⟩, rfl⟩
      exact ⟨(φ : Mor × W).1, φ.2.symm, ((htgt E).covers φ).symm⟩
    · rintro ⟨ψ, hs', ht'⟩
      obtain ⟨w', ⟨φ, h1, h2⟩, hw'⟩ := hiso E ⟨ψ, hs', ht'⟩
      exact ⟨w', ⟨φ, h1, h2⟩, hw'⟩
  · exact ⟨E.projFunctor.orbitMap, fun w => rfl, hsurj E, hcont E⟩

/-! ### `B ⇒ A` -/

section FromB
variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {SB : StrongBundle X.PObj P}

/-- The composition formula, from B (a). -/
theorem morComp_val_of_B (hB : RoundTrip.V8_22.B) (E : EpStrongBundle X SB)
    {q' q : pullbackSpace P X.src} (h : (q' : Mor × W).2 = E.μ q) :
    (EpStrongBundle.morComp q' q : Mor × W) =
      (X.comp (q' : Mor × W).1 (q : Mor × W).1, (q : Mor × W).2) := by
  have := SB.paracompactSpace_pullback X.PMor X.src
  exact (hB Obj Mor X W P SB X.isScSmoothMap_src E).1.2.2.2.2.2.2 q' q h

/-- `t_𝐖` of a composite, from the composition formula `hcv` and Definition 8.3.1 (3). -/
theorem μ_morComp_of_cv (E : EpStrongBundle X SB)
    (hcv : ∀ {q' q : pullbackSpace P X.src}, (q' : Mor × W).2 = E.μ q →
      (EpStrongBundle.morComp q' q : Mor × W) =
        (X.comp (q' : Mor × W).1 (q : Mor × W).1, (q : Mor × W).2))
    {q' q : pullbackSpace P X.src} (h : (q' : Mor × W).2 = E.μ q) :
    E.μ (EpStrongBundle.morComp q' q) = E.μ q' := by
  obtain ⟨⟨γ, w⟩, hq⟩ := q
  obtain ⟨⟨ψ, w'⟩, hq'⟩ := q'
  have h' : w' = E.μ ⟨(γ, w), hq⟩ := h
  subst h'
  have hq₁ : P w = X.src γ := hq
  calc E.μ (EpStrongBundle.morComp _ _) = E.μ ⟨(X.comp ψ γ, w),
        hq₁.trans (X.src_comp ψ γ (EpStrongBundle.src_eq_tgt_of_eq_μ h)).symm⟩ :=
        E.μ_congr (hcv h)
    _ = _ := E.μ_comp ψ γ w hq₁ (EpStrongBundle.src_eq_tgt_of_eq_μ h)

variable [ParacompactSpace (pullbackSpace P X.src)]

/-- Definition 7.3 (3) for `(W, 𝐖)`, re-proved (a copy of the project's proof). -/
theorem exists_isProperMap_tgt' (E : EpStrongBundle X SB) (w : W) : ∃ V : Set W, IsOpen V ∧
    w ∈ V ∧ IsProperMap ((pullbackProj' P X.src ⁻¹' closure V).domRestrict E.μ) := by
  obtain ⟨V, hVo, hxV, hprop⟩ := X.exists_isProperMap (P w)
  refine ⟨P ⁻¹' V, hVo.preimage SB.continuous, hxV, ?_⟩
  have hμc := E.continuous_μ
  rw [MPolyfold.isProperMap_domRestrict_iff (SB.pullback X.isScSmoothMap_src).toMPolyfold0
    SB.toMPolyfold0 hμc]
  intro φ y hφ hy
  have hcl : closure (P ⁻¹' V) ⊆ P ⁻¹' closure V :=
    closure_minimal (preimage_mono subset_closure) (isClosed_closure.preimage SB.continuous)
  have hs : ∀ n, X.src ((φ n : Mor × W).1) ∈ closure V := fun n => by
    rw [← ((φ n).2 : P (φ n : Mor × W).2 = X.src (φ n : Mor × W).1)]; exact hcl (hφ n)
  have ht : Tendsto (X.tgt ∘ fun n => (φ n : Mor × W).1) atTop (𝓝 (P y)) :=
    ((SB.continuous.tendsto y).comp hy).congr fun n => E.P_μ (φ n)
  obtain ⟨ψ₀, -, hψ₀t, k, hk, hkt⟩ :=
    MPolyfold.exists_tendsto_subseq_of_isProperMap_domRestrict X.PMor hprop hs ht
  let q₀ : pullbackSpace P X.src := ⟨(X.inv ψ₀, y), by
    change P y = X.src (X.inv ψ₀); rw [X.src_inv, hψ₀t]⟩
  have hq : Tendsto (fun n => E.morInv (φ (k n))) atTop (𝓝 q₀) := by
    rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
    exact ((X.continuous_inv.tendsto ψ₀).comp hkt).prodMk_nhds (hy.comp hk.tendsto_atTop)
  have hw : Tendsto (fun n => (φ (k n) : Mor × W).2) atTop (𝓝 (E.μ q₀)) :=
    ((hμc.tendsto q₀).comp hq).congr fun n => EpStrongBundle.μ_morInv (φ (k n))
  let r₀ : pullbackSpace P X.src := ⟨(ψ₀, E.μ q₀), by
    change P (E.μ q₀) = X.src ψ₀; rw [E.P_μ]; exact X.tgt_inv ψ₀⟩
  refine ⟨r₀, ?_, k, hk, ?_⟩
  · exact isClosed_closure.mem_of_tendsto hw (Eventually.of_forall fun n => hφ (k n))
  · rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
    exact hkt.prodMk_nhds hw

/-- Definition 7.3 (4) for `(W, 𝐖)` in sheet form, re-proved (the project's proof, with B's
composition formula `hcv` in place of `morComp_val`). -/
theorem isScSmoothCompSheet' (E : EpStrongBundle X SB)
    (hcv : ∀ {q' q : pullbackSpace P X.src}, (q' : Mor × W).2 = E.μ q →
      (EpStrongBundle.morComp q' q : Mor × W) =
        (X.comp (q' : Mor × W).1 (q : Mor × W).1, (q : Mor × W).2)) :
    IsScSmoothCompSheet SB.toMPolyfold0 (SB.pullback X.isScSmoothMap_src).toMPolyfold0
      (pullbackProj' P X.src) E.μ EpStrongBundle.morComp := by
  intro σ U V hd
  have hμc := E.continuous_μ
  have hVo : IsOpen (E.μ ⁻¹' V) := hd.isScSmoothOn_inv.isOpen.preimage hμc
  have hσc : ContinuousOn (fun q => (σ (E.μ q) : Mor × W).1) (E.μ ⁻¹' V) :=
    (continuous_fst.comp continuous_subtype_val).comp_continuousOn
      (hd.isScSmoothOn_inv.continuousOn.comp hμc.continuousOn fun q hq => hq)
  refine MPolyfold.IsScSmoothOn.of_locally hVo fun q hq => ?_
  obtain ⟨U', V', σ', hU', hd'⟩ := X.isLocalScDiffeo_src (σ (E.μ q) : Mor × W).1
  have hNo := hσc.isOpen_inter_preimage hVo hd'.isScSmoothOn.isOpen
  refine ⟨_, hNo, ⟨hq, hU'⟩, inter_subset_left, ?_⟩
  have hX := X.isScSmoothCompSheet σ' U' V' hd'
  have hmaps : MapsTo (pullbackProj P X.src) (E.μ ⁻¹' V ∩
      (fun q => (σ (E.μ q) : Mor × W).1) ⁻¹' U') (X.tgt ⁻¹' V') := fun r hr => by
    change X.tgt (r : Mor × W).1 ∈ V'
    rw [← EpStrongBundle.src_eq_tgt_of_eq_μ (hd.right_inv _ hr.1)]
    exact hd'.mapsTo hr.2
  refine SB.isScSmoothOn_to_pullback_of_eqOn X.isScSmoothMap_src
    (a := fun r => X.comp (σ' (X.tgt (r : Mor × W).1)) (r : Mor × W).1)
    (b := fun r => (r : Mor × W).2)
    (MPolyfold.IsScSmoothOn.comp hX
      ((SB.isScSmoothMap_pullbackProj X.isScSmoothMap_src).mono hNo (subset_univ _)) hmaps)
    ((SB.isScSmoothMap_pullbackProj' X.isScSmoothMap_src).mono hNo (subset_univ _)) ?_
  intro r hr
  have h1 : (σ (E.μ r) : Mor × W).2 = E.μ r := hd.right_inv _ hr.1
  rw [hcv h1]
  have h3 : σ' (X.tgt (r : Mor × W).1) = (σ (E.μ r) : Mor × W).1 := by
    rw [← EpStrongBundle.src_eq_tgt_of_eq_μ h1]; exact hd'.left_inv _ hr.2
  rw [h3]

/-- B (e)'s `|P|` is the project's `orbitMap` of `projFunctor`. -/
theorem orbitMap_eq_of_B (E : EpStrongBundle X SB)
    (f : E.toEpGroupoid.OrbitSpace → X.OrbitSpace) (hf : ∀ w : W, f (E.toEpGroupoid.π w) = X.π (P w)) :
    f = E.projFunctor.orbitMap := by
  funext c
  induction c using Quotient.ind with
  | _ w => exact hf w

end FromB

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ SB E q' q h
    exact morComp_val_of_B hB E h
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ SB E q' q h
    exact μ_morComp_of_cv E (morComp_val_of_B hB E) h
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ SB _ E w
    exact exists_isProperMap_tgt' E w
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ SB _ E
    exact isScSmoothCompSheet' E (morComp_val_of_B hB E)
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ SB _ E
    exact SB.isStrongBundleMap_pullbackProj' X.isScSmoothMap_src
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ SB _ E
    exact E.isStrongBundleMap
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ SB _ E w x h
    have hd := (hB Obj Mor X W P SB X.isScSmoothMap_src E).2.2.2.1 w
    have hx : x ∈ orbitB X.toGroupoidStr (P w) := h
    rw [← hd] at hx
    obtain ⟨w', hw', rfl⟩ := hx
    exact ⟨w', hw', rfl⟩
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ SB _ E
    obtain ⟨f, hf, hsurj, -⟩ := (hB Obj Mor X W P SB X.isScSmoothMap_src E).2.2.2.2
    rw [← orbitMap_eq_of_B E f hf]
    exact hsurj
  · intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ SB _ E
    obtain ⟨f, hf, -, hcont⟩ := (hB Obj Mor X W P SB X.isScSmoothMap_src E).2.2.2.2
    rw [← orbitMap_eq_of_B E f hf]
    exact hcont

/-! ### Checks

**Harness note.**  `B`'s own statement mentions `E.toEpGroupoid`, whose body (with that of
`toGroupoidStr`) uses four of the banned theorems as proof fields: `morComp_val`, `μ_morComp`
(the groupoid laws of `toGroupoidStr`) and `exists_isProperMap_tgt` (the field
`exists_isProperMap`) as plain applications, `isScSmoothCompSheet_toGroupoidStr` through
`toEpGroupoid._proof_N`.  So `#rt_check` and `#rt_check_soft` fail on every term mentioning `B`
(recorded with `#guard_msgs` on `B_stmt : B → B := id`).  As in V7_40 we run
`#rt_check_except_defs`, the harness traversal `rtCollect` with the bodies of the three
constructions `toEpGroupoid`, `toGroupoidStr`, `projFunctor` not unfolded: our proofs reach no
banned theorem otherwise, i.e. they never use the fields of these constructions (B ⇒ A re-proves
`exists_isProperMap_tgt` and `isScSmoothCompSheet_toGroupoidStr` instead of reading them off the
fields of `E.toEpGroupoid`, and A ⇒ B builds its own functor `projF`).  This traversal cannot
see whether a proof projects a field of `toEpGroupoid`; that is checked mechanically for the
re-proved conjuncts instead: `μ_morComp_of_cv`, `exists_isProperMap_tgt'` and
`isScSmoothCompSheet'` take the composition formula as a hypothesis (not `B`, not
`toEpGroupoid`) and pass plain `#rt_check`; `B_to_A` uses `hB` only for the composition formula
(B (a)), B (d) and B (e). -/

open Lean Elab Command in
/-- `#rt_check_except_defs T [defs] [banned]`: the proof of `T` reaches no banned declaration
outside the bodies of the definitions `defs`. -/
elab "#rt_check_except_defs " t:ident " [" ds:ident,* "]" " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let stops := ds.getElems.toList.map (·.getId)
  let used := rtCollect env roots.toList (stops.foldl (fun s n => s.insert n) {})
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do throwError "FAIL: {t.getId} uses {bad} outside the bodies of {stops}"
  logInfo m!"OK: {t.getId} reaches the banned theorems only through the bodies of {stops}"

/-- `B`'s statement alone, to show what it reaches. -/
theorem B_stmt : B → B := id

/--
error: rt_check FAIL: RoundTrip.V8_22.B_stmt uses [Polyfold.EpStrongBundle.morComp_val,
 Polyfold.EpStrongBundle.μ_morComp,
 Polyfold.EpStrongBundle.exists_isProperMap_tgt,
 Polyfold.EpStrongBundle.isScSmoothCompSheet_toGroupoidStr]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V8_22.B_stmt [Polyfold.EpStrongBundle.morComp_val,
  Polyfold.EpStrongBundle.μ_morComp, Polyfold.EpStrongBundle.exists_isProperMap_tgt,
  Polyfold.EpStrongBundle.isScSmoothCompSheet_toGroupoidStr,
  Polyfold.EpStrongBundle.isStrongBundleMap_src, Polyfold.EpStrongBundle.isStrongBundleMap_tgt,
  Polyfold.EpStrongBundle.exists_isomorphic_of_isomorphic,
  Polyfold.EpStrongBundle.surjective_orbitMap_projFunctor,
  Polyfold.EpStrongBundle.continuous_orbitMap_projFunctor]

/--
error: rt_check_soft FAIL: RoundTrip.V8_22.B_stmt uses [Polyfold.EpStrongBundle.morComp_val,
 Polyfold.EpStrongBundle.μ_morComp,
 Polyfold.EpStrongBundle.exists_isProperMap_tgt]
-/
#guard_msgs (whitespace := lax) in
#rt_check_soft RoundTrip.V8_22.B_stmt [Polyfold.EpStrongBundle.morComp_val,
  Polyfold.EpStrongBundle.μ_morComp, Polyfold.EpStrongBundle.exists_isProperMap_tgt,
  Polyfold.EpStrongBundle.isScSmoothCompSheet_toGroupoidStr,
  Polyfold.EpStrongBundle.isStrongBundleMap_src, Polyfold.EpStrongBundle.isStrongBundleMap_tgt,
  Polyfold.EpStrongBundle.exists_isomorphic_of_isomorphic,
  Polyfold.EpStrongBundle.surjective_orbitMap_projFunctor,
  Polyfold.EpStrongBundle.continuous_orbitMap_projFunctor]

#rt_check_except_defs RoundTrip.V8_22.A_to_B [Polyfold.EpStrongBundle.toEpGroupoid,
  Polyfold.EpStrongBundle.toGroupoidStr, Polyfold.EpStrongBundle.projFunctor] [Polyfold.EpStrongBundle.morComp_val,
  Polyfold.EpStrongBundle.μ_morComp, Polyfold.EpStrongBundle.exists_isProperMap_tgt,
  Polyfold.EpStrongBundle.isScSmoothCompSheet_toGroupoidStr,
  Polyfold.EpStrongBundle.isStrongBundleMap_src, Polyfold.EpStrongBundle.isStrongBundleMap_tgt,
  Polyfold.EpStrongBundle.exists_isomorphic_of_isomorphic,
  Polyfold.EpStrongBundle.surjective_orbitMap_projFunctor,
  Polyfold.EpStrongBundle.continuous_orbitMap_projFunctor]
#rt_check_except_defs RoundTrip.V8_22.B_to_A [Polyfold.EpStrongBundle.toEpGroupoid,
  Polyfold.EpStrongBundle.toGroupoidStr, Polyfold.EpStrongBundle.projFunctor] [Polyfold.EpStrongBundle.morComp_val,
  Polyfold.EpStrongBundle.μ_morComp, Polyfold.EpStrongBundle.exists_isProperMap_tgt,
  Polyfold.EpStrongBundle.isScSmoothCompSheet_toGroupoidStr,
  Polyfold.EpStrongBundle.isStrongBundleMap_src, Polyfold.EpStrongBundle.isStrongBundleMap_tgt,
  Polyfold.EpStrongBundle.exists_isomorphic_of_isomorphic,
  Polyfold.EpStrongBundle.surjective_orbitMap_projFunctor,
  Polyfold.EpStrongBundle.continuous_orbitMap_projFunctor]
-- the re-proved conjuncts, from the composition formula only (no `B`, no `toEpGroupoid`):
#rt_check RoundTrip.V8_22.μ_morComp_of_cv [Polyfold.EpStrongBundle.morComp_val,
  Polyfold.EpStrongBundle.μ_morComp, Polyfold.EpStrongBundle.exists_isProperMap_tgt,
  Polyfold.EpStrongBundle.isScSmoothCompSheet_toGroupoidStr,
  Polyfold.EpStrongBundle.isStrongBundleMap_src, Polyfold.EpStrongBundle.isStrongBundleMap_tgt,
  Polyfold.EpStrongBundle.exists_isomorphic_of_isomorphic,
  Polyfold.EpStrongBundle.surjective_orbitMap_projFunctor,
  Polyfold.EpStrongBundle.continuous_orbitMap_projFunctor]
#rt_check RoundTrip.V8_22.exists_isProperMap_tgt' [Polyfold.EpStrongBundle.morComp_val,
  Polyfold.EpStrongBundle.μ_morComp, Polyfold.EpStrongBundle.exists_isProperMap_tgt,
  Polyfold.EpStrongBundle.isScSmoothCompSheet_toGroupoidStr,
  Polyfold.EpStrongBundle.isStrongBundleMap_src, Polyfold.EpStrongBundle.isStrongBundleMap_tgt,
  Polyfold.EpStrongBundle.exists_isomorphic_of_isomorphic,
  Polyfold.EpStrongBundle.surjective_orbitMap_projFunctor,
  Polyfold.EpStrongBundle.continuous_orbitMap_projFunctor]
#rt_check RoundTrip.V8_22.isScSmoothCompSheet' [Polyfold.EpStrongBundle.morComp_val,
  Polyfold.EpStrongBundle.μ_morComp, Polyfold.EpStrongBundle.exists_isProperMap_tgt,
  Polyfold.EpStrongBundle.isScSmoothCompSheet_toGroupoidStr,
  Polyfold.EpStrongBundle.isStrongBundleMap_src, Polyfold.EpStrongBundle.isStrongBundleMap_tgt,
  Polyfold.EpStrongBundle.exists_isomorphic_of_isomorphic,
  Polyfold.EpStrongBundle.surjective_orbitMap_projFunctor,
  Polyfold.EpStrongBundle.continuous_orbitMap_projFunctor]
#rt_overlap RoundTrip.V8_22.B_to_A [Polyfold.EpStrongBundle.morComp_val,
  Polyfold.EpStrongBundle.μ_morComp, Polyfold.EpStrongBundle.exists_isProperMap_tgt,
  Polyfold.EpStrongBundle.isScSmoothCompSheet_toGroupoidStr,
  Polyfold.EpStrongBundle.isStrongBundleMap_src, Polyfold.EpStrongBundle.isStrongBundleMap_tgt,
  Polyfold.EpStrongBundle.exists_isomorphic_of_isomorphic,
  Polyfold.EpStrongBundle.surjective_orbitMap_projFunctor,
  Polyfold.EpStrongBundle.continuous_orbitMap_projFunctor]

end RoundTrip.V8_22
