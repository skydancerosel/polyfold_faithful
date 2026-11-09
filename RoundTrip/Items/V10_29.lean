import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_29

/-! Round trip for V10_29 (2021 Remark 10.4.9 and (10.23) = 2017 Remark 10.4: `T(w) =
(τ(P(w)), Φ(w))`, `Ψ(w) = μ'(τ(P(w)), Φ(w))`, so `T` and `Ψ` are determined by `Φ` and `τ`, and
`T` is a strong bundle map).

`A` (universes at `0`) is the conjunction of the types of the six theorems
`StrongBundleNatTrans.T_val`, `T_eq`, `obj_eq`, `unique`, `unique_functor`,
`isStrongBundleMap_T`.  They assume less than `B`: `T_val`, `T_eq`, `obj_eq`, `unique` hold for
every `θ : StrongBundleNatTrans` (no strong bundle functor hypotheses), `unique_functor` needs
only `Ψ₁`, `Ψ₂` to be strong bundle functors, `isStrongBundleMap_T` only `Φ`.  `B` assumes both
`Φ` and `Ψ` are strong bundle functors and the text's `IsSBNatTransB` (V10_28; the same data as
the project's structure).

* `A_to_B`: package `B`'s `(T, τ)` as a `StrongBundleNatTrans` `θ` (fields = the clauses of
  `IsSBNatTransB`) and read (i)–(iv) off `A`: (i) `T_val`, (ii) `obj_eq` (membership from `T_val`),
  (iii) `unique` and `unique_functor`, (iv) `isStrongBundleMap_T` (`B'.pullback hs'` is
  `B'.pullback X'.isScSmoothMap_src` by proof irrelevance).
* `B_to_A`: vacuous.  `B` needs `Φ` and `Ψ` to be strong bundle functors, which `A`'s conjuncts do
  not assume, so `B` cannot be applied; the six conjuncts are re-proved outright below (the
  project's proofs, from non-item lemmas). -/

namespace RoundTrip.V10_29
open Polyfold Set Function

/-! ### The project's statement (universes at `0`)

The statements of `T_eq` and `obj_eq` (our `A2`, `A3`) contain the theorem
`StrongBundleNatTrans.mem` (the membership `(τ(P(w)), Φ(w)) ∈ 𝐗' ₛ×_{P'} W'`), whose proof is
`T_val ▸ _`, a banned theorem; see the harness note at the end. -/

def A1 : Prop := type_of% @Polyfold.EpStrongBundle.StrongBundleNatTrans.T_val.{0}
def A2 : Prop := type_of% @Polyfold.EpStrongBundle.StrongBundleNatTrans.T_eq.{0}
def A3 : Prop := type_of% @Polyfold.EpStrongBundle.StrongBundleNatTrans.obj_eq.{0}
def A4 : Prop := type_of% @Polyfold.EpStrongBundle.StrongBundleNatTrans.unique.{0}
def A5 : Prop := type_of% @Polyfold.EpStrongBundle.StrongBundleNatTrans.unique_functor.{0}
def A6 : Prop := type_of% @Polyfold.EpStrongBundle.StrongBundleNatTrans.isStrongBundleMap_T.{0}

def A : Prop := A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A6

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.StrongBundleNatTrans.T_val.{0},
    @Polyfold.EpStrongBundle.StrongBundleNatTrans.T_eq.{0},
    @Polyfold.EpStrongBundle.StrongBundleNatTrans.obj_eq.{0},
    @Polyfold.EpStrongBundle.StrongBundleNatTrans.unique.{0},
    @Polyfold.EpStrongBundle.StrongBundleNatTrans.unique_functor.{0},
    @Polyfold.EpStrongBundle.StrongBundleNatTrans.isStrongBundleMap_T.{0}⟩

theorem A_to_B : A → B := by
  rintro ⟨hTval, -, hobj, huniq, hufun, hmap⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
    hs' E E' ϕ ψ Φ Ψ τ T hΦ hΨ hT
  -- `B`'s data as a project natural transformation
  let θ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ :=
    ⟨T, fun w => (hT.1 w).1, fun w => (hT.1 w).2, hT.2.1, τ, fun w => (hT.2.2 w).symm⟩
  have hmem : ∀ w, P' (Φ.obj w) = X'.src (τ.app (P w)) := fun w => by
    have e : (T w : Mor' × W') = (τ.app (P w), Φ.obj w) := hTval θ w
    have h2 := (T w).2
    rw [e] at h2
    exact h2
  refine ⟨fun w => hTval θ w, fun w => ⟨hmem w, hobj θ w⟩,
    fun Ψ₂ T₂ hΨ₂ hT₂ => ?_, hmap θ hΦ⟩
  let θ₂ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ₂ :=
    ⟨T₂, fun w => (hT₂.1 w).1, fun w => (hT₂.1 w).2, hT₂.2.1, τ, fun w => (hT₂.2.2 w).symm⟩
  obtain ⟨hobj₂, hT₂eq⟩ := huniq θ₂ θ rfl
  have hfun : Ψ₂ = Ψ := hufun hΨ₂ hΨ θ₂ θ rfl
  exact ⟨hT₂eq, hobj₂, by rw [hfun]⟩

/-! ### The six conjuncts, re-proved outright (the project's proofs) -/

section

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
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'}
  {ϕ ψ : EpFunctor X X'} {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}

theorem T_val' (θ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ) (w : W) :
    (θ.T w : Mor' × W') = (θ.τ.app (P w), Φ.obj w) :=
  Prod.ext (θ.app_P w).symm (θ.src_T w)

theorem mem' (θ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ) (w : W) :
    (θ.τ.app (P w), Φ.obj w) ∈ pullbackSpace P' X'.src :=
  T_val' θ w ▸ (θ.T w).2

theorem T_eq' (θ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ) (w : W) :
    θ.T w = ⟨(θ.τ.app (P w), Φ.obj w), mem' θ w⟩ :=
  Subtype.ext (T_val' θ w)

theorem obj_eq' (θ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ) (w : W) :
    Ψ.obj w = E'.μ ⟨(θ.τ.app (P w), Φ.obj w), mem' θ w⟩ :=
  (θ.tgt_T w).symm.trans (congrArg E'.μ (T_eq' θ w))

theorem unique' {Ψ₁ Ψ₂ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (θ₁ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ₁) (θ₂ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ₂)
    (hτ : θ₁.τ.app = θ₂.τ.app) : Ψ₁.obj = Ψ₂.obj ∧ θ₁.T = θ₂.T := by
  have hT : θ₁.T = θ₂.T := funext fun w => Subtype.ext (by rw [T_val' θ₁, T_val' θ₂, hτ])
  refine ⟨funext fun w => ?_, hT⟩
  rw [← θ₁.tgt_T, ← θ₂.tgt_T, hT]

theorem unique_functor' {Ψ₁ Ψ₂ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (h₁ : E.IsStrongBundleFunctor E' ψ Ψ₁) (h₂ : E.IsStrongBundleFunctor E' ψ Ψ₂)
    (θ₁ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ₁) (θ₂ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ₂)
    (hτ : θ₁.τ.app = θ₂.τ.app) : Ψ₁ = Ψ₂ := by
  have h := (unique' θ₁ θ₂ hτ).1
  refine EpFunctor.ext h (funext fun q => Subtype.ext ?_)
  rw [h₁.mor_val, h₂.mor_val, h]

theorem isStrongBundleMap_T' (θ : E.StrongBundleNatTrans E' ϕ ψ Φ Ψ)
    (hΦ : E.IsStrongBundleFunctor E' ϕ Φ) :
    B.IsStrongBundleMap (B'.pullback X'.isScSmoothMap_src) θ.τ.app θ.T where
  covers w := (θ.app_P w).symm
  fiber_linear x := by
    let L : P ⁻¹' {x} →ₗ[ℝ] pullbackProj P' X'.src ⁻¹' {θ.τ.app x} :=
      ((pullbackFiberLinearEquiv P' X'.src (θ.τ.app x)).symm.toLinearMap).comp
        ((fiberCast P' (θ.τ.src_app x).symm).comp
          (hΦ.isStrongBundleMap_obj.fiber_linear x).mk')
    have hL : fiberRestrict P (pullbackProj P' X'.src) θ.τ.app θ.T (fun w => (θ.app_P w).symm) x =
        L := by
      funext v
      apply Subtype.ext; apply Subtype.ext
      have hv : P (v : W) = x := v.2
      change (θ.T v : Mor' × W') = ((L v : pullbackSpace P' X'.src) : Mor' × W')
      rw [T_val' θ, hv]
      change (θ.τ.app x, Φ.obj v) = (θ.τ.app x,
        ((fiberCast P' (θ.τ.src_app x).symm _ : P' ⁻¹' {X'.src (θ.τ.app x)}) : W'))
      rw [fiberCast_val]
      rfl
    rw [hL]; exact L.isLinear
  isScSmoothMap := by
    have hT : θ.T = pullbackPair P' X'.src (θ.τ.app ∘ P) Φ.obj (mem' θ) :=
      funext fun w => T_eq' θ w
    rw [hT]
    exact B'.isScSmoothMap_pullbackPair X'.isScSmoothMap_src
      (θ.τ.isScSmoothMap_app.comp B.isScSmoothMap_proj) hΦ.isStrongBundleMap_obj.isScSmoothMap _
  mapsTo_oneSet w hw := by
    rw [B'.mem_oneSet_pullback_iff X'.isScSmoothMap_src, T_val' θ]
    exact hΦ.isStrongBundleMap_obj.mapsTo_oneSet hw
  isScSmoothMap_one := by
    refine B'.isScSmoothMap_to_pullback_one X'.isScSmoothMap_src ?_ ?_
    · refine MPolyfold.IsScSmoothOn.congr (θ.τ.isScSmoothMap_app.comp B.isScSmoothMap_proj1)
        fun a _ => ?_
      change θ.τ.app (P (B.oneVal a)) = (θ.T (B.oneVal a) : Mor' × W').1
      rw [T_val' θ]
    · refine MPolyfold.IsScSmoothOn.congr hΦ.isStrongBundleMap_obj.isScSmoothMap_one
        fun a _ => B'.oneVal_injective ?_
      change Φ.obj (B.oneVal a) = (θ.T (B.oneVal a) : Mor' × W').2
      rw [T_val' θ]

end

/-- Vacuous for the audit: `A` is re-proved outright, `B` is not used. -/
theorem B_to_A : B → A := fun _ =>
  ⟨@T_val', @T_eq', @obj_eq', @unique', @unique_functor', @isStrongBundleMap_T'⟩

/-! ### Harness checks

`A2`, `A3` mention `StrongBundleNatTrans.mem`, a theorem proved with the banned `T_val`, so every
term mentioning `A` reaches `T_val` and plain `#rt_check` fails on both directions for that name
only (recorded below with `#guard_msgs`).  `#rt_check_except_defs` is the harness traversal
`rtCollect` with the bodies of the statement definitions `A2`, `A3` not unfolded: our proofs reach
banned theorems only through those statements (in `A_to_B` the membership is
`(T w).2` rewritten with `hTval θ w` from the hypothesis; in `B_to_A` it is `mem'`). -/

open Lean Elab Command in
/-- `#rt_check_except_defs T [nᵢ]`: the proof of `T` reaches the banned `nᵢ` only through the
bodies of the statement definitions `RoundTrip.V10_29.A2`, `RoundTrip.V10_29.A3`. -/
elab "#rt_check_except_defs " t:ident " [" bs:ident,* "]" : command => do
  let env ← getEnv
  let some ci := env.find? t.getId | throwError "unknown {t.getId}"
  let roots := ((rtValue? ci).map (·.getUsedConstants)).getD #[]
  let used := rtCollect env roots.toList
    ((NameSet.empty.insert ``RoundTrip.V10_29.A2).insert ``RoundTrip.V10_29.A3)
  if used.contains ``sorryAx then throwError "FAIL: {t.getId} contains sorry"
  let bad := bs.getElems.toList.map (·.getId) |>.filter used.contains
  unless bad.isEmpty do
    throwError "FAIL: {t.getId} uses {bad} outside the statements A2, A3"
  logInfo m!"OK: {t.getId} reaches the banned theorems only through the statements A2, A3"

/--
error: rt_check FAIL: RoundTrip.V10_29.A_to_B uses [Polyfold.EpStrongBundle.StrongBundleNatTrans.T_val]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_29.A_to_B [Polyfold.EpStrongBundle.StrongBundleNatTrans.T_val,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.T_eq,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.obj_eq,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.unique,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.unique_functor,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.isStrongBundleMap_T]

/--
error: rt_check FAIL: RoundTrip.V10_29.B_to_A uses [Polyfold.EpStrongBundle.StrongBundleNatTrans.T_val]
-/
#guard_msgs (whitespace := lax) in
#rt_check RoundTrip.V10_29.B_to_A [Polyfold.EpStrongBundle.StrongBundleNatTrans.T_val,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.T_eq,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.obj_eq,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.unique,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.unique_functor,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.isStrongBundleMap_T]

#rt_check_except_defs RoundTrip.V10_29.A_to_B [Polyfold.EpStrongBundle.StrongBundleNatTrans.T_val,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.T_eq,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.obj_eq,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.unique,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.unique_functor,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.isStrongBundleMap_T]
#rt_check_except_defs RoundTrip.V10_29.B_to_A [Polyfold.EpStrongBundle.StrongBundleNatTrans.T_val,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.T_eq,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.obj_eq,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.unique,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.unique_functor,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.isStrongBundleMap_T]
#rt_overlap RoundTrip.V10_29.B_to_A [Polyfold.EpStrongBundle.StrongBundleNatTrans.T_val,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.T_eq,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.obj_eq,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.unique,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.unique_functor,
  Polyfold.EpStrongBundle.StrongBundleNatTrans.isStrongBundleMap_T]

end RoundTrip.V10_29
