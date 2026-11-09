import Polyfold.Chapter3.FillerLinearAlgebra
import Polyfold.Chapter3.BasicGermLinearization

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1, the
paragraph after Definition 3.1.4 (preprint 3.4) (the matrix of `Dg(0)`) and **Proposition 3.1.5 (preprint 3.5) (Filler)** for a
filler, and §3.6 **Remark 3.6.2 (preprint 3.49)**.

# The linearization of a filled section

## The text, paraphrased

(After Definition 3.1.4 (preprint 3.4)) `ρ(0)` and `Dr(0)` are projections.  "From `ρ(r(y))f(r(y)) = f(r(y))` …
by linearization at `y = 0` the relation `ρ(0)Tf(0) = Tf(0)`.  From `g(r(y)) = f(r(y))` … we
deduce `Tg(0) = Tf(0)` on `T₀O`.  From the identity `(1 − ρ(r(y)))g(r(y)) = 0` … we deduce, using
`g(0) = 0`, the relation `(1 − ρ(0))Dg(0) ∘ Dr(0) = 0`."  Hence the matrix
`Dg(0) = [[Tf(0), ρ(0)Dg(0)(1 − Dr(0))], [0, (1 − ρ(0))Dg(0)(1 − Dr(0))]]`, and by property (3)
the lower right entry is an isomorphism `ker Dr(0) → ker ρ(0)`, so `ker Dg(0) = ker Tf(0) ⊕ {0}`.
(Proposition 3.1.5 (preprint 3.5)) (1) `Tf(0)` surjective iff `Dg(0)` surjective; (2) `Tf(0)` Fredholm iff `Dg(0)`
Fredholm, with equal index.  (Remark 3.6.2 (preprint 3.49)) By replacing `O` by a smaller set one may assume in
Definition 3.6.1 (preprint 3.48) (1) that `f = g` on all of `O` and in (2) that `g(y) = ρ(r(y))g(y)` for `y ∈ U`
implies `y ∈ O`.

## What is formalized

* `Polyfold.StrongRetr.scDeriv_fiber_zero`: `D(pr_F ∘ R)(0, 0)(h, k) = ρ(0)k` (the linearization
  of `R(u, k) = (r(u), ρ(u)k)` at `(0, 0)` in the fibre direction is `ρ(0)`, in the base direction
  `0`); `Polyfold.StrongRetr.scDeriv_r_idem` (`Dr(0)² = Dr(0)`), `ρCLM_idem` (`ρ(0)² = ρ(0)`).
* `Polyfold.IsFillerOf.scDeriv_sub_eq` (the linearization of `y ↦ [1 − ρ(r(y))]g(y)` at `0` is
  `(1 − ρ(0))Dg(0)`, using `g(0) = 0`), `Polyfold.IsFillerOf.deriv_comp_r_eq_zero`
  (`(1 − ρ(0))Dg(0)Dr(0) = 0`), `Polyfold.IsFillerOf.exists_kerEquiv` (property (3) in terms of
  `Dg(0)`), `Polyfold.IsFillerOf.scDeriv_section_comp_r` (`D(f ∘ r)(0) = Dg(0)Dr(0)`, the text's
  `Tg(0) = Tf(0)`).
* `Polyfold.IsFillerOf.proposition_3_1_5` (**Proposition 3.1.5 (preprint 3.5)**): for a filler `g` of `f` with
  `g(0) = 0`, the restriction `Tf(0) = Dg(0)|_{range Dr(0)} : range Dr(0) → range ρ(0)`
  (`fillerRestrict`) is surjective iff `Dg(0)` is, Fredholm iff `Dg(0)` is, with the same index.
* `Polyfold.IsFillerOf.remark_3_6_2` (**Remark 3.6.2 (preprint 3.49)**).

## What the text leaves implicit, and the choices made (the findings)

* **The linearization of `ρ(r(y))g(y)` at `0`** is `ρ(0)Dg(0)`: the text says "using `g(0) = 0`"
  for the analogous identity.  The proof is the chain rule for `(u, k) ↦ ρ(u)k = (R(u, k))₂`
  composed with `y ↦ (r(y), g(y))`, where the derivative of `(R(u, k))₂` at `(0, 0)` is `(h, k) ↦
  ρ(0)k`: in the fibre direction because `k ↦ ρ(0)k` is linear, in the base direction because
  `ρ(u)0 = 0`; both computed on the dense level `1` and extended by continuity.  `g(0) = 0` enters
  through the point `(r(0), g(0)) = (0, 0)` at which `R` is linearized; `r(0) = 0` holds because
  `0 ∈ O`.
* **`(1 − ρ(0))Dg(0)Dr(0) = 0`** needs `f = g` on `O` near `0` and `ρ(x)f(x) = f(x)` on `O`, i.e.
  that `f` is a section of `K → O` (hypothesis `hfK`), and the continuity of `r` at `0`.
* **Proposition 3.1.5 (preprint 3.5) is the abstract statement `FillerLinearAlgebra.lean`** applied to
  `p = Dr(0)`, `q = ρ(0)`, `L = Dg(0)`; the "topological" in condition (3) is used for the
  closedness of the ranges.
* `Tf(0)` is formalized as `Dg(0)|_{range Dr(0)}` (`fillerRestrict`); that this is the
  restriction of `D(f ∘ r)(0) = Dg(0)Dr(0)` to `T₀O = range Dr(0)` is `scDeriv_section_comp_r`
  (for `f ∘ r` sc¹, as in Definition 3.1.3 (preprint 3.3)).
-/

open Set Filter Topology Function Module ContinuousLinearMap

noncomputable section

namespace Polyfold

variable {E F : ScBanach} {C U : Set (E 0)} {R : E 0 × F 0 → E 0 × F 0}

open StrongRetr

/-- The chain rule at a level-`1` point, for sc¹ maps `f : U → V`, `g : V → G₀` (Theorem 1.3.1 (preprint 1.21),
second component; `scDeriv_comp_apply` of `DegeneracyIndex.lean` with a general target). -/
lemma scDeriv_comp_apply' {G : ScBanach} {D : Set (F 0)} {V : Set (F 0)} {f : E 0 → F 0}
    {g : F 0 → G 0} (hU : IsRelOpenInQuadrant E C U) (hV : IsRelOpenInQuadrant F D V)
    (hf : IsSc1 U f) (hg : IsSc1 V g) (hfV : MapsTo f U V) {x : E 1} (hx : x ∈ E.lvlSet U 1)
    (h : E 0) : scDeriv V g (levelMap f 1 x) (scDeriv U f x h) = scDeriv U (g ∘ f) x h := by
  obtain ⟨_, hchain⟩ := theorem_1_3_1 hU hV hf hg hfV
  have := hchain (show ((x, h) : E.tangent 0) ∈ E.tangentSet U from hx)
  exact (congrArg Prod.snd this).symm

/-! ### Derivative identities for strong bundle retractions -/

namespace StrongRetr

variable (hU : IsRelOpenInQuadrant E C U) (hR : IsStrongBundleRetraction U R)
  (h0 : (0 : E 0) ∈ U)
include hU hR

/-- `r` is sc-smooth on `U`. -/
lemma r_isScSmooth : IsScSmooth U (r R) := (hR.baseRetraction hU).isScSmooth

omit hU in
/-- `r(0) = 0` when `0 ∈ O`. -/
lemma r_zero (h0O : (0 : E 0) ∈ r R '' U) : r R 0 = 0 := r_eq_self hR h0O

/-- `Dr(0)` is idempotent (`r ∘ r = r`). -/
theorem scDeriv_r_idem (h0O : (0 : E 0) ∈ r R '' U) (h : E 0) :
    scDeriv U (r R) 0 (scDeriv U (r R) 0 h) = scDeriv U (r R) 0 h := by
  have hr1 : IsSc1 U (r R) := (r_isScSmooth hU hR).isSc1
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact mem_U_of_mem_O hR h0O
  have hlev : levelMap (r R) 1 (0 : E 1) = 0 :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, r_zero hR h0O])
  have h1 := scDeriv_comp_apply' hU hU hr1 hr1 (fun u hu => r_mem hR hu) h01 h
  rw [hlev] at h1
  rw [h1]
  have h2 : IsSc1With U (r R ∘ r R) (scDeriv U (r R)) :=
    hr1.isSc1With_scDeriv.congr fun u hu => (r_r hR hu).symm
  rw [IsSc1.scDeriv_eqOn h2 (hU.isScDomain.uniqueDiffWithinAt 1) h01]

omit hU in
include h0 in
/-- `ρ(0)` is idempotent. -/
theorem ρCLM_idem (h0O : (0 : E 0) ∈ r R '' U) (k : F 0) :
    ρCLM hR h0 (ρCLM hR h0 k) = ρCLM hR h0 k := by
  rw [ρCLM_apply, ρCLM_apply, ρ_ρ hR h0O]

/-- The fibre part `(u, k) ↦ (R(u, k))₂ = ρ(u)k` is sc¹ on `U ⊕ F`. -/
lemma fiber_isSc1 : IsSc1 (U ×ˢ univ) fun p : (E.prod F) 0 => (R p).2 :=
  (hR.isScSmooth_zero.snd (hU.prod_univ F).isScDomain).isSc1

include h0 in
/-- **The linearization of `ρ(u)k` at `(0, 0)`**: `D(pr_F ∘ R)(0, 0)(h, k) = ρ(0)k` (the fibre
direction: `k ↦ ρ(0)k` is linear; the base direction: `ρ(u)0 = 0`; both on the dense level `1`). -/
theorem scDeriv_fiber_zero (h : E 0) (k : F 0) :
    scDeriv (U ×ˢ univ) (fun p : (E.prod F) 0 => (R p).2) 0 (h, k) = ρCLM hR h0 k := by
  set D := scDeriv (U ×ˢ univ) (fun p : (E.prod F) 0 => (R p).2) (0 : (E.prod F) 1) with hD
  have hUF := (hU.prod_univ F).isScDomain
  have h01 : (0 : (E.prod F) 1) ∈ (E.prod F).lvlSet (U ×ˢ univ) 1 := by
    rw [ScBanach.mem_lvlSet, map_zero]; exact ⟨h0, mem_univ _⟩
  have h01' : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have hder := (fiber_isSc1 hU hR).isSc1With_scDeriv.hasFDerivWithinAt 0 h01
  -- the fibre direction
  have hinr : D.comp (ContinuousLinearMap.inr ℝ (E 0) (F 0)) = ρCLM hR h0 := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := F)
    have hmaps : MapsTo ⇑(ContinuousLinearMap.inr ℝ (E 1) (F 1)) univ
        ((E.prod F).lvlSet (U ×ˢ univ) 1) := by
      intro k₁ _
      change (((0 : E 1), k₁) : (E.prod F) 1) ∈ _
      rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase, map_zero]; exact ⟨h0, mem_univ _⟩
    have h1 : HasFDerivWithinAt
        (((fun p : (E.prod F) 0 => (R p).2) ∘ (E.prod F).toBase 1) ∘
          ⇑(ContinuousLinearMap.inr ℝ (E 1) (F 1)))
        ((D.comp ((E.prod F).toBase 1)).comp (ContinuousLinearMap.inr ℝ (E 1) (F 1))) univ 0 :=
      HasFDerivWithinAt.comp (f := ⇑(ContinuousLinearMap.inr ℝ (E 1) (F 1))) 0 hder
        (ContinuousLinearMap.inr ℝ (E 1) (F 1)).hasFDerivWithinAt hmaps
    have h2 : HasFDerivWithinAt
        (((fun p : (E.prod F) 0 => (R p).2) ∘ (E.prod F).toBase 1) ∘
          ⇑(ContinuousLinearMap.inr ℝ (E 1) (F 1)))
        ((ρCLM hR h0).comp (F.toBase 1)) univ 0 := by
      have : (((fun p : (E.prod F) 0 => (R p).2) ∘ (E.prod F).toBase 1) ∘
          ⇑(ContinuousLinearMap.inr ℝ (E 1) (F 1))) = fun k₁ => ρCLM hR h0 (F.toBase 1 k₁) := by
        funext k₁
        simp only [Function.comp_apply, ContinuousLinearMap.inr_apply]
        change (R ((E.prod F).toBase 1 ((0 : E 1), k₁))).2 = _
        rw [ScBanach.prod_toBase, map_zero]
        rfl
      rw [this]
      exact ((ρCLM hR h0).comp (F.toBase 1)).hasFDerivAt.hasFDerivWithinAt
    have huniq := uniqueDiffWithinAt_univ.eq h1 h2
    ext k₁
    have := congrArg (fun T : F 1 →L[ℝ] F 0 => T k₁) huniq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply] at this ⊢
    rw [ScBanach.prod_toBase, map_zero] at this
    exact this
  -- the base direction
  have hinl : D.comp (ContinuousLinearMap.inl ℝ (E 0) (F 0)) = 0 := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
    have hmaps : MapsTo ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1)) (E.lvlSet U 1)
        ((E.prod F).lvlSet (U ×ˢ univ) 1) := by
      intro u₁ hu₁
      change ((u₁, (0 : F 1)) : (E.prod F) 1) ∈ _
      rw [ScBanach.mem_lvlSet, ScBanach.prod_toBase]; exact ⟨hu₁, mem_univ _⟩
    have h1 : HasFDerivWithinAt
        (((fun p : (E.prod F) 0 => (R p).2) ∘ (E.prod F).toBase 1) ∘
          ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1)))
        ((D.comp ((E.prod F).toBase 1)).comp (ContinuousLinearMap.inl ℝ (E 1) (F 1)))
        (E.lvlSet U 1) 0 :=
      HasFDerivWithinAt.comp (f := ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1))) 0 hder
        (ContinuousLinearMap.inl ℝ (E 1) (F 1)).hasFDerivWithinAt hmaps
    have hzero : ∀ u₁ ∈ E.lvlSet U 1,
        (((fun p : (E.prod F) 0 => (R p).2) ∘ (E.prod F).toBase 1) ∘
          ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1))) u₁ = 0 := by
      intro u₁ hu₁
      simp only [Function.comp_apply, ContinuousLinearMap.inl_apply]
      change (R ((E.prod F).toBase 1 (u₁, (0 : F 1)))).2 = 0
      rw [ScBanach.prod_toBase, map_zero]
      exact (ρ_isLinear hR hu₁).map_zero
    have h2 : HasFDerivWithinAt
        (((fun p : (E.prod F) 0 => (R p).2) ∘ (E.prod F).toBase 1) ∘
          ⇑(ContinuousLinearMap.inl ℝ (E 1) (F 1)))
        (0 : E 1 →L[ℝ] F 0) (E.lvlSet U 1) 0 :=
      (hasFDerivWithinAt_const (0 : F 0) 0 (E.lvlSet U 1)).congr hzero (hzero 0 h01')
    have huniq := (hU.isScDomain.uniqueDiffWithinAt 1 0 h01').eq h1 h2
    ext u₁
    have := congrArg (fun T : E 1 →L[ℝ] F 0 => T u₁) huniq
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
      zero_apply] at this ⊢
    rw [ScBanach.prod_toBase, map_zero] at this
    exact this
  have hhk : ((h, k) : (E.prod F) 0) = ContinuousLinearMap.inl ℝ (E 0) (F 0) h +
      ContinuousLinearMap.inr ℝ (E 0) (F 0) k := by simp
  rw [hhk, map_add]
  have e1 := congrArg (fun T : E 0 →L[ℝ] F 0 => T h) hinl
  have e2 := congrArg (fun T : F 0 →L[ℝ] F 0 => T k) hinr
  simp only [ContinuousLinearMap.comp_apply, zero_apply] at e1 e2
  rw [e1, e2, zero_add]

end StrongRetr

/-! ### The linearization of a filler -/

namespace IsFillerOf

variable {hU : IsRelOpenInQuadrant E C U} {hR : IsStrongBundleRetraction U R} {h0 : (0 : E 0) ∈ U}
  {fb g : E 0 → F 0} (hfg : IsFillerOf hU hR h0 fb g)

/-- `(f.prod g).comp h = (f.comp h).prod (g.comp h)` for bounded operators. -/
lemma _root_.Polyfold.ContinuousLinearMap.prod_comp' {M N₁ N₂ M₀ : Type*} [NormedAddCommGroup M]
    [NormedSpace ℝ M] [NormedAddCommGroup N₁] [NormedSpace ℝ N₁] [NormedAddCommGroup N₂]
    [NormedSpace ℝ N₂] [NormedAddCommGroup M₀] [NormedSpace ℝ M₀] (f : M →L[ℝ] N₁) (g : M →L[ℝ] N₂)
    (h : M₀ →L[ℝ] M) : (f.prod g).comp h = (f.comp h).prod (g.comp h) :=
  ContinuousLinearMap.ext fun _ => rfl

include hfg in
/-- **The linearization of `y ↦ [1 − ρ(r(y))]g(y)` at `0` is `(1 − ρ(0))Dg(0)`** (for `g(0) = 0`,
by the chain rule and `scDeriv_fiber_zero`). -/
theorem scDeriv_sub_eq (hg : IsScSmooth U g) (hg0 : g 0 = 0) (h0O : (0 : E 0) ∈ r R '' U) :
    scDeriv U (fun y => g y - ρ R (r R y) (g y)) 0 =
      scDeriv U g 0 - (ρCLM hR h0).comp (scDeriv U g 0) := by
  have hUF := (hU.prod_univ F).isScDomain
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have huniq := hU.isScDomain.uniqueDiffWithinAt 1 0 h01
  have hr1 : IsSc1 U (r R) := (r_isScSmooth hU hR).isSc1
  have hg1 : IsSc1 U g := hg.isSc1
  set Dr := scDeriv U (r R) 0 with hDr
  set Dg := scDeriv U g 0 with hDg
  -- the pair `(r, g)` and its derivative
  have hpair : IsSc1 U (scPair (r R) g) :=
    (IsSck.scPair (k := 1) hU.isScDomain (r_isScSmooth hU hR 1) (hg 1)).1
  have hmaps : MapsTo (scPair (r R) g) U (U ×ˢ univ) := fun u hu => ⟨r_mem hR hu, mem_univ _⟩
  have hDpair : scDeriv U (scPair (r R) g) 0 = Dr.prod Dg := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
    have h1 := hpair.isSc1With_scDeriv.hasFDerivWithinAt 0 h01
    have h2 := (hr1.isSc1With_scDeriv.hasFDerivWithinAt 0 h01).prodMk
      (hg1.isSc1With_scDeriv.hasFDerivWithinAt 0 h01)
    rw [ContinuousLinearMap.prod_comp']
    exact huniq.eq h1 h2
  have hlev : levelMap (scPair (r R) g) 1 (0 : E 1) = 0 := by
    apply levelMap_eq_of_toBase_eq
    rw [map_zero, map_zero]
    show (0 : (E.prod F) 0) = (r R 0, g 0)
    rw [r_zero hR h0O, hg0]; rfl
  -- the composite `ψ₂ = pr_F ∘ R ∘ (r, g)` and its derivative `ρ(0)Dg(0)`
  have hψ₂ : IsSc1 U ((fun p : (E.prod F) 0 => (R p).2) ∘ scPair (r R) g) :=
    (theorem_1_3_1' hU.isScDomain hUF hpair (fiber_isSc1 hU hR) hmaps).1
  have hDψ₂ : scDeriv U ((fun p : (E.prod F) 0 => (R p).2) ∘ scPair (r R) g) 0 =
      (ρCLM hR h0).comp Dg := by
    ext h
    have := scDeriv_comp_apply' hU (hU.prod_univ F) hpair (fiber_isSc1 hU hR) hmaps h01 h
    rw [hlev, hDpair] at this
    rw [← this, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
    exact scDeriv_fiber_zero hU hR h0 _ _
  -- uniqueness of the derivative of `g − ψ₂`
  apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
  have h1 := hfg.isSc1.isSc1With_scDeriv.hasFDerivWithinAt 0 h01
  have h2 := (hg1.isSc1With_scDeriv.hasFDerivWithinAt 0 h01).sub
    (hψ₂.isSc1With_scDeriv.hasFDerivWithinAt 0 h01)
  rw [hDψ₂] at h2
  rw [ContinuousLinearMap.sub_comp]
  exact huniq.eq h1 h2

include hfg in
/-- **`(1 − ρ(0))Dg(0)Dr(0) = 0`**: the identity `[1 − ρ(r(y))]g(r(y)) = 0` near `0` (from `g = f`
on `O` and `ρ(x)f(x) = f(x)` on `O`), linearized at `0`. -/
theorem deriv_comp_r_eq_zero (hg : IsScSmooth U g) (hg0 : g 0 = 0) (h0O : (0 : E 0) ∈ r R '' U)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) (h : E 0) :
    scDeriv U g 0 (scDeriv U (r R) 0 h) - ρCLM hR h0 (scDeriv U g 0 (scDeriv U (r R) 0 h)) = 0 := by
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have huniq := hU.isScDomain.uniqueDiffWithinAt 1 0 h01
  have hr1 : IsSc1 U (r R) := (r_isScSmooth hU hR).isSc1
  set ψ₁ : E 0 → F 0 := fun y => g y - ρ R (r R y) (g y) with hψ₁def
  have hψ₁ : IsSc1 U ψ₁ := hfg.isSc1
  have hψ₁r : IsSc1 U (ψ₁ ∘ r R) :=
    (theorem_1_3_1' hU.isScDomain hU.isScDomain hr1 hψ₁ fun u hu => r_mem hR hu).1
  have hlev : levelMap (r R) 1 (0 : E 1) = 0 :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, r_zero hR h0O])
  -- `ψ₁ ∘ r = 0` near `0` in `U`
  have hev : ∀ᶠ y in 𝓝[U] (0 : E 0), (ψ₁ ∘ r R) y = 0 := by
    have hrc : Tendsto (r R) (𝓝[U] 0) (𝓝 0) := by
      have := (r_isScSmooth hU hR).isSc1.isSc0.continuousOn_base 0 h0
      rwa [ContinuousWithinAt, r_zero hR h0O] at this
    have h1 : ∀ᶠ y in 𝓝[U] (0 : E 0), r R y ∈ r R '' U → fb (r R y) = g (r R y) :=
      hrc.eventually hfg.eq_on
    filter_upwards [h1, self_mem_nhdsWithin] with y hy hyU
    have hryO : r R y ∈ r R '' U := ⟨y, hyU, rfl⟩
    have hK := hfK _ hryO
    simp only [Function.comp_apply, hψ₁def]
    rw [r_r hR hyU, ← hy hryO, ρ_eq_self_of_mem_K hR (r_mem hR hyU) hK, sub_self]
  have hev' : ((ψ₁ ∘ r R) ∘ E.toBase 1) =ᶠ[𝓝[E.lvlSet U 1] (0 : E 1)] fun _ => (0 : F 0) := by
    have ht : Tendsto (E.toBase 1) (𝓝[E.lvlSet U 1] (0 : E 1)) (𝓝[U] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h1 : Tendsto (E.toBase 1) (𝓝[E.lvlSet U 1] (0 : E 1)) (𝓝 (E.toBase 1 0)) :=
          ((E.toBase 1).continuous.tendsto 0).mono_left nhdsWithin_le_nhds
        rwa [map_zero] at h1
      · exact eventually_nhdsWithin_of_forall fun x hx => hx
    exact ht.eventually hev
  have hzero : HasFDerivWithinAt ((ψ₁ ∘ r R) ∘ E.toBase 1) (0 : E 1 →L[ℝ] F 0) (E.lvlSet U 1) 0 := by
    refine (hasFDerivWithinAt_const (0 : F 0) 0 (E.lvlSet U 1)).congr_of_eventuallyEq hev' ?_
    simp only [Function.comp_apply, map_zero, hψ₁def]
    rw [r_zero hR h0O, hg0, r_zero hR h0O, (ρ_isLinear hR h0).map_zero, sub_self]
  have hD0 : scDeriv U (ψ₁ ∘ r R) 0 = 0 := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
    rw [ContinuousLinearMap.zero_comp]
    exact huniq.eq (hψ₁r.isSc1With_scDeriv.hasFDerivWithinAt 0 h01) hzero
  have hchain := scDeriv_comp_apply' hU hU hr1 hψ₁ (fun u hu => r_mem hR hu) h01 h
  rw [hlev, hD0, zero_apply, hfg.scDeriv_sub_eq hg hg0 h0O] at hchain
  simpa only [sub_apply, ContinuousLinearMap.comp_apply] using hchain

include hfg in
/-- **Property (3) of a filler in terms of `Dg(0)`**: `(1 − ρ(0))Dg(0)` restricts to a topological
isomorphism `ker Dr(0) → ker ρ(0)`. -/
theorem exists_kerEquiv (hg : IsScSmooth U g) (hg0 : g 0 = 0) (h0O : (0 : E 0) ∈ r R '' U) :
    ∃ Φ : ↥(LinearMap.ker ((scDeriv U (r R) 0 : E 0 →L[ℝ] E 0) : E 0 →ₗ[ℝ] E 0)) ≃L[ℝ]
        ↥(LinearMap.ker ((ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0)),
      ∀ v, ((Φ v : ↥(LinearMap.ker ((ρCLM hR h0 : F 0 →L[ℝ] F 0) : F 0 →ₗ[ℝ] F 0))) : F 0) =
        scDeriv U g 0 v - ρCLM hR h0 (scDeriv U g 0 v) := by
  obtain ⟨Φ, hΦ⟩ := hfg.linearization
  refine ⟨Φ, fun v => ?_⟩
  rw [hΦ v, hfg.scDeriv_sub_eq hg hg0 h0O]
  rfl

include hfg in
/-- `ρ(0)Dg(0)Dr(0) = Dg(0)Dr(0)` (`Tf(0)` takes values in `ρ(0)F`). -/
theorem ρ_deriv_comp_r (hg : IsScSmooth U g) (hg0 : g 0 = 0) (h0O : (0 : E 0) ∈ r R '' U)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) (h : E 0) :
    ρCLM hR h0 (scDeriv U g 0 (scDeriv U (r R) 0 h)) = scDeriv U g 0 (scDeriv U (r R) 0 h) :=
  (sub_eq_zero.1 (hfg.deriv_comp_r_eq_zero hg hg0 h0O hfK h)).symm

include hfg in
/-- **Proposition 3.1.5 (preprint 3.5) (Filler)**: let `g` fill `f` with `g(0) = 0` (`f` a section of `K → O`).
Then `Tf(0) = Dg(0)|_{Dr(0)E} : Dr(0)E → ρ(0)F` (`fillerRestrict`) satisfies: (1) `Tf(0)` is
surjective iff `Dg(0)` is; (2) `Tf(0)` is Fredholm iff `Dg(0)` is, and `ind Tf(0) = ind Dg(0)`. -/
theorem proposition_3_1_5 (hg : IsScSmooth U g) (hg0 : g 0 = 0) (h0O : (0 : E 0) ∈ r R '' U)
    (hfK : ∀ x ∈ r R '' U, (x, fb x) ∈ R '' (U ×ˢ univ)) :
    ∃ h1 : ∀ x, ρCLM hR h0 (scDeriv U g 0 (scDeriv U (r R) 0 x)) = scDeriv U g 0 (scDeriv U (r R) 0 x),
      (Surjective (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1) ↔
          Surjective (scDeriv U g 0)) ∧
        (IsFredholm (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1) ↔
          IsFredholm (scDeriv U g 0)) ∧
        fredholmIndex (fillerRestrict (scDeriv U (r R) 0) (ρCLM hR h0) (scDeriv U g 0) h1) =
          fredholmIndex (scDeriv U g 0) := by
  obtain ⟨Φ, hΦ⟩ := hfg.exists_kerEquiv hg hg0 h0O
  exact ⟨hfg.ρ_deriv_comp_r hg hg0 h0O hfK, Polyfold.proposition_3_1_5_preprint (scDeriv_r_idem hU hR h0O)
    (ρCLM_idem hR h0 h0O) _ Φ hΦ⟩

include hfg in
/-- **`D(f ∘ r)(0) = Dg(0)Dr(0)`** (the text's "`Tg(0) = Tf(0)` on `T₀O`"): `f ∘ r = g ∘ r` near
`0`. -/
theorem scDeriv_section_comp_r (hg : IsScSmooth U g) (h0O : (0 : E 0) ∈ r R '' U)
    (hfr : IsSc1 U (fb ∘ r R)) :
    scDeriv U (fb ∘ r R) 0 = (scDeriv U g 0).comp (scDeriv U (r R) 0) := by
  have h01 : (0 : E 1) ∈ E.lvlSet U 1 := by rw [ScBanach.mem_lvlSet, map_zero]; exact h0
  have huniq := hU.isScDomain.uniqueDiffWithinAt 1 0 h01
  have hr1 : IsSc1 U (r R) := (r_isScSmooth hU hR).isSc1
  have hgr : IsSc1 U (g ∘ r R) :=
    (theorem_1_3_1' hU.isScDomain hU.isScDomain hr1 hg.isSc1 fun u hu => r_mem hR hu).1
  have hlev : levelMap (r R) 1 (0 : E 1) = 0 :=
    levelMap_eq_of_toBase_eq (by rw [map_zero, r_zero hR h0O])
  -- `f ∘ r = g ∘ r` near `0` in `U`
  have hev : ∀ᶠ y in 𝓝[U] (0 : E 0), (fb ∘ r R) y = (g ∘ r R) y := by
    have hrc : Tendsto (r R) (𝓝[U] 0) (𝓝 0) := by
      have := (r_isScSmooth hU hR).isSc1.isSc0.continuousOn_base 0 h0
      rwa [ContinuousWithinAt, r_zero hR h0O] at this
    filter_upwards [hrc.eventually hfg.eq_on, self_mem_nhdsWithin] with y hy hyU
    exact hy ⟨y, hyU, rfl⟩
  have hev' : ((fb ∘ r R) ∘ E.toBase 1) =ᶠ[𝓝[E.lvlSet U 1] (0 : E 1)] ((g ∘ r R) ∘ E.toBase 1) := by
    have ht : Tendsto (E.toBase 1) (𝓝[E.lvlSet U 1] (0 : E 1)) (𝓝[U] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have h1 : Tendsto (E.toBase 1) (𝓝[E.lvlSet U 1] (0 : E 1)) (𝓝 (E.toBase 1 0)) :=
          ((E.toBase 1).continuous.tendsto 0).mono_left nhdsWithin_le_nhds
        rwa [map_zero] at h1
      · exact eventually_nhdsWithin_of_forall fun x hx => hx
    exact ht.eventually hev
  have hD : scDeriv U (fb ∘ r R) 0 = scDeriv U (g ∘ r R) 0 := by
    apply ContinuousLinearMap.ext_of_comp_toBase_one (E := E)
    refine huniq.eq (hfr.isSc1With_scDeriv.hasFDerivWithinAt 0 h01) ?_
    refine (hgr.isSc1With_scDeriv.hasFDerivWithinAt 0 h01).congr_of_eventuallyEq hev' ?_
    have : (fb ∘ r R) (E.toBase 1 0) = (g ∘ r R) (E.toBase 1 0) := by
      simp only [Function.comp_apply, map_zero, r_zero hR h0O]
      exact hfg.eq_on.self_of_nhds h0O
    exact this
  rw [hD]
  ext h
  have := scDeriv_comp_apply' hU hU hr1 hg.isSc1 (fun u hu => r_mem hR hu) h01 h
  rw [hlev] at this
  rw [ContinuousLinearMap.comp_apply, this]

include hfg in
/-- **Remark 3.6.2 (preprint 3.49)**: on a smaller neighbourhood `W` of `0`, `f = g` on all of `O ∩ W` and
`g(y) = ρ(r(y))g(y)` for `y ∈ U ∩ W` implies `y ∈ O`. -/
theorem remark_3_6_2 : ∃ W : Set (E 0), IsOpen W ∧ (0 : E 0) ∈ W ∧
    (∀ x ∈ r R '' U ∩ W, fb x = g x) ∧
    ∀ y ∈ U ∩ W, g y = ρ R (r R y) (g y) → y ∈ r R '' U := by
  obtain ⟨W, hWsub, hWopen, h0W⟩ := mem_nhds_iff.1 (hfg.eq_on.and hfg.mem_of_fixed)
  exact ⟨W, hWopen, h0W, fun x hx => (hWsub hx.2).1 hx.1, fun y hy => (hWsub hy.2).2 hy.1⟩

end IsFillerOf

end Polyfold
