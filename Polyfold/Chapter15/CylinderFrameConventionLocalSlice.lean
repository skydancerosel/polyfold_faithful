import Polyfold.Chapter15.CylinderEndCanonical
import Polyfold.Chapter6.IntervalSliceFrames
import Polyfold.Chapter15.CylinderFrameConventionLocalRestr

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §15.4, p. 703: the proof
of **Corollary 15.4.4**, with **Remark 6.6.19** (p. 276).

# The linearization of `f̃ − s̃` on the slice directions, for local sc⁺-sections

## The text, paraphrased

(p. 703) Near `(i, x)`, `i ∈ {0, 1}`, a sheet of the cobordism is `M̃ = {f̃ = s̃}`, and its
boundary is `{i} × M` with `M = {f = s̃(i, ·)}`.

## What is formalized (namespace `Polyfold.SBLocalization`)

* **`subDeriv_ivChart_restrictInter_slice`**: let `s` be an sc⁺-section of `W` over an open
  `O ⊆ X` and `s̃` an sc⁺-section of `W̃` over an open `Õ ⊆ [0, 1] × X` with `s̃(q, ·) = s`
  where both are defined.  In the product chart `χ_b × φ` restricted to `Õ`, at `(q, y)`, the
  derivative of the principal part of `f̃ − s̃` on a vector `(0, v)` is the derivative of the
  principal part of `f − s` on `v`, in the chart `φ` restricted to `O` (the chain rule for
  `u ↦ (χ_b(q), u)`).

The sections `s`, `s̃` are given on open sets only.
-/

set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false

open Set Function Topology Module

noncomputable section

namespace Polyfold

universe u

namespace SBLocalization

open StrongBundle StrongRetr MPolyfold Linearization15 EpGroupoid SEP UnitCube

variable {A : SEP.{u}} {f : A.Obj → A.W}

set_option maxHeartbeats 1600000 in
-- the product chart and its restriction are unfolded
/-- **`(f̃ − s̃)'(q, y)(0, v) = (f − s)'(y) v`** (2021 p. 703) for sc⁺-sections `s` on an open
`O ⊆ X` and `s̃` on an open `Õ ⊆ [0, 1] × X` with `s̃(q, ·) = s`: the derivative of the principal
part of `f̃ − s̃` in the product chart `χ_b × φ` restricted to `Õ`, on a vector `(0, v)`, is the
derivative of the principal part of `f − s` in the chart `φ` restricted to `O`, on `v`. -/
theorem subDeriv_ivChart_restrictInter_slice (hf : A.B.IsScSmoothSection f)
    (hf' : (A.cubeSEP 1).B.IsScSmoothSection (cubeLiftEp (n := 1) f hf.1))
    {O : Set A.Obj} (hO : IsOpen O) {s : A.Obj → A.W} (hs : IsScPlusSectionOn A s O)
    {O' : Set (A.cubeSEP 1).Obj} (hO' : IsOpen O') {s' : (A.cubeSEP 1).Obj → (A.cubeSEP 1).W}
    (hs' : IsScPlusSectionOn (A.cubeSEP 1) s' O') (q : Fin 1 → unitInterval)
    (hss : ∀ y ∈ O, ((q, y) : (A.cubeSEP 1).Obj) ∈ O' → cubeVal (s' (q, y)) = ((q, y), s y))
    {y : A.Obj} (p : ChartPoint A.B y) (hyO : y ∈ O) (hyO' : ((q, y) : (A.cubeSEP 1).Obj) ∈ O')
    (b : Fin 1 → Bool) (ht : q ∈ (chart b).source)
    (q₀ : pullbackSpace A.P (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj))
    (v : p.c.φ.model.E 0) :
    subDeriv (A := A.cubeSEP 1) ((ivChart b p.c q₀).restrictInter hO')
        (cubeLiftEp (n := 1) f hf.1) s'
        (((chart b q : Fin 1 → ℝ), p.z) : (ivChart b p.c q₀).φ.model.E 1)
        (((0 : Fin 1 → ℝ), v) : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
      subDeriv (p.c.restrictInter hO) f s p.z v := by
  have := MPolyfold.paracompactSpace_prod (cubePolyfold 1) A.X.PObj
  have := A.B.paracompactSpace_pullback ((cubePolyfold 1).prod A.X.PObj)
    (Prod.snd : (Fin 1 → unitInterval) × A.Obj → A.Obj)
  -- the open set where both sections are defined
  obtain ⟨V₀, hV₀def⟩ : ∃ V₀ : Set A.Obj,
      V₀ = O ∩ {y' | ((q, y') : (A.cubeSEP 1).Obj) ∈ O'} := ⟨_, rfl⟩
  have hV₀ : IsOpen V₀ := by
    rw [hV₀def]
    exact hO.inter (hO'.preimage (continuous_const.prodMk continuous_id))
  have hyV₀ : y ∈ V₀ := by rw [hV₀def]; exact ⟨hyO, hyO'⟩
  have hV₀O : V₀ ⊆ O := by rw [hV₀def]; exact inter_subset_left
  have hV₀O' : ∀ y' ∈ V₀, ((q, y') : (A.cubeSEP 1).Obj) ∈ O' := fun y' hy' => by
    rw [hV₀def] at hy'; exact hy'.2
  -- the charts
  set c₀ := p.c.restrictInter hV₀ with hc₀def
  set c₁ := p.c.restrictInter hO with hc₁def
  have hc₀ : A.B.IsChart c₀ := p.isChart.restrictInter hV₀
  have hc₁ : A.B.IsChart c₁ := p.isChart.restrictInter hO
  have hsub₀ : c₀.φ.source ⊆ O := (p.c.restrictInter_source_subset hV₀).trans hV₀O
  have hsub₁ : c₁.φ.source ⊆ O := p.c.restrictInter_source_subset hO
  have hpc : (A.cubeSEP 1).B.IsChart (ivChart b p.c q₀) := isChart_ivChart b p.isChart q₀
  set pc₁ : StrongBundleChart (A.cubeSEP 1).X.PObj (A.cubeSEP 1).P :=
    (ivChart b p.c q₀).restrictInter hO' with hpc₁def
  have hpc₁ : (A.cubeSEP 1).B.IsChart pc₁ := hpc.restrictInter hO'
  have hsub' : pc₁.φ.source ⊆ O' := (ivChart b p.c q₀).restrictInter_source_subset hO'
  have hH := isSc1_sub_comp_r (A := A.cubeSEP 1) hf' hs' hpc₁ hsub'
  have hg₀ := isSc1_sub_comp_r hf hs hc₀ hsub₀
  have hg₁ := isSc1_sub_comp_r hf hs hc₁ hsub₁
  -- the points of `c₀.U`
  have hU₀ : ∀ w ∈ c₀.U, w ∈ p.c.U ∧ ∃ y' ∈ p.c.φ.source, y' ∈ V₀ ∧ r p.c.R w = p.c.φ y' := by
    intro w hw
    have hw' := (Set.ext_iff.1 (p.c.restrictInter_U hV₀) w).1 hw
    obtain ⟨hwU, y', hy', hy'w⟩ := hw'
    exact ⟨hwU, y', hy'.1, hy'.2, hy'w.symm⟩
  have hU₀₁ : c₀.U ⊆ c₁.U := fun w hw => by
    have h := hU₀ w hw
    obtain ⟨hwU, y', hy', hy'V, hy'w⟩ := h
    exact (Set.ext_iff.1 (p.c.restrictInter_U hO) w).2
      ⟨hwU, y', ⟨hy', hV₀O hy'V⟩, hy'w.symm⟩
  -- the slice inclusion
  set a : Fin 1 → ℝ := (chart b q : Fin 1 → ℝ) with ha
  set ι : p.c.φ.model.E 0 → (ivChart b p.c q₀).φ.model.E 0 :=
    scPair (E := p.c.φ.model.E) (F := rnSc 1) (G := p.c.φ.model.E) (fun _ => a) _root_.id
    with hι
  have hdom := c₀.relOpen.isScDomain
  have hιs : IsScSmooth (E := p.c.φ.model.E) (F := (ivChart b p.c q₀).φ.model.E) c₀.U ι :=
    IsScSmooth.scPair hdom (isScSmooth_const_of_mem_smooth hdom (mem_smooth_rnSc a))
      (isScSmooth_id hdom)
  have hι1 : IsSc1 (E := p.c.φ.model.E) (F := (ivChart b p.c q₀).φ.model.E) c₀.U ι := hιs.isSc1
  have hmaps : MapsTo ι c₀.U pc₁.U := fun w hw => by
    have h := hU₀ w hw
    obtain ⟨hwU, y', hy', hy'V, hy'w⟩ := h
    refine (Set.ext_iff.1 ((ivChart b p.c q₀).restrictInter_U hO') (ι w)).2
      ⟨show ((a, w) : (Fin 1 → ℝ) × p.c.φ.model.E 0) ∈ (chart b).model.O ×ˢ p.c.U from
      ⟨chart_mem_modelO ht, hwU⟩, ((q, y') : (Fin 1 → unitInterval) × A.Obj),
      ⟨⟨ht, hy'⟩, hV₀O' y' hy'V⟩, ?_⟩
    change (((chart b q : Fin 1 → ℝ), p.c.φ y') : (Fin 1 → ℝ) × p.c.φ.model.E 0) =
      (a, r p.c.R w)
    rw [hy'w]
  have hz : p.z ∈ p.c.φ.model.E.lvlSet c₀.U 1 := (p.restr hV₀ hyV₀).mem_U
  have hcomp := theorem_1_3_1 c₀.relOpen pc₁.relOpen hι1 hH hmaps
  have hchain := scDeriv_comp_apply' c₀.relOpen pc₁.relOpen hι1 hH hmaps hz v
  have hlvl : levelMap (E := p.c.φ.model.E) (F := (ivChart b p.c q₀).φ.model.E) ι 1 p.z =
      (p.ivPt b ht q₀).z := by
    apply (ivChart b p.c q₀).φ.model.E.toBase_injective 1
    refine (IsSc0.toBase_levelMap (hιs 0) (x := p.z) hz).trans ?_
    exact (p.ivPt_toBase b ht q₀).symm
  have hDι : scDeriv (E := p.c.φ.model.E) (F := (ivChart b p.c q₀).φ.model.E) c₀.U ι p.z =
      ContinuousLinearMap.inr ℝ (Fin 1 → ℝ) (p.c.φ.model.E 0) :=
    scDeriv_eq_of_hasFDerivAt c₀.relOpen hι1 hz
      ((hasFDerivAt_const a _).prodMk (hasFDerivAt_id _))
  have e0 : scDeriv pc₁.U ((fun u => pc₁.principal (cubeLiftEp (n := 1) f hf.1) u -
        pc₁.principal s' u) ∘ r pc₁.R) (p.ivPt b ht q₀).z
        (ContinuousLinearMap.inr ℝ (Fin 1 → ℝ) (p.c.φ.model.E 0) v) =
      scDeriv pc₁.U ((fun u => pc₁.principal (cubeLiftEp (n := 1) f hf.1) u -
        pc₁.principal s' u) ∘ r pc₁.R)
        (levelMap (E := p.c.φ.model.E) (F := (ivChart b p.c q₀).φ.model.E) ι 1 p.z)
        (scDeriv (E := p.c.φ.model.E) (F := (ivChart b p.c q₀).φ.model.E) c₀.U ι p.z v) :=
    congrArg₂ (fun (z' : (ivChart b p.c q₀).φ.model.E 1) (u : (ivChart b p.c q₀).φ.model.E 0) =>
      scDeriv pc₁.U ((fun u => pc₁.principal (cubeLiftEp (n := 1) f hf.1) u -
        pc₁.principal s' u) ∘ r pc₁.R) z' u) hlvl.symm
      (congrArg (fun M : p.c.φ.model.E 0 →L[ℝ] (ivChart b p.c q₀).φ.model.E 0 => M v) hDι).symm
  -- the composite is the principal part of `f − s`
  have hHι : EqOn (((fun u => pc₁.principal (cubeLiftEp (n := 1) f hf.1) u -
      pc₁.principal s' u) ∘ r pc₁.R) ∘ ι)
      ((fun u => c₀.principal f u - c₀.principal s u) ∘ r c₀.R) c₀.U := fun w hw => by
    have h := hU₀ w hw
    obtain ⟨hwU, y', hy', hy'V, hy'w⟩ := h
    have hy'eq : p.c.φ.symm (r p.c.R w) = y' := by
      rw [hy'w]; exact p.c.φ.symm_apply_apply hy'
    have hq : (chart b).symm a = q := (chart b).symm_apply_apply ht
    have h1 : (s' ((chart b).symm a, p.c.φ.symm (r p.c.R w))).1.2 =
        s (p.c.φ.symm (r p.c.R w)) := by
      rw [hq, hy'eq]
      exact congrArg Prod.snd (hss y' (hV₀O hy'V) (hV₀O' y' hy'V))
    change (p.c ((cubeLiftEp (n := 1) f hf.1)
        ((chart b).symm a, p.c.φ.symm (r p.c.R w))).1.2).2 -
      (p.c (s' ((chart b).symm a, p.c.φ.symm (r p.c.R w))).1.2).2 =
      (p.c (f (p.c.φ.symm (r p.c.R w)))).2 - (p.c (s (p.c.φ.symm (r p.c.R w)))).2
    rw [h1]
    rfl
  have e1 := scDeriv_eq_of_eqOn_relOpen c₀.relOpen hcomp.1 hg₀ subset_rfl subset_rfl hHι hz
  have e2 := scDeriv_eq_of_eqOn_relOpen c₀.relOpen hg₀ hg₁ subset_rfl hU₀₁
    (fun _ _ => rfl) hz
  have e3 := congrArg (fun M : p.c.φ.model.E 0 →L[ℝ] p.c.F 0 => M v) (e1.trans e2)
  exact (e0.trans hchain).trans e3

end SBLocalization

end Polyfold
