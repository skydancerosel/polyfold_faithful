import Polyfold.Chapter6.ProductSectionOrientation2021d

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), §6.6, p. 276:
**Remark 6.6.19** (preprint Remark 6.42, p. 230), continued: a push-forward of `f` along a path
`γ` of `X` lifts to a push-forward of `f̃` along `(τ, γ)` in the product chart, which carries the
product orientation `e ∧ o` to the product orientation of the push-forward of `o`.
-/

open Module TensorProduct Bundle Topology Set Filter

noncomputable section

namespace Polyfold

universe u v

section ProdPush

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] {f : X → Y}

/-- **The product orientation in the chart point of the product chart with a given lift**
`z' = (t, z)`: `prodOrFirst₀` over `chartPt c hc hx z hz`. -/
def prodOrLift {c : StrongBundleChart PX P} (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source)
    (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ x) (t : Fin 1 → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X))
    (hxc : ((t, x) : (Fin 1 → ℝ) × X) ∈ (prodChart c q₀).φ.source)
    (z' : (prodChart c q₀).φ.model.E 1)
    (hz' : (prodChart c q₀).φ.model.E.toBase 1 z' = (prodChart c q₀).φ (t, x))
    (hzz : z' = (t, z)) (hf : B.IsScFredholmSection f) (hxs : x ∈ PX.smoothSet)
    (hne : ((chartPt c hc hx z hz).linSet f).Nonempty) (o : (chartPt c hc hx z hz).Or f hf) :
    (chartPt (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀) hxc z' hz').Or
      (paramLift (n := 1) f hf.isScSmooth.1) hf.param := by
  subst hzz
  exact (chartPt c hc hx z hz).prodOrFirst₀ t q₀ hf hxs hne o

namespace IsStabKernels

variable {Q : Type*} [TopologicalSpace Q] {c : StrongBundleChart PX P} {hc : B.IsChart c}
  {y : Q → X} {hy : ∀ q, y q ∈ c.φ.source} {S : Q → X → Y} {k : ℕ} {s : Fin k → Q → X → Y}
  {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}

/-- **The product orientation read in `λ((ℝ × Λ)_q)`** is `w ↦ ê ∧ J(w)` of the orientation read
in `λ(Λ_q)`: `orRay_{f̃} (e ∧ o) = ê ∧ J(orRay_f o)`. -/
theorem orRay_prodLift (hΛ : IsStabKernels f c hc y hy S s Λ) (hf : B.IsScFredholmSection f)
    (τ : Q → (Fin 1 → ℝ)) (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) (q : Q)
    {x : X} (hq : y q = x) (hx : x ∈ PX.smoothSet) (z : c.φ.model.E 1)
    (hz : c.φ.model.E.toBase 1 z = c.φ x) {t : Fin 1 → ℝ} (hτ : τ q = t)
    (hq' : ((τ q, y q) : (Fin 1 → ℝ) × X) = (t, x))
    (hx' : ((t, x) : (Fin 1 → ℝ) × X) ∈ ((rnPolyfold 1).prod PX).smoothSet)
    (z' : (prodChart c q₀).φ.model.E 1)
    (hz' : (prodChart c q₀).φ.model.E.toBase 1 z' = (prodChart c q₀).φ (t, x))
    (hzz : z' = (t, z)) (hne : ((chartPt c hc (hq ▸ hy q) z hz).linSet f).Nonempty)
    (o : (chartPt c hc (hq ▸ hy q) z hz).Or f hf) :
    (hΛ.prodLift hf τ q₀).orRay hf.param q hq' hx' z' hz'
        (prodOrLift hc (hq ▸ hy q) z hz t q₀ (mem_prodChart_source q₀ (hq ▸ hy q) t) z' hz' hzz
          hf hx hne o) =
      Module.Ray.map (Λ.prodLineWedgeEquiv q) (hΛ.orRay hf q hq hx z hz o) := by
  subst hq hτ hzz
  let p := chartPt c hc (hy q) z hz
  have h0 : IsZeroAt P (sectionAdd P f (S q)) (y q) := hΛ.zero q
  have hT := p.stabT_mem_linSet hf (hΛ.isScPlusSection q) h0 hx
  have hsq := hΛ.spec q rfl (hy q) z hz (p.stabT hf (hΛ.isScPlusSection q) h0) (fun _ => rfl)
    (p.stabPhi (fun i => s i q) (fun i => hΛ.isSection i q)) (fun μ => p.coe_stabPhi _ _ μ)
  have hΛ' := hΛ.prodLift hf τ q₀
  have h0' := hΛ'.zero q
  have hT' := (p.prodPt (τ q) q₀).stabT_mem_linSet hf.param (hΛ'.isScPlusSection q) h0' hx'
  have hsq' := hΛ'.spec q rfl (mem_prodChart_source q₀ (hy q) (τ q)) (τ q, z) hz'
    ((p.prodPt (τ q) q₀).stabT hf.param (hΛ'.isScPlusSection q) h0') (fun _ => rfl)
    ((p.prodPt (τ q) q₀).stabPhi (fun i => paramLift (n := 1) (s i q) (hΛ.isSection i q))
      (fun i => hΛ'.isSection i q)) (fun μ => (p.prodPt (τ q) q₀).coe_stabPhi _ _ μ)
  exact p.stabRay_prodOrFirst₀_aux (τ q) q₀ hf hx o hT
    (p.stabPhi (fun i => s i q) (fun i => hΛ.isSection i q)) hsq.1 Λ q hsq.2
    (p.stabT_prodPt (τ q) q₀ hf (hΛ.isScPlusSection q) h0 (hΛ'.isScPlusSection q) h0') hT'
    (p.stabPhi_prodPt (τ q) q₀ (fun i => s i q) (fun i => hΛ.isSection i q)
      (fun i => hΛ'.isSection i q)) hsq'.1 hsq'.2

end IsStabKernels

end ProdPush

/-! ### The lift of a push-forward -/

section Push

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))] {f : X → Y}
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))]

omit [TopologicalSpace X] [T2Space X] [ParacompactSpace X] [TopologicalSpace Y] [T2Space Y]
  [ParacompactSpace Y] [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × X)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × X → X))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × X))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace (pullbackProj P (Prod.snd : (Fin n → ℝ) × X → X))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × X) → (Fin n → ℝ) × X))] in
/-- Folding `e = A ⬝ (C ⬝ D⁻¹)`: `C(A(x)) = D(y)` gives `e(x) = y`. -/
theorem equiv_trans_trans_symm_apply_of {α β γ δ : Sort*} {A : α ≃ β} {C : β ≃ γ} {D : δ ≃ γ}
    {x : α} {y : δ} (h : C (A x) = D y) : (A.trans (C.trans D.symm)) x = y := by
  rw [Equiv.trans_apply, Equiv.trans_apply, h, Equiv.symm_apply_apply]

/-- **The product orientation `e ∧ o` of `f̃` at `(t, x)`, read in the product chart** over a
chart `c` of `P` at the smooth point `x` (`prodOrLift` for the chosen lifts of `chartPtOf`). -/
def prodOrOf {c : StrongBundleChart PX P} (hc : B.IsChart c) {x : X} (hx : x ∈ c.φ.source)
    (hs : x ∈ PX.smoothSet) (t : Fin 1 → ℝ)
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) (hf : B.IsScFredholmSection f)
    (hne : ((chartPtOf c hc hx hs).linSet f).Nonempty) (o : (chartPtOf c hc hx hs).Or f hf) :
    (chartPtOf (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀)
      (mem_prodChart_source q₀ hx t) (prod_rn_mem_smoothSet_iff.2 hs)).Or
      (paramLift (n := 1) f hf.isScSmooth.1) hf.param :=
  prodOrLift hc hx _ (exists_lift_of_smooth c hx hs).choose_spec t q₀ _ _
    (exists_lift_of_smooth (prodChart c q₀) (mem_prodChart_source q₀ hx t)
      (prod_rn_mem_smoothSet_iff.2 hs)).choose_spec
    (prodChart_lift_eq _ (exists_lift_of_smooth c hx hs).choose_spec t q₀ _
      (exists_lift_of_smooth (prodChart c q₀) (mem_prodChart_source q₀ hx t)
        (prod_rn_mem_smoothSet_iff.2 hs)).choose_spec) hf hs hne o

/-- **A push-forward of `f` along `γ` lifts to a push-forward of `f̃` along `(τ, γ)`** in the
product chart, which carries `e ∧ o` to `e ∧ (push-forward of o)` (2021 Remark 6.6.19: the
convention is compatible with the choices made in the construction). The data are the lifts
`liftProd` of the sections and the kernels `ℝ × Λ`. -/
theorem IsPush.prodLift {hf : B.IsScFredholmSection f} {c : StrongBundleChart PX P}
    {hc : B.IsChart c} {γ : (Fin 1 → ℝ) → X}
    {hγ : ∀ q ∈ Icc (0 : Fin 1 → ℝ) 1, γ q ∈ c.φ.source} {x₀ x₁ : X} {h₀ : γ (pt1 0) = x₀}
    {h₁ : γ (pt1 1) = x₁} {hx₀ : x₀ ∈ c.φ.source} {hx₁ : x₁ ∈ c.φ.source}
    {hs₀ : x₀ ∈ PX.smoothSet} {hs₁ : x₁ ∈ PX.smoothSet}
    {e : (chartPtOf c hc hx₀ hs₀).Or f hf ≃ (chartPtOf c hc hx₁ hs₁).Or f hf}
    (he : IsPush f hf c hc γ hγ h₀ h₁ hx₀ hx₁ hs₀ hs₁ e) (τ : (Fin 1 → ℝ) → (Fin 1 → ℝ))
    (q₀ : pullbackSpace P (Prod.snd : (Fin 1 → ℝ) × X → X)) {t₀ t₁ : Fin 1 → ℝ}
    (ht₀ : τ (pt1 0) = t₀) (ht₁ : τ (pt1 1) = t₁)
    (hne₀ : ((chartPtOf c hc hx₀ hs₀).linSet f).Nonempty)
    (hne₁ : ((chartPtOf c hc hx₁ hs₁).linSet f).Nonempty) :
    ∃ e' : (chartPtOf (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀)
          (mem_prodChart_source q₀ hx₀ t₀) (prod_rn_mem_smoothSet_iff.2 hs₀)).Or
          (paramLift (n := 1) f hf.isScSmooth.1) hf.param ≃
        (chartPtOf (B := prodBundle B) (prodChart c q₀) (isChart_prodChart hc q₀)
          (mem_prodChart_source q₀ hx₁ t₁) (prod_rn_mem_smoothSet_iff.2 hs₁)).Or
          (paramLift (n := 1) f hf.isScSmooth.1) hf.param,
      IsPush (B := prodBundle B) (paramLift (n := 1) f hf.isScSmooth.1) hf.param
        (prodChart c q₀) (isChart_prodChart hc q₀) (fun q => (τ q, γ q))
        (fun q hq => mem_prodChart_source q₀ (hγ q hq) (τ q))
        (Prod.ext ht₀ h₀ : ((τ (pt1 0), γ (pt1 0)) : (Fin 1 → ℝ) × X) = (t₀, x₀))
        (Prod.ext ht₁ h₁ : ((τ (pt1 1), γ (pt1 1)) : (Fin 1 → ℝ) × X) = (t₁, x₁))
        (mem_prodChart_source q₀ hx₀ t₀) (mem_prodChart_source q₀ hx₁ t₁)
        (prod_rn_mem_smoothSet_iff.2 hs₀) (prod_rn_mem_smoothSet_iff.2 hs₁) e' ∧
      ∀ o, e' (prodOrOf hc hx₀ hs₀ t₀ q₀ hf hne₀ o) = prodOrOf hc hx₁ hs₁ t₁ q₀ hf hne₁ (e o) := by
  obtain ⟨S, hS, hz, k, s, hs, Λ, hΛ, rfl⟩ := he
  have hΛ' := hΛ.prodLift hf (fun q : Icc (0 : Fin 1 → ℝ) 1 => τ q) q₀
  have hx₀' : ((t₀, x₀) : (Fin 1 → ℝ) × X) ∈ ((rnPolyfold 1).prod PX).smoothSet :=
    prod_rn_mem_smoothSet_iff.2 hs₀
  have hx₁' : ((t₁, x₁) : (Fin 1 → ℝ) × X) ∈ ((rnPolyfold 1).prod PX).smoothSet :=
    prod_rn_mem_smoothSet_iff.2 hs₁
  have hl₀ := (exists_lift_of_smooth c hx₀ hs₀).choose_spec
  have hl₁ := (exists_lift_of_smooth c hx₁ hs₁).choose_spec
  have hl₀' := (exists_lift_of_smooth (prodChart c q₀) (mem_prodChart_source q₀ hx₀ t₀)
    hx₀').choose_spec
  have hl₁' := (exists_lift_of_smooth (prodChart c q₀) (mem_prodChart_source q₀ hx₁ t₁)
    hx₁').choose_spec
  refine ⟨hΛ'.push hf.param iccZero iccOne (Prod.ext ht₀ h₀) (Prod.ext ht₁ h₁) hx₀' hx₁' _ hl₀'
      _ hl₁',
    ⟨liftProd (n := 1) S hS.1, isScPlusSection_liftProd hS, ?_, k,
      fun i => liftProd (n := 1) (s i) (hs i).1, fun i => isScPlusSection_liftProd (hs i),
      Λ.prodLine, hΛ', rfl⟩, fun o => ?_⟩
  · refine hz.mono fun q hq => ?_
    have h1 := (isZeroAt_pullback_iff_pullbackSlice
      ((isSection_pullbackLift _).sectionAdd hS.1) q (γ q)).1 hq
    rw [pullbackSlice_sectionAdd_paramLift hf.isScSmooth.1 hS.1] at h1
    refine (isZeroAt_pullback_iff_pullbackSlice
      ((isSection_pullbackLift _).sectionAdd (isSection_liftProd S hS.1)) q (τ q, γ q)).2 ?_
    rw [pullbackSlice_sectionAdd_paramLift (isSection_pullbackLift _) (isSection_liftProd S hS.1),
      pullbackSlice_liftProd, sectionAdd_paramLift hf.isScSmooth.1 (hS.1.pullbackSlice q)]
    exact (isZeroAt_pullback_iff_pullbackSlice (isSection_pullbackLift _) (τ q) (γ q)).2 h1
  · have ha := hΛ.orRay_prodLift hf (fun q : Icc (0 : Fin 1 → ℝ) 1 => τ q) q₀ iccZero h₀ hs₀
      _ hl₀ ht₀ (Prod.ext ht₀ h₀) hx₀' _ hl₀' (prodChart_lift_eq _ hl₀ t₀ q₀ _ hl₀') hne₀ o
    have hb := hΛ.orRay_prodLift hf (fun q : Icc (0 : Fin 1 → ℝ) 1 => τ q) q₀ iccOne h₁ hs₁
      _ hl₁ ht₁ (Prod.ext ht₁ h₁) hx₁' _ hl₁' (prodChart_lift_eq _ hl₁ t₁ q₀ _ hl₁') hne₁
      (hΛ.push hf iccZero iccOne h₀ h₁ hs₀ hs₁ _ hl₀ _ hl₁ o)
    have hcont := equiv_trans_trans_symm_apply
      (DFunLike.congr_fun (hΛ.push_eq_orRay hf iccZero iccOne h₀ h₁ hs₀ hs₁ _ hl₀ _ hl₁) o).symm
    have key : Λ.prodLine.contEquiv iccZero iccOne
        ((hΛ'.orRay hf.param iccZero (Prod.ext ht₀ h₀) hx₀' _ hl₀')
          (prodOrOf hc hx₀ hs₀ t₀ q₀ hf hne₀ o)) =
        (hΛ'.orRay hf.param iccOne (Prod.ext ht₁ h₁) hx₁' _ hl₁')
          (prodOrOf hc hx₁ hs₁ t₁ q₀ hf hne₁
            (hΛ.push hf iccZero iccOne h₀ h₁ hs₀ hs₁ _ hl₀ _ hl₁ o)) :=
      ((congrArg (Λ.prodLine.cont iccZero iccOne) ha).trans
        (Λ.cont_prodLine iccZero iccOne _)).trans
        ((congrArg (Module.Ray.map (Λ.prodLineWedgeEquiv iccOne)) hcont).trans hb.symm)
    have hp := hΛ'.push_eq_orRay hf.param iccZero iccOne (Prod.ext ht₀ h₀)
      (Prod.ext ht₁ h₁) hx₀' hx₁' _ hl₀' _ hl₁'
    rw [hp]
    exact equiv_trans_trans_symm_apply_of key

end Push

end Polyfold
