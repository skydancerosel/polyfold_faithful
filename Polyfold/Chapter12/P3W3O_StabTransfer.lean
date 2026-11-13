import Polyfold.Chapter12.P3W3O_SectionPull

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
p. 594: a step of the proof of the last sentence of **Theorem 12.5.3** (2017: Theorem 12.11),
the naturality of the propagation of orientations of Part I (§6.6) under a local strong bundle
isomorphism.

# Stabilized kernels carried along a local strong bundle isomorphism

Let `L : Y|U → Y'|U'` be a local strong bundle isomorphism over `ϕ : U → U'`, `f = Ψ ∘ f' ∘ ϕ` on
`U`, `c` a strong bundle chart of `Y'` with domain in `U'` and `cT = Ψ' ∘ Φ` the transported chart
(`LocalIso.transportChart`), which has the model `(K, U ◁ F, R)` of `c`.  If sections `S_q`, `sᵢ(q)`
of `Y` have in `cT` the principal parts of sections `S'_q`, `sᵢ'(q)` of `Y'` in `c`, then

* `LocalIso.principal_transportChart_eq`, `principal_transportChart_sectionAdd`: the principal
  parts of `S_q`, `f + S_q` in `cT` are those of `S'_q`, `f' + S'_q` in `c` on `O`;
* `LocalIso.isStabKernels_mpull`: **stabilized kernels of `(f', S', s')` along `ϕ ∘ y` in `c` are
  stabilized kernels of `(f, S, s)` along `y` in `cT`**, with the same subspaces `Λ`;
* `LocalIso.morPull_apply`: the identification `morPull : Or_x^{f'} ≃ Or_a^f` of P3F does not
  change the value of an orientation at an operator;
* `LocalIso.orRay_mpull`, `LocalIso.push_mpull`: **the push-forwards correspond under
  `morPull`**: `φ_*(morPull o) = morPull (φ'_* o)`.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter Module

noncomputable section

namespace Polyfold

open StrongRetr

universe u v u' v'

section ConjRefl

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Conjugating by the identities between two sets of operators** does not change the value at an
operator lying in both sets. -/
theorem LineOrientation.conj_refl_apply {C C' : Set (E →L[ℝ] F)} {hC : ∀ T ∈ C, T.IsFredholm}
    {hC' : ∀ T ∈ C', T.IsFredholm}
    (hmem : ∀ S' ∈ C', (((ContinuousLinearEquiv.refl ℝ F).symm : F →L[ℝ] F) ∘L S' ∘L
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E)) ∈ C)
    (o : LineOrientation (DetOn C hC)) {S : E →L[ℝ] F} (hS : S ∈ C) (hS' : S ∈ C') :
    o.conj (hC' := hC') (ContinuousLinearEquiv.refl ℝ E) (ContinuousLinearEquiv.refl ℝ F) hmem
      ⟨S, hS'⟩ = o ⟨S, hS⟩ := by
  have h : ∀ v, S (ContinuousLinearEquiv.refl ℝ E v) = ContinuousLinearEquiv.refl ℝ F (S v) :=
    fun _ => rfl
  rw [o.conj_apply _ _ hmem hS hS' h]
  exact ray_map_eq_self _ (fun w => (DFunLike.congr_fun (conjDet_refl h) w).trans
    (DFunLike.congr_fun (linDetEquivOfEq_self _ _) w)) _

end ConjRefl

section StabTransfer

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {X' : Type u'} [TopologicalSpace X'] [T2Space X'] [ParacompactSpace X'] {PX' : MPolyfold X'}
  {Y' : Type v'} [TopologicalSpace Y'] [T2Space Y'] [ParacompactSpace Y'] {P' : Y' → X'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle PX' P'}
  {f : X → Y} {f' : X' → Y'}

namespace StrongBundle.LocalIso

variable {U : Set X} {U' : Set X'} (L : LocalIso B B' U U')

/-! ### Principal parts in the transported chart -/

section Principal

variable {c : StrongBundleChart PX' P'} (hsub : c.φ.source ⊆ U')

/-- **The principal part of `S` in `cT` is that of `S'` in `c`** when `cT(S(x)) = c(S'(ϕ(x)))` in
the fibre components on the domain of `cT`. -/
theorem principal_transportChart_eq {S : X → Y} {S' : X' → Y'}
    (hSe : ∀ x ∈ (L.transportChart c hsub).φ.source,
      ((L.transportChart c hsub) (S x)).2 = (c (S' (L.ϕ x))).2)
    {w : c.φ.model.E 0} (hw : w ∈ c.φ.model.O) :
    (L.transportChart c hsub).principal S w = c.principal S' w := by
  have hws : c.φ.symm w ∈ c.φ.source := c.φ.symm_mapsTo hw
  have hwU : c.φ.symm w ∈ U' := hsub hws
  have hx : L.g (c.φ.symm w) ∈ (L.transportChart c hsub).φ.source := by
    refine ⟨L.base.mapsTo_inv hwU, ?_⟩
    change L.ϕ (L.g (c.φ.symm w)) ∈ c.φ.source
    rw [L.base.right_inv _ hwU]; exact hws
  change ((L.transportChart c hsub) (S (L.g (c.φ.symm w)))).2 = (c (S' (c.φ.symm w))).2
  rw [hSe _ hx, L.base.right_inv _ hwU]

/-- **The principal part of `f + S` in `cT` is that of `f' + S'` in `c`**, for `f = Ψ ∘ f' ∘ ϕ`
on `U`. -/
theorem principal_transportChart_sectionAdd (hfs : IsSection P f) (hfs' : IsSection P' f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) {S : X → Y} {S' : X' → Y'} (hS : IsSection P S)
    (hS' : IsSection P' S')
    (hSe : ∀ x ∈ (L.transportChart c hsub).φ.source,
      ((L.transportChart c hsub) (S x)).2 = (c (S' (L.ϕ x))).2)
    {w : c.φ.model.E 0} (hw : w ∈ c.φ.model.O) :
    (L.transportChart c hsub).principal (sectionAdd P f S) w =
      c.principal (sectionAdd P' f' S') w := by
  have hw' : w ∈ (L.transportChart c hsub).φ.model.O := by
    rw [L.transportChart_model_O]; exact hw
  rw [(L.transportChart c hsub).principal_sectionAdd hfs hS hw', c.principal_sectionAdd hfs' hS' hw,
    L.principal_transportChart c hsub hfL hfs' hw, L.principal_transportChart_eq hsub hSe hw]
  rfl

/-- **The linearizations agree**: `Lin` of `f + S` in `cT` is `Lin` of `f' + S'` in `c`. -/
theorem linAt_transportChart_sectionAdd (hf : B.IsScSmoothSection f)
    (hf' : B'.IsScSmoothSection f') (hc : B'.IsChart c) (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U)
    {S : X → Y} {S' : X' → Y'} (hS : B.IsScPlusSection S) (hS' : B'.IsScPlusSection S')
    (hSe : ∀ x ∈ (L.transportChart c hsub).φ.source,
      ((L.transportChart c hsub) (S x)).2 = (c (S' (L.ϕ x))).2)
    {z : c.φ.model.E 1} (hz : c.φ.model.E.toBase 1 z ∈ c.U)
    (v : ↥(rangeS (scDeriv c.U (r c.R) z))) :
    linAt c.U c.R ((L.transportChart c hsub).principal (sectionAdd P f S)) z v =
      linAt c.U c.R (c.principal (sectionAdd P' f' S')) z v := by
  have h1 : IsSc1 c.U ((L.transportChart c hsub).principal (sectionAdd P f S) ∘ r c.R) :=
    (hf.sectionAdd hS).isSc1_principal_comp_r (L.isChart_transportChart c hsub hc)
  have h2 : IsSc1 c.U (c.principal (sectionAdd P' f' S') ∘ r c.R) :=
    (hf'.sectionAdd hS').isSc1_principal_comp_r hc
  refine linAt_congr c.relOpen h1 h2 (fun u hu => ?_) hz v
  exact L.principal_transportChart_sectionAdd hsub hf.1 hf'.1 hfL hS.1 hS'.1 hSe
    (c.r_image ▸ hu)

end Principal

/-! ### Stabilized kernels -/

section Stab

variable {Q : Type*} [TopologicalSpace Q] {c : StrongBundleChart PX' P'} {hc : B'.IsChart c}
  (hsub : c.φ.source ⊆ U')

/-- **Stabilized kernels carried along `L`** (`IsStabKernels`, pp. 221–223): stabilized kernels
of `(f', S', s')` along `ϕ ∘ y` in the chart `c` are stabilized kernels of `(f, S, s)` along `y`
in the transported chart `cT = Ψ' ∘ Φ`, with the same subspaces, when `f = Ψ ∘ f' ∘ ϕ` on `U` and
`S_q`, `sᵢ(q)` have in `cT` the principal parts of `S'_q`, `sᵢ'(q)` in `c`. -/
theorem isStabKernels_mpull (hf : B.IsScSmoothSection f) (hf' : B'.IsScSmoothSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) {y : Q → X}
    (hy : ∀ q, y q ∈ (L.transportChart c hsub).φ.source) {S' : Q → X' → Y'} {k : ℕ}
    {s' : Fin k → Q → X' → Y'} {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}
    (hΛ : IsStabKernels f' c hc (fun q => L.ϕ (y q)) (fun q => (hy q).2) S' s' Λ)
    {S : Q → X → Y} {s : Fin k → Q → X → Y} (hS : ∀ q, B.IsScPlusSection (S q))
    (hs : ∀ i q, IsSection P (s i q))
    (hSe : ∀ q, ∀ x ∈ (L.transportChart c hsub).φ.source,
      ((L.transportChart c hsub) (S q x)).2 = (c (S' q (L.ϕ x))).2)
    (hse : ∀ i q, ∀ x ∈ (L.transportChart c hsub).φ.source,
      ((L.transportChart c hsub) (s i q x)).2 = (c (s' i q (L.ϕ x))).2) :
    IsStabKernels f (L.transportChart c hsub) (L.isChart_transportChart c hsub hc) y hy S s Λ where
  isScPlusSection := hS
  zero q := by
    have h0 := (c.isZeroAt_iff (hf'.sectionAdd (hΛ.isScPlusSection q)).1 (hy q).2).1 (hΛ.zero q)
    refine ((L.transportChart c hsub).isZeroAt_iff (hf.sectionAdd (hS q)).1 (hy q)).2 ?_
    exact (L.principal_transportChart_sectionAdd hsub hf.1 hf'.1 hfL (hS q).1
      (hΛ.isScPlusSection q).1 (hSe q) (c.φ.mapsTo_model _ (hy q).2)).trans h0
  isSection := hs
  exists_lift q := hΛ.exists_lift q
  spec q x hq hxc z hz T hT φ hφ := by
    subst hq
    have hzU : c.φ.model.E.toBase 1 z ∈ c.U := (chartPt c hc (hy q).2 z hz).mem_U
    refine hΛ.spec q rfl (hy q).2 z hz T (fun v => ?_) φ (fun μ => ?_)
    · exact (hT v).trans (L.linAt_transportChart_sectionAdd hsub hf hf' hc hfL (hS q)
        (hΛ.isScPlusSection q) (hSe q) hzU v)
    · refine (hφ μ).trans (Finset.sum_congr rfl fun i _ => ?_)
      exact congrArg (μ i • ·)
        (L.principal_transportChart_eq hsub (hse i q) (c.φ.mapsTo_model _ (hy q).2))

end Stab

/-! ### `morPull` and the values of orientations -/

section MorPull

variable {x : X'} {a : X}

set_option maxHeartbeats 2000000 in
-- the carried chart point and the original one have the same `T`, `K` only up to unfolding the
-- transported chart, which the unifier does at the default transparency
/-- **`morPull` does not change the value at an operator**: `morPull o` at `T ∈ Lin(f, a)` is `o`
at `T ∈ Lin(f', x)` (the two sets coincide). -/
theorem morPull_apply (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (p : ChartPoint B' x) (hp : p.c.φ.source ⊆ U') (ha : a ∈ U) (hϕ : L.ϕ a = x)
    (hlin : (L.mpullPt p hp ha hϕ).linSet f = p.linSet f') (o : p.Or f' hf')
    {T : ↥p.T →L[ℝ] ↥p.K} (hT : T ∈ (L.mpullPt p hp ha hϕ).linSet f) (hT' : T ∈ p.linSet f') :
    L.morPull hf hf' p hp ha hϕ hlin o ⟨T, hT⟩ = o ⟨T, hT'⟩ := by
  exact LineOrientation.conj_refl_apply (E := ↥p.T) (F := ↥p.K) (C := p.linSet f')
    (C' := (L.mpullPt p hp ha hϕ).linSet f) (hC := p.isFredholm_of_mem_linSet hf')
    (hC' := (L.mpullPt p hp ha hϕ).isFredholm_of_mem_linSet hf) (mcastT_mem hlin) o hT' hT

end MorPull

/-! ### The push-forwards correspond under `morPull` -/

section Push

variable {Q : Type*} [TopologicalSpace Q] {c : StrongBundleChart PX' P'} {hc : B'.IsChart c}
  (hsub : c.φ.source ⊆ U')

/-- **`orRay` under `morPull`**: reading `morPull o` in `λ(Λ)` through the carried stabilized
kernels (`isStabKernels_mpull`) is reading `o` through the original ones. -/
theorem orRay_mpull (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) {y : Q → X}
    (hy : ∀ q, y q ∈ (L.transportChart c hsub).φ.source) {S' : Q → X' → Y'} {k : ℕ}
    {s' : Fin k → Q → X' → Y'} {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}
    (hΛ : IsStabKernels f' c hc (fun q => L.ϕ (y q)) (fun q => (hy q).2) S' s' Λ)
    {S : Q → X → Y} {s : Fin k → Q → X → Y} (hS : ∀ q, B.IsScPlusSection (S q))
    (hs : ∀ i q, IsSection P (s i q))
    (hSe : ∀ q, ∀ x ∈ (L.transportChart c hsub).φ.source,
      ((L.transportChart c hsub) (S q x)).2 = (c (S' q (L.ϕ x))).2)
    (hse : ∀ i q, ∀ x ∈ (L.transportChart c hsub).φ.source,
      ((L.transportChart c hsub) (s i q x)).2 = (c (s' i q (L.ϕ x))).2)
    (q : Q) (hxs : y q ∈ PX.smoothSet) (hxs' : L.ϕ (y q) ∈ PX'.smoothSet)
    (z : c.φ.model.E 1) (hz : c.φ.model.E.toBase 1 z = c.φ (L.ϕ (y q)))
    (hlin : (L.mpullPt (chartPt c hc (hy q).2 z hz) hsub (hy q).1 rfl).linSet f =
      (chartPt c hc (hy q).2 z hz).linSet f')
    (o : (chartPt c hc (hy q).2 z hz).Or f' hf') :
    (L.isStabKernels_mpull hsub hf.isScSmooth hf'.isScSmooth hfL hy hΛ hS hs hSe hse).orRay hf q
        rfl hxs z hz (L.morPull hf hf' (chartPt c hc (hy q).2 z hz) hsub (hy q).1 rfl hlin o) =
      hΛ.orRay hf' q rfl hxs' z hz o := by
  have hΛT := L.isStabKernels_mpull hsub hf.isScSmooth hf'.isScSmooth hfL hy hΛ hS hs hSe hse
  have h0 : IsZeroAt P (sectionAdd P f (S q)) (y q) := hΛT.zero q
  let p := chartPt c hc (hy q).2 z hz
  let p' := chartPt (L.transportChart c hsub) (L.isChart_transportChart c hsub hc) (hy q) z hz
  have : CompleteSpace ↥p.T :=
    (fun p : ChartPoint B' (L.ϕ (y q)) => (inferInstance : CompleteSpace ↥p.T)) _
  have : CompleteSpace ↥p.K :=
    (fun p : ChartPoint B' (L.ϕ (y q)) => (inferInstance : CompleteSpace ↥p.K)) _
  have : CompleteSpace ↥p'.T :=
    (fun p : ChartPoint B (y q) => (inferInstance : CompleteSpace ↥p.T)) _
  have : CompleteSpace ↥p'.K :=
    (fun p : ChartPoint B (y q) => (inferInstance : CompleteSpace ↥p.K)) _
  let A : ↥p.T ≃L[ℝ] ↥p'.T := ContinuousLinearEquiv.refl ℝ ↥p.T
  let Γ : ↥p.K ≃L[ℝ] ↥p'.K := ContinuousLinearEquiv.refl ℝ ↥p.K
  let T := p.stabT hf' (hΛ.isScPlusSection q) (hΛ.zero q)
  let T' := p'.stabT hf (hS q) h0
  let φ := p.stabPhi (fun i => s' i q) (fun i => hΛ.isSection i q)
  let φ' := p'.stabPhi (fun i => s i q) (fun i => hs i q)
  have hTm := p.stabT_mem_linSet hf' (hΛ.isScPlusSection q) (hΛ.zero q) hxs'
  have hT'm := p'.stabT_mem_linSet hf (hS q) h0 hxs
  have hzU : c.φ.model.E.toBase 1 z ∈ c.U := p.mem_U
  have hconj : ∀ v, T' (A v) = Γ (T v) := fun v => Subtype.ext
    (L.linAt_transportChart_sectionAdd hsub hf.isScSmooth hf'.isScSmooth hc hfL (hS q)
      (hΛ.isScPlusSection q) (hSe q) hzU v)
  have hφconj : ∀ μ, φ' μ = Γ (φ μ) := fun μ => Subtype.ext (by
    refine (p'.coe_stabPhi _ _ μ).trans ((Finset.sum_congr rfl fun i _ => ?_).trans
      (p.coe_stabPhi _ _ μ).symm)
    exact congrArg (μ i • ·)
      (L.principal_transportChart_eq hsub (hse i q) (c.φ.mapsTo_model _ (hy q).2)))
  have hsq := hΛ.spec q rfl (hy q).2 z hz T (fun _ => rfl) φ (fun μ => p.coe_stabPhi _ _ μ)
  have hsq' := hΛT.spec q rfl (hy q) z hz T' (fun _ => rfl) φ' (fun μ => p'.coe_stabPhi _ _ μ)
  let tr : p.Or f' hf' ≃ p'.Or f hf := L.morPull hf hf' p hsub (hy q).1 rfl hlin
  have hval : ∀ o', p'.orEquivRay hf hT'm (tr o') =
      Module.Ray.map (conjDet A Γ hconj) (p.orEquivRay hf' hTm o') :=
    fun o' => LineOrientation.conj_apply (E := ↥p.T) (F := ↥p.K) (E' := ↥p'.T) (F' := ↥p'.K)
      (hC := p.isFredholm_of_mem_linSet hf') (hC' := p'.isFredholm_of_mem_linSet hf) A Γ
      (mcastT_mem hlin) o' hTm hT'm hconj
  have hfinT := (fun (d : StrongBundleChart PX P)
    (Λd : SubspaceFamily Q (d.φ.model.E 0 × (Fin k → ℝ))) => Λd.finiteDimensional q)
      (L.transportChart c hsub) Λ
  have hM' : ∀ v, kerEquivMap p'.T.subtypeL Subtype.val_injective hsq'.2
      (conjKerEquiv (A.prodCongr (ContinuousLinearEquiv.refl ℝ (Fin k → ℝ))) Γ
        (coprod_conj A Γ hconj hφconj) v) =
      (LinearEquiv.refl ℝ _) (kerEquivMap p.T.subtypeL Subtype.val_injective hsq.2 v) :=
    fun v => rfl
  have key := ray_trans_conj_aux (p.orEquivRay hf' hTm) (p'.orEquivRay hf hT'm) tr
    (conjDet A Γ hconj) (stabSign T) (stabSign T')
    (stabRayEquiv (p.isFredholm_of_mem_linSet hf' _ hTm) hsq.1
      (kerEquivMap p.T.subtypeL Subtype.val_injective hsq.2))
    (stabRayEquiv (p'.isFredholm_of_mem_linSet hf _ hT'm) hsq'.1
      (kerEquivMap p'.T.subtypeL Subtype.val_injective hsq'.2))
    (maxPowEquiv (LinearEquiv.refl ℝ ↥(Λ.L q))) hval (stabSign_conj A Γ hconj)
    (stabRayEquiv_conjDet A Γ hconj hφconj (p.isFredholm_of_mem_linSet hf' _ hTm)
      (p'.isFredholm_of_mem_linSet hf _ hT'm) hsq.1 hsq'.1
      (kerEquivMap p.T.subtypeL Subtype.val_injective hsq.2)
      (kerEquivMap p'.T.subtypeL Subtype.val_injective hsq'.2) (LinearEquiv.refl ℝ ↥(Λ.L q))
      hM') o
  exact key.trans (ray_map_eq_self _ (fun w => DFunLike.congr_fun maxPowEquiv_refl w) _)

/-- **The push-forwards correspond under `morPull`** (pp. 223–224): the push-forward `φ_*` along
the carried stabilized kernels (`isStabKernels_mpull`) of `morPull o` is `morPull` of the
push-forward `φ'_* o` along the original ones. -/
theorem push_mpull [SimplyConnectedSpace Q] [LocallyPathConnectedSpace Q]
    (hf : B.IsScFredholmSection f) (hf' : B'.IsScFredholmSection f')
    (hfL : EqOn f (L.Ψ ∘ f' ∘ L.ϕ) U) {y : Q → X}
    (hy : ∀ q, y q ∈ (L.transportChart c hsub).φ.source) {S' : Q → X' → Y'} {k : ℕ}
    {s' : Fin k → Q → X' → Y'} {Λ : SubspaceFamily Q (c.φ.model.E 0 × (Fin k → ℝ))}
    (hΛ : IsStabKernels f' c hc (fun q => L.ϕ (y q)) (fun q => (hy q).2) S' s' Λ)
    {S : Q → X → Y} {s : Fin k → Q → X → Y} (hS : ∀ q, B.IsScPlusSection (S q))
    (hs : ∀ i q, IsSection P (s i q))
    (hSe : ∀ q, ∀ x ∈ (L.transportChart c hsub).φ.source,
      ((L.transportChart c hsub) (S q x)).2 = (c (S' q (L.ϕ x))).2)
    (hse : ∀ i q, ∀ x ∈ (L.transportChart c hsub).φ.source,
      ((L.transportChart c hsub) (s i q x)).2 = (c (s' i q (L.ϕ x))).2)
    (a b : Q) (has : y a ∈ PX.smoothSet) (has' : L.ϕ (y a) ∈ PX'.smoothSet)
    (hbs : y b ∈ PX.smoothSet) (hbs' : L.ϕ (y b) ∈ PX'.smoothSet)
    (z₀ : c.φ.model.E 1) (hz₀ : c.φ.model.E.toBase 1 z₀ = c.φ (L.ϕ (y a)))
    (z₁ : c.φ.model.E 1) (hz₁ : c.φ.model.E.toBase 1 z₁ = c.φ (L.ϕ (y b)))
    (hlin₀ : (L.mpullPt (chartPt c hc (hy a).2 z₀ hz₀) hsub (hy a).1 rfl).linSet f =
      (chartPt c hc (hy a).2 z₀ hz₀).linSet f')
    (hlin₁ : (L.mpullPt (chartPt c hc (hy b).2 z₁ hz₁) hsub (hy b).1 rfl).linSet f =
      (chartPt c hc (hy b).2 z₁ hz₁).linSet f')
    (o : (chartPt c hc (hy a).2 z₀ hz₀).Or f' hf') :
    (L.isStabKernels_mpull hsub hf.isScSmooth hf'.isScSmooth hfL hy hΛ hS hs hSe hse).push hf a b
        rfl rfl has hbs z₀ hz₀ z₁ hz₁
        (L.morPull hf hf' (chartPt c hc (hy a).2 z₀ hz₀) hsub (hy a).1 rfl hlin₀ o) =
      L.morPull hf hf' (chartPt c hc (hy b).2 z₁ hz₁) hsub (hy b).1 rfl hlin₁
        (hΛ.push hf' a b rfl rfl has' hbs' z₀ hz₀ z₁ hz₁ o) := by
  rw [hΛ.push_eq_orRay]
  refine (DFunLike.congr_fun (IsStabKernels.push_eq_orRay
    (L.isStabKernels_mpull hsub hf.isScSmooth hf'.isScSmooth hfL hy hΛ hS hs hSe hse) hf a b rfl rfl
      has hbs z₀ hz₀ z₁ hz₁) _).trans ?_
  erw [Equiv.trans_apply, Equiv.trans_apply,
    L.orRay_mpull hsub hf hf' hfL hy hΛ hS hs hSe hse a has has' z₀ hz₀ hlin₀ o,
    Equiv.symm_apply_eq, L.orRay_mpull hsub hf hf' hfL hy hΛ hS hs hSe hse b hbs hbs' z₁ hz₁ hlin₁,
    Equiv.apply_symm_apply]
  rfl

end Push

end StrongBundle.LocalIso

end StabTransfer

end Polyfold
