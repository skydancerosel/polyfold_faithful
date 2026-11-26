import Polyfold.Chapter18.MultisectionConstructionTextAtomic
import Polyfold.Chapter12.OrientationGeneralizedIsoTopology
import Polyfold.Chapter13.ScPlusSectionOn
import Polyfold.Chapter18.LinearizationSetLocal

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part IV, §18.4:
**Proposition 18.4.3 (2021 p. 855) for the functor `Λ` of the construction of p. 854**, built in
one strong bundle uniformizer `Ψ̄ ∈ F̄(α)`.

## The text, paraphrased

Let the strong polyfold bundle admit sc-smooth bump functions, `α` be a smooth object and `(α, e)`
a smooth vector, and `Ψ̄ : G ⋉ K → E` a strong bundle uniformizer in `F̄(α)` over
`Ψ : G ⋉ O → C`, `Ψ̄(h̄) = (α, e)`, `p(h̄) = q̄`.  For a small invariant neighbourhood `V` of `q̄`
and an sc⁺-section `s₁` of `p` vanishing off `V` with `s₁(q̄) = h̄`, the translates
`s_g(g ∗ q) = g ∗ s₁(q)` define `Λ(Ψ̄(h)) = |G|⁻¹·#{g ∈ G | s_g(p(h)) = h}`, extended along the
morphisms into `Ψ(O)` and by `1_{e = 0}` elsewhere (p. 854).  Proposition 18.4.3: `Λ` is an
sc⁺-multisection functor with `Λ(α, e) > 0`, atomic in a suitable model, hence structurable.

## Main statements (namespace `Polyfold.GCT.VectorBundle.StrongPolyfoldBundleConstruction`)

* `textLam` (`MultisectionConstructionTextLam.lean`): the functor `Λ` of p. 854.
* **`textLam_indep`**: for every `(q, φ)` with `φ : P(e) → Ψ(q)`, `Λ(e)` is the value attached to
  `(q, φ)`; two choices give the same value.
* **`proposition_18_4_3_text`**: there is an open `W ∋ q̄`, invariant under the stabilizer
  `G_{q̄}`, such that for every `G_{q̄}`-invariant `V ⊆ W` and every sc⁺-section `s₁` vanishing
  off `V`, `Λ` is an sc⁺-multisection functor (Definition 18.3.1), `Λ(Ψ̄(s₁(q̄))) > 0`, `Γ̄^*Λ` is
  atomic (Definition 13.5.1) in the model of `c ⊔ {Ψ̄}` for every covering family `c`, and `Λ` is
  structurable (Definition 18.3.3).
* **`TextData.textLam_eq`**: `Λ` is the push-forward of the multisection `mult` of atomic data in
  the model of `c ⊔ {Ψ̄}`, i.e. the functor of `proposition_18_4_3` for that atomic data.
* **`exists_textSection`**, **`proposition_18_4_3_text_exists`**: with sc-smooth bump functions,
  for a smooth `q̄` and a smooth `h̄` over `q̄` such an `s₁` with `s₁(q̄) = h̄` exists, so the
  hypotheses are satisfiable, and `Λ(e) > 0` for every `e ≅ Ψ̄(h̄)`.
* **`proposition_18_4_3_cutoff`**: the same statement with `s₁ = β·s` for a local sc⁺-section `s`
  on an open `V_s ∋ q̄` and an sc-smooth `β : O → [0, 1]`, `β(q̄) = 1`, supported in a small
  neighbourhood of `q̄`, with `Λ` written through the morphisms `φ : Ψ(q) → P(e)`
  (`cutoffValue`, `cutoffLam`; `cutoffLam_eq` identifies it with `textLam`).

## Readings

* "Pick `V`" is read as "for `V` small enough": the statement is for every `G_{q̄}`-invariant
  `V ⊆ W`, `W` chosen first.  The text's `V` is `G`-invariant for a uniformizer centred at `q̄`
  (`G = G_{q̄}`); for a general `Ψ̄` the stabilizer `G_{q̄}` takes its place, `W` is also chosen
  disjoint from its translates `g ∗ W`, `g ∉ G_{q̄}`, and the formula of p. 854 is used unchanged
  (the translates `s_g`, `g ∉ G_{q̄}`, then vanish near `q̄`).
* Smoothness of `s₁` is read in `p : K → O` (an sc⁺-section, Definition 2.6.6); the vector
  `(α, e)` enters only through `h̄ = s₁(q̄)`.
* "Atomic in a suitable model" is read as atomic in the model of every covering family containing
  `Ψ̄` (`BundleCoveringFamily.withUnif`).
* The standing hypothesis `F̄(α) ≠ ∅` for every `α` (`HasStrongBundleUniformizers`) supplies a
  covering family.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology

noncomputable section

namespace Polyfold

universe u

namespace GCT.VectorBundle.StrongPolyfoldBundleConstruction

open GroupoidalCategory GroupoidalCategory.BanachFunctor SBLocalization StrongBundle
  StrongBundleUniformizerConstruction StrongBundleUniformizerData PolyfoldConstruction

variable {C : GCT.{u}} {V : C.VectorBundle}

/-! ### Independence of the choice -/

/-- **The value of `Λ` does not depend on the choice of `(q, φ)`** (the construction of p. 854):
`Λ(e)` is the value attached to any `(q, φ)` with `φ : P(e) → Ψ(q)`. -/
theorem textLam_indep (Ψb : V.StrongBundleUniformizer) (s₁ : Ψb.base.O → Ψb.K) (e : V.EObj)
    (r r' : Ψb.base.O × C.Mor) (hr : TextReach Ψb e r) (hr' : TextReach Ψb e r') :
    textLam Ψb s₁ e = textValue Ψb s₁ e r hr ∧
      textValue Ψb s₁ e r hr = textValue Ψb s₁ e r' hr' :=
  ⟨textLam_eq_textValue e r hr, textValue_indep e r r' hr hr'⟩

/-! ### Neighbourhoods of `q̄` in `O` -/

section Nhds

variable (Ψb : V.StrongBundleUniformizer)

theorem continuous_smul_base (g : Ψb.base.G) : Continuous fun q : Ψb.base.O => g • q :=
  continuousOn_univ.1 (Ψb.base.smooth_smul g).continuousOn

/-- An open `N ∋ q₀` disjoint from `g ∗ N` for every `g ∉ G_{q₀}`. -/
theorem exists_nhds_smul_disjoint (q₀ : Ψb.base.O) :
    ∃ N : Set Ψb.base.O, IsOpen N ∧ q₀ ∈ N ∧
      ∀ g : Ψb.base.G, g • q₀ ≠ q₀ → ∀ q ∈ N, g • q ∉ N := by
  have key : ∀ g : Ψb.base.G, ∃ N : Set Ψb.base.O, IsOpen N ∧ q₀ ∈ N ∧
      (g • q₀ ≠ q₀ → ∀ q ∈ N, g • q ∉ N) := by
    intro g
    by_cases hg : g • q₀ = q₀
    · exact ⟨univ, isOpen_univ, mem_univ _, fun h => absurd hg h⟩
    · obtain ⟨A, B, hA, hB, hqA, hgB, hAB⟩ := t2_separation (Ne.symm hg)
      refine ⟨A ∩ (fun q => g • q) ⁻¹' B, hA.inter (hB.preimage (continuous_smul_base Ψb g)),
        ⟨hqA, hgB⟩, fun _ q hq hgq => ?_⟩
      exact hAB.ne_of_mem hgq.1 hq.2 rfl
  choose N hN hqN hNs using key
  refine ⟨⋂ g, N g, isOpen_iInter_of_finite hN, mem_iInter.2 hqN, fun g hg q hq hgq => ?_⟩
  exact hNs g hg q (mem_iInter.1 hq g) (mem_iInter.1 hgq g)

/-- A `G_{q₀}`-invariant open neighbourhood of `q₀` inside a given one. -/
theorem exists_stab_invariant (q₀ : Ψb.base.O) {W : Set Ψb.base.O} (hW : IsOpen W)
    (hq : q₀ ∈ W) :
    ∃ W' ⊆ W, IsOpen W' ∧ q₀ ∈ W' ∧
      ∀ g : Ψb.base.G, g • q₀ = q₀ → MapsTo (g • ·) W' W' := by
  refine ⟨⋂ h : {h : Ψb.base.G // h • q₀ = q₀}, (fun q => h.1 • q) ⁻¹' W, fun q hq' => ?_,
    isOpen_iInter_of_finite fun h => hW.preimage (continuous_smul_base Ψb h.1),
    mem_iInter.2 fun h => ?_, fun g hg q hq' => mem_iInter.2 fun h => ?_⟩
  · have := mem_iInter.1 hq' ⟨1, one_smul _ _⟩
    simpa only [mem_preimage, one_smul] using this
  · change h.1 • q₀ ∈ W
    rw [h.2]; exact hq
  · change h.1 • g • q ∈ W
    rw [← mul_smul]
    exact mem_iInter.1 hq' ⟨h.1 * g, by rw [mul_smul, hg, h.2]⟩

end Nhds

/-! ### The data of the construction, chosen in `Ψ̄` -/

section Main

variable {S : C.PolyfoldConstruction} {Q : V.StrongPolyfoldBundleConstruction S}

/-- **The neighbourhood `W` of the construction of p. 854**: for every `G_{q₀}`-invariant
`V ⊆ W` and every sc⁺-section `s₁` vanishing off `V`, the data `TextData` exist (a natural
representation with the properness property in every model `c ⊔ {Ψ̄}`, `V(x)`, ...). -/
theorem exists_textData (Ψ : Q.Unif) (q₀ : Ψ.1.base.O) :
    ∃ W : Set Ψ.1.base.O, IsOpen W ∧ q₀ ∈ W ∧ ∀ Vt : Set Ψ.1.base.O,
      (∀ g : Ψ.1.base.G, g • q₀ = q₀ → MapsTo (g • ·) Vt Vt) → Vt ⊆ W →
      ∀ s₁ : Ψ.1.base.O → Ψ.1.K, Ψ.1.B.IsScPlusSection s₁ →
        (∀ q ∉ Vt, s₁ q = fiberZero Ψ.1.p q) →
        ∃ T : TextData Ψ q₀, T.Vt = Vt ∧ T.s₁ = s₁ := by
  obtain ⟨U, hU, hqU, hprop⟩ := S.proposition_17_1_11 (Q.baseUnif Ψ) q₀
  obtain ⟨N, hN, hqN, hNs⟩ := exists_nhds_smul_disjoint Ψ.1 q₀
  have hW0 : IsOpen (Sigma.mk (β := fun _ : PUnit.{u + 1} => Ψ.1.base.O) PUnit.unit '' (U ∩ N)) :=
    isOpenMap_sigmaMk _ (hU.inter hN)
  obtain ⟨R₀, V₀, hV₀o, hqV₀, hV₀inv, hV₀cl, hRU, -⟩ :=
    EpGroupoid.exists_invariant_nhds_of_isOpen (Q.unifEp Ψ) ⟨PUnit.unit, q₀⟩ hW0
      ⟨q₀, ⟨hqU, hqN⟩, rfl⟩
  have hpre : IsOpen (Sigma.mk (β := fun _ : PUnit.{u + 1} => Ψ.1.base.O) PUnit.unit ⁻¹' V₀) :=
    hV₀o.preimage continuous_sigmaMk
  obtain ⟨t, ht, htc, htV⟩ := exists_mem_nhds_isClosed_subset (hpre.mem_nhds hqV₀)
  refine ⟨interior t, isOpen_interior, mem_interior_iff_mem_nhds.2 ht,
    fun Vt hVt hVtW s₁ hs₁ hvan => ?_⟩
  refine ⟨TextData.mk R₀ V₀ hV₀o hqV₀ hV₀inv hV₀cl (fun c => ?_) Vt hVt ?_ ?_ s₁ hs₁ hvan,
    rfl, rfl⟩
  · have h1 := hasPropernessProperty_objMk_image (Q.modelBase (c.withUnif Ψ).Ψ) none (U := U) hU
      hprop
    refine h1.mono ((pieceEmbedding c Ψ q₀).isOpenMap_fo _ R₀.isOpen_U) ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨q, hq, rfl⟩ := hRU hy
    exact ⟨q, hq.1, rfl⟩
  · intro g hg q hq hgq
    obtain ⟨q', hq', e⟩ := hRU hq
    obtain ⟨q'', hq'', e'⟩ := hRU hgq
    have e1 : q' = q := eq_of_heq (Sigma.mk.inj_iff.1 e).2
    have e2 : q'' = g • q := eq_of_heq (Sigma.mk.inj_iff.1 e').2
    exact hNs g hg q (e1 ▸ hq'.2) (e2 ▸ hq''.2)
  · exact (closure_minimal (hVtW.trans interior_subset) htc).trans htV

/-- `bundlePush` depends only on the function pushed. -/
theorem bundlePush_congr {ι : Type u} {Ψb : ι → Q.Unif} (h : S.IsCoveringFamily (Q.modelBase Ψb))
    {β : Type*} {N₁ N₂ : Q.ModelW Ψb → β} (e : N₁ = N₂) (h₁ h₂) :
    Q.bundlePush h N₁ h₁ = Q.bundlePush h N₂ h₂ := by
  subst e; rfl

/-- **`Λ` is the functor of `proposition_18_4_3` for atomic data in the model of `c ⊔ {Ψ̄}`**:
the push-forward of the multisection `mult` of `TextData.atomicData`. -/
theorem TextData.textLam_eq {Ψ : Q.Unif} {q₀ : Ψ.1.base.O} (T : TextData Ψ q₀)
    (c : Q.BundleCoveringFamily) :
    textLam Ψ.1 T.s₁ = Q.bundlePush (c.withUnif Ψ).cover (T.atomicData c).mult
      (Q.eq_of_isomorphic_of_isWFunctor (T.atomicData c).isWFunctor_mult) :=
  (Q.bundlePush_bundlePull (c.withUnif Ψ).cover isMorInvariant_textLam).symm.trans
    (bundlePush_congr _ (T.bundlePull_textLam c) _ _)

/-- **2021 Proposition 18.4.3, p. 855, for the functor `Λ` of the construction of p. 854**, built
in one strong bundle uniformizer `Ψ̄ ∈ F̄(α)` over `Ψ : G ⋉ O → C`: there is an open `W ∋ q̄`,
invariant under `G_{q̄}`, such that for every `G_{q̄}`-invariant `V ⊆ W` and every sc⁺-section
`s₁` of `K → O` vanishing off `V`, `Λ` is an sc⁺-multisection functor, `Λ(Ψ̄(s₁(q̄))) > 0`, the
pull-back `Γ̄^*Λ` to the model of `c ⊔ {Ψ̄}` is atomic for every covering family `c`, and `Λ` is
structurable. -/
theorem proposition_18_4_3_text (hF : Q.HasStrongBundleUniformizers) {α : C.Obj}
    {Ψb : V.StrongBundleUniformizer} (hΨb : Ψb ∈ Q.F α) (q₀ : Ψb.base.O) :
    ∃ W : Set Ψb.base.O, IsOpen W ∧ q₀ ∈ W ∧
      (∀ g : Ψb.base.G, g • q₀ = q₀ → MapsTo (g • ·) W W) ∧
      ∀ Vt ⊆ W, (∀ g : Ψb.base.G, g • q₀ = q₀ → MapsTo (g • ·) Vt Vt) →
      ∀ s₁ : Ψb.base.O → Ψb.K, Ψb.B.IsScPlusSection s₁ →
        (∀ q ∉ Vt, s₁ q = fiberZero Ψb.p q) →
        Q.IsScPlusMultisectionFunctor (textLam Ψb s₁) ∧
        0 < textLam Ψb s₁ (Ψb.obj (s₁ q₀)) ∧
        (∀ c : Q.BundleCoveringFamily,
          IsAtomic (Q.modelSEP (c.withUnif ⟨Ψb, α, hΨb⟩).Ψ)
            (Q.bundlePull (c.withUnif ⟨Ψb, α, hΨb⟩).Ψ (textLam Ψb s₁))) ∧
        Q.IsStructurableFunctor (textLam Ψb s₁) := by
  obtain ⟨W, hW, hqW, hT⟩ := exists_textData (Q := Q) ⟨Ψb, α, hΨb⟩ q₀
  obtain ⟨W', hW'W, hW', hqW', hinv⟩ := exists_stab_invariant Ψb q₀ hW hqW
  refine ⟨W', hW', hqW', hinv, fun Vt hVt hVinv s₁ hs₁ hvan => ?_⟩
  obtain ⟨T, -, rfl⟩ := hT Vt hVinv (hVt.trans hW'W) s₁ hs₁ hvan
  have hinvΛ : IsMorInvariant (textLam Ψb T.s₁) := isMorInvariant_textLam
  have hA : ∀ c : Q.BundleCoveringFamily, IsAtomic (Q.modelSEP (c.withUnif ⟨Ψb, α, hΨb⟩).Ψ)
      (Q.bundlePull (c.withUnif ⟨Ψb, α, hΨb⟩).Ψ (textLam Ψb T.s₁)) := fun c => by
    have := (T.atomicData c).isAtomic_mult
    rw [← T.bundlePull_textLam c] at this
    exact this
  refine ⟨⟨hinvΛ, (Q.refCoveringFamily hF).withUnif ⟨Ψb, α, hΨb⟩, (hA _).1⟩,
    textLam_pos T.isScPlusSection_s₁.1 q₀, hA,
    ⟨hinvΛ, (Q.refCoveringFamily hF).withUnif ⟨Ψb, α, hΨb⟩, ?_⟩⟩
  exact theorem_13_5_3_of_paracompact (Q.hasParacompactOrbitSpace_model _) (hA _)

/-! ### Existence of `s₁` -/

/-- With sc-smooth bump functions (Definition 18.4.1), the M-polyfold `O` of a strong bundle
uniformizer admits sc-smooth bump functions (Definition 5.3.1): `O` is an open piece of a model. -/
theorem admitsBumpFunctions_unif (hbump : S.AdmitsModelBumpFunctions)
    (hF : Q.HasStrongBundleUniformizers) (Ψ : Q.Unif) : Ψ.1.base.P.AdmitsBumpFunctions := by
  have h1 := ((S.remark_18_4_2 (Q.baseCoveringFamily ((Q.refCoveringFamily hF).withUnif Ψ))).2.1).1
    hbump
  have h2 := EpGroupoid.theorem_12_3_2_1.1 h1
  exact (MPolyfold.isLocalScDiffeo_sigmaMk
    (fun o => (Q.modelBase ((Q.refCoveringFamily hF).withUnif Ψ).Ψ o).1.P) none).admitsBumpFunctions
    h2

/-- **An `s₁` as in the construction of p. 854 exists** (Lemma 5.3.3): for a smooth `q̄`, a smooth
`h̄` over `q̄` and an open `W ∋ q̄`, an sc⁺-section `s₁` with `s₁(q̄) = h̄` vanishing off `W`. -/
theorem exists_textSection (hbump : S.AdmitsModelBumpFunctions)
    (hF : Q.HasStrongBundleUniformizers) (Ψ : Q.Unif) {q₀ : Ψ.1.base.O}
    (hq₀ : q₀ ∈ Ψ.1.base.P.smoothSet) {h₀ : Ψ.1.K} (hh₀ : h₀ ∈ Ψ.1.B.toMPolyfold0.smoothSet)
    (hp : Ψ.1.p h₀ = q₀) {W : Set Ψ.1.base.O} (hW : IsOpen W) (hqW : q₀ ∈ W) :
    ∃ s₁ : Ψ.1.base.O → Ψ.1.K, Ψ.1.B.IsScPlusSection s₁ ∧ s₁ q₀ = h₀ ∧
      ∀ q ∉ W, s₁ q = fiberZero Ψ.1.p q := by
  obtain ⟨N, hN⟩ := proposition_5_1_3_exists (B := Ψ.1.B)
  obtain ⟨-, s, hs, hsx, hsupp, -⟩ :=
    lemma_5_3_3 (admitsBumpFunctions_unif hbump hF Ψ) hN hq₀ hh₀ hp one_pos hW hqW
  exact ⟨s, hs, hsx, fun q hq =>
    StrongBundle.eq_fiberZero_of_notMem_sectionSupport fun h => hq (hsupp h)⟩

/-- **2021 Proposition 18.4.3, p. 855, with the choices of p. 854 made**: with sc-smooth bump
functions, for `Ψ̄ ∈ F̄(α)`, a smooth `q̄ ∈ O` and a smooth `h̄ ∈ K` over `q̄`, there is an
sc⁺-section `s₁` with `s₁(q̄) = h̄` for which `Λ` is an sc⁺-multisection functor, `Λ(e) > 0` for
every `e ≅ Ψ̄(h̄)`, `Γ̄^*Λ` is atomic in the model of `c ⊔ {Ψ̄}` for every covering family `c`, and
`Λ` is structurable. -/
theorem proposition_18_4_3_text_exists (hbump : S.AdmitsModelBumpFunctions)
    (hF : Q.HasStrongBundleUniformizers) {α : C.Obj} {Ψb : V.StrongBundleUniformizer}
    (hΨb : Ψb ∈ Q.F α) {q₀ : Ψb.base.O} (hq₀ : q₀ ∈ Ψb.base.P.smoothSet) {h₀ : Ψb.K}
    (hh₀ : h₀ ∈ Ψb.B.toMPolyfold0.smoothSet) (hp : Ψb.p h₀ = q₀) :
    ∃ s₁ : Ψb.base.O → Ψb.K, Ψb.B.IsScPlusSection s₁ ∧ s₁ q₀ = h₀ ∧
      Q.IsScPlusMultisectionFunctor (textLam Ψb s₁) ∧
      (∀ e : V.EObj, V.groupoid.Isomorphic (Ψb.obj h₀) e → 0 < textLam Ψb s₁ e) ∧
      (∀ c : Q.BundleCoveringFamily,
        IsAtomic (Q.modelSEP (c.withUnif ⟨Ψb, α, hΨb⟩).Ψ)
          (Q.bundlePull (c.withUnif ⟨Ψb, α, hΨb⟩).Ψ (textLam Ψb s₁))) ∧
      Q.IsStructurableFunctor (textLam Ψb s₁) := by
  obtain ⟨W, hW, hqW, hinv, hmain⟩ := proposition_18_4_3_text hF hΨb q₀
  obtain ⟨s₁, hs₁, hsx, hvan⟩ :=
    exists_textSection hbump hF (Q := Q) ⟨Ψb, α, hΨb⟩ hq₀ hh₀ hp hW hqW
  obtain ⟨h1, h2, h3, h4⟩ := hmain W subset_rfl hinv s₁ hs₁ hvan
  refine ⟨s₁, hs₁, hsx, h1, fun e he => ?_, h3, h4⟩
  rw [← h1.1.eq_of_isomorphic he, ← hsx]
  exact h2

end Main

/-! ### The construction with a local section and a cut-off -/

section Cutoff

variable (Ψb : V.StrongBundleUniformizer) (s : Ψb.base.O → Ψb.K) (hs : ∀ q, Ψb.p (s q) = q)
  (β : Ψb.base.O → ℝ)

/-- `Ψ̄(β(r)·s(r)) ∈ E` over `Ψ(r)`. -/
def cutoffObj (r : Ψb.base.O) : V.EObj :=
  V.objMk (Ψb.base.obj r) (β r • Ψb.fiber r ⟨s r, hs r⟩)

/-- The value attached to `φ : Ψ(q) → P(e')`:
`|G|⁻¹·#{g | μ(φ ∘ Ψ(g, g⁻¹ q))(Ψ̄((β·s)(g⁻¹ q))) = e'}`. -/
def cutoffValue (q : Ψb.base.O) (φ : C.Mor) (e' : V.EObj) : ℚ≥0 :=
  (Nat.card {g : Ψb.base.G //
      ∃ hh, V.act (C.toGroupoidStr.comp φ (Ψb.base.mor (g, g⁻¹ • q)))
        (cutoffObj Ψb s hs β (g⁻¹ • q)) hh = e'} : ℚ≥0) / (Nat.card Ψb.base.G : ℚ≥0)

/-- `φ : Ψ(q) → P(e')`. -/
def CutoffLift (e' : V.EObj) (p : Ψb.base.O × C.Mor) : Prop :=
  C.toGroupoidStr.src p.2 = Ψb.base.obj p.1 ∧ C.toGroupoidStr.tgt p.2 = e'.1

open Classical in
/-- The functor `Λ` of p. 854 for `s₁ = β·s`, written through the morphisms `φ : Ψ(q) → P(e')`. -/
def cutoffLam (e' : V.EObj) : ℚ≥0 :=
  if h : ∃ p, CutoffLift Ψb e' p then cutoffValue Ψb s hs β h.choose.1 h.choose.2 e'
  else if e'.2 = 0 then 1 else 0

theorem cutoffObj_eq (r : Ψb.base.O) :
    cutoffObj Ψb s hs β r = Ψb.obj (Polyfold.sectionSmul Ψb.p β s r) := by
  have hk : Ψb.p (Polyfold.sectionSmul Ψb.p β s r) = r := IsSection.sectionSmul hs r
  rw [Ψb.obj_of_eq hk]
  refine objMk_eq_iff.2 ?_
  rw [← map_smul]
  congr 1
  exact Subtype.ext (sectionSmul_apply hs r).symm

variable {Ψb}

theorem act_eq_iff_eq_act_inv {φ : C.Mor} {x e' : V.EObj}
    (hx : V.base x = C.toGroupoidStr.src φ)
    (he : V.base e' = C.toGroupoidStr.src (C.toGroupoidStr.inv φ)) :
    V.act φ x hx = e' ↔ x = V.act (C.toGroupoidStr.inv φ) e' he := by
  constructor
  · rintro rfl; exact (act_inv_act φ x hx).symm
  · rintro rfl; exact act_act_inv φ e' he

variable {s β}

/-- The counted condition of `cutoffValue` is that of `textLamK` for `s₁ = β·s`. -/
theorem cutoff_count_iff {q : Ψb.base.O} {φ : C.Mor} {e' : V.EObj}
    (hsrc : C.toGroupoidStr.src φ = Ψb.base.obj q)
    (hr : TextReach Ψb e' (q, C.toGroupoidStr.inv φ)) (g : Ψb.base.G) :
    (∃ hh, V.act (C.toGroupoidStr.comp φ (Ψb.base.mor (g, g⁻¹ • q)))
        (cutoffObj Ψb s hs β (g⁻¹ • q)) hh = e') ↔
      textTranslate Ψb (Polyfold.sectionSmul Ψb.p β s) g q =
        textLift Ψb e' (q, C.toGroupoidStr.inv φ) hr := by
  have hk : Ψb.p (Polyfold.sectionSmul Ψb.p β s (g⁻¹ • q)) = g⁻¹ • q :=
    IsSection.sectionSmul hs _
  have htm : C.toGroupoidStr.tgt (Ψb.base.mor (g, g⁻¹ • q)) = Ψb.base.obj q :=
    (Ψb.base.functor.tgt_mor (g, g⁻¹ • q)).trans (congrArg Ψb.base.obj (smul_inv_smul g q))
  have hc : C.toGroupoidStr.src φ = C.toGroupoidStr.tgt (Ψb.base.mor (g, g⁻¹ • q)) :=
    hsrc.trans htm.symm
  have hh0 : V.base (cutoffObj Ψb s hs β (g⁻¹ • q)) =
      C.toGroupoidStr.src (C.toGroupoidStr.comp φ (Ψb.base.mor (g, g⁻¹ • q))) := by
    rw [C.toGroupoidStr.src_comp _ _ hc]
    exact (Ψb.base.functor.src_mor (g, g⁻¹ • q)).symm
  set k := Polyfold.sectionSmul Ψb.p β s (g⁻¹ • q) with hkdef
  have hx : V.base (Ψb.obj (g • k)) = C.toGroupoidStr.src φ := by
    change Ψb.base.obj (Ψb.p (g • k)) = _
    rw [Ψb.p_smul, hk, smul_inv_smul]; exact hsrc.symm
  have hA : ∀ hh, V.act (C.toGroupoidStr.comp φ (Ψb.base.mor (g, g⁻¹ • q)))
      (cutoffObj Ψb s hs β (g⁻¹ • q)) hh = V.act φ (Ψb.obj (g • k)) hx := fun hh => by
    rw [act_comp' _ _ hc]
    exact act_congr rfl ((act_congr (congrArg (fun y => Ψb.base.mor (g, y)) hk.symm)
      (cutoffObj_eq Ψb s hs β _) _ _).trans (Ψb.obj_smul' g k)) _ _
  have hB : V.act φ (Ψb.obj (g • k)) hx = e' ↔
      g • k = textLift Ψb e' (q, C.toGroupoidStr.inv φ) hr := by
    rw [act_eq_iff_eq_act_inv hx hr.1.symm, ← obj_textLift e' _ hr]
    exact Ψb.obj_injective.eq_iff
  constructor
  · rintro ⟨hh, h⟩
    exact hB.1 ((hA hh).symm.trans h)
  · intro h
    exact ⟨hh0, (hA hh0).trans (hB.2 h)⟩

variable (s β) in
theorem cutoffValue_eq {q : Ψb.base.O} {φ : C.Mor} {e' : V.EObj}
    (hsrc : C.toGroupoidStr.src φ = Ψb.base.obj q)
    (hr : TextReach Ψb e' (q, C.toGroupoidStr.inv φ)) :
    cutoffValue Ψb s hs β q φ e' =
      textValue Ψb (Polyfold.sectionSmul Ψb.p β s) e' (q, C.toGroupoidStr.inv φ) hr := by
  unfold cutoffValue textValue textLamK
  rw [div_eq_inv_mul]
  congr 2
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [p_textLift]
  exact cutoff_count_iff hs hsrc hr g

theorem textReach_of_cutoffLift {e' : V.EObj} {p : Ψb.base.O × C.Mor}
    (h : CutoffLift Ψb e' p) : TextReach Ψb e' (p.1, C.toGroupoidStr.inv p.2) :=
  ⟨(C.toGroupoidStr.src_inv _).trans h.2, (C.toGroupoidStr.tgt_inv _).trans h.1⟩

variable (s β) in
/-- **`cutoffLam` is `textLam` for `s₁ = β·s`.** -/
theorem cutoffLam_eq : cutoffLam Ψb s hs β = textLam Ψb (Polyfold.sectionSmul Ψb.p β s) := by
  funext e'
  unfold cutoffLam
  by_cases h : ∃ p, CutoffLift Ψb e' p
  · rw [dif_pos h, cutoffValue_eq s hs β h.choose_spec.1 (textReach_of_cutoffLift h.choose_spec),
      textLam_eq_textValue _ _ (textReach_of_cutoffLift h.choose_spec)]
  · rw [dif_neg h]
    have h' : ¬ ∃ r, TextReach Ψb e' r := fun ⟨r, hr⟩ =>
      h ⟨(r.1, C.toGroupoidStr.inv r.2), (C.toGroupoidStr.src_inv _).trans hr.2,
        (C.toGroupoidStr.tgt_inv _).trans hr.1⟩
    rw [textLam_of_not_reach _ h']

variable (Ψb)

/-- `Ψ̄` as a strong bundle over the trivial ep-groupoid `O`. -/
def unifSEP : SEP.{u} where
  Obj := Ψb.base.O
  Mor := Ψb.base.O
  X := EpGroupoid.trivial Ψb.base.P
  W := Ψb.K
  P := Ψb.p
  B := Ψb.B
  E := EpStrongBundle.trivial Ψb.B

variable {Ψb}

include hs in
/-- **`β·s` is an sc⁺-section** for a local sc⁺-section `s` on `V_s` and an sc-smooth `β` with
`tsupport β ⊆ V_s`. -/
theorem isScPlusSection_cutoff {Vs : Set Ψb.base.O} (hVs : IsOpen Vs)
    (hsV : Ψb.B.IsScPlusSectionOn s Vs) (hβ : Ψb.base.P.IsScSmoothMap realPolyfold β)
    (hβV : tsupport β ⊆ Vs) : Ψb.B.IsScPlusSection (Polyfold.sectionSmul Ψb.p β s) := by
  have hzero : ∀ y, y ∉ tsupport β → Polyfold.sectionSmul Ψb.p β s y = fiberZero Ψb.p y :=
    fun y hy => by
      rw [sectionSmul_apply hs, image_eq_zero_of_notMem_tsupport hy, zero_smul]; rfl
  obtain ⟨G₀, hG₀, hG₀f⟩ := (StrongBundle.isScPlusSection_fiberZero (B := Ψb.B)).exists_one
  refine StrongBundle.isScPlusSection_of_locally (IsSection.sectionSmul hs) fun y₀ => ?_
  by_cases hy₀ : y₀ ∈ Vs
  · obtain ⟨-, G, hG, hGs⟩ :=
      SBLocalization.IsScPlusSectionOn.sectionSmul (A := unifSEP Ψb) hVs hsV hs hβ
    exact ⟨Vs, hVs, hy₀, G, hGs, hG⟩
  · have hy₀' : y₀ ∉ tsupport β := fun h => hy₀ (hβV h)
    exact ⟨(tsupport β)ᶜ, (isClosed_tsupport β).isOpen_compl, hy₀', G₀,
      hG₀.mono (isClosed_tsupport β).isOpen_compl (subset_univ _), fun y hy => by
        rw [hG₀f, hzero y hy]⟩

variable {S : C.PolyfoldConstruction} {Q : V.StrongPolyfoldBundleConstruction S}

/-- **2021 Proposition 18.4.3, p. 855, with a local section and a cut-off**: for `Ψ̄ ∈ F̄(α)`,
`q̄ ∈ O` and a local sc⁺-section `s` of `K → O` on an open `V_s ∋ q̄`, there is an open `W ∋ q̄`
such that for every sc-smooth `β : O → [0, 1]` with `β(q̄) = 1` and `tsupport β ⊆ W`, the
functor `Λ` of the construction of p. 854 for `s₁ = β·s` has values independent of the choice of
`φ`, is an sc⁺-multisection functor with `Λ(Ψ̄(s(q̄))) > 0`, is atomic in the model of
`c ⊔ {Ψ̄}` for every covering family `c`, and is structurable. -/
theorem proposition_18_4_3_cutoff (hF : Q.HasStrongBundleUniformizers)
    (_hbump : S.AdmitsModelBumpFunctions) (α : C.Obj) (Ψb : V.StrongBundleUniformizer)
    (hΨb : Ψb ∈ Q.F α) (q₀ : Ψb.base.O) (_hq₀ : Ψb.base.obj q₀ = α)
    (s : Ψb.base.O → Ψb.K) (hs : ∀ q, Ψb.p (s q) = q) (Vs : Set Ψb.base.O) (hVs : IsOpen Vs)
    (hq₀Vs : q₀ ∈ Vs) (hsV : Ψb.B.IsScPlusSectionOn s Vs) :
    ∃ W : Set Ψb.base.O, IsOpen W ∧ q₀ ∈ W ∧
      ∀ β : Ψb.base.O → ℝ, Ψb.base.P.IsScSmoothMap realPolyfold β →
        (∀ r, 0 ≤ β r ∧ β r ≤ 1) → tsupport β ⊆ W → β q₀ = 1 →
        (∀ (e' : V.EObj) (p p' : Ψb.base.O × C.Mor), CutoffLift Ψb e' p →
          CutoffLift Ψb e' p' →
          cutoffValue Ψb s hs β p.1 p.2 e' = cutoffValue Ψb s hs β p'.1 p'.2 e') ∧
        Q.IsScPlusMultisectionFunctor (cutoffLam Ψb s hs β) ∧
        0 < cutoffLam Ψb s hs β (V.objMk (Ψb.base.obj q₀) (Ψb.fiber q₀ ⟨s q₀, hs q₀⟩)) ∧
        (∀ c : Q.BundleCoveringFamily,
          SBLocalization.IsAtomic (Q.modelSEP (c.withUnif ⟨Ψb, α, hΨb⟩).Ψ)
            (Q.bundlePull (c.withUnif ⟨Ψb, α, hΨb⟩).Ψ (cutoffLam Ψb s hs β))) ∧
        Q.IsStructurableFunctor (cutoffLam Ψb s hs β) := by
  obtain ⟨W, hW, hqW, hinv, hmain⟩ := proposition_18_4_3_text hF hΨb q₀
  refine ⟨W ∩ Vs, hW.inter hVs, ⟨hqW, hq₀Vs⟩, fun β hβ _ hβW hβ1 => ?_⟩
  have hzero : ∀ y, y ∉ W → Polyfold.sectionSmul Ψb.p β s y = fiberZero Ψb.p y :=
    fun y hy => by
      have hy' : y ∉ tsupport β := fun h => hy (hβW h).1
      rw [sectionSmul_apply hs, image_eq_zero_of_notMem_tsupport hy', zero_smul]; rfl
  have htplus := isScPlusSection_cutoff hs hVs hsV hβ (hβW.trans inter_subset_right)
  obtain ⟨h1, h2, h3, h4⟩ := hmain W subset_rfl hinv _ htplus hzero
  have hobj : V.objMk (Ψb.base.obj q₀) (Ψb.fiber q₀ ⟨s q₀, hs q₀⟩) =
      Ψb.obj (Polyfold.sectionSmul Ψb.p β s q₀) := by
    refine Eq.trans ?_ (cutoffObj_eq Ψb s hs β q₀)
    unfold cutoffObj; rw [hβ1, one_smul]
  rw [cutoffLam_eq s hs β, hobj]
  refine ⟨fun e' p p' hp hp' => ?_, h1, h2, h3, h4⟩
  rw [cutoffValue_eq s hs β hp.1 (textReach_of_cutoffLift hp),
    cutoffValue_eq s hs β hp'.1 (textReach_of_cutoffLift hp')]
  exact textValue_indep _ _ _ _ _

end Cutoff

end GCT.VectorBundle.StrongPolyfoldBundleConstruction

end Polyfold
