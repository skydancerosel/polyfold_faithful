import Polyfold.Chapter6.Continuation
import Polyfold.Chapter6.DetBundle

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §6.5,
pp. 223–226: the continuity statements used in the proofs of Lemmas 6.6.5, 6.6.8, 6.6.10 (preprint 6.30, 6.33, 6.34) and
Theorem 6.6.11 (preprint 6.35) ("as `τ` varies, the bundle varies continuously"; "the data in the occurring exact
sequence … vary continuously"; "the operators for `t = 0, 1` in `DET(∗)` change continuously in
`τ`") *(book 2017: §6.5; see `BookConcordance.md`)*.

# Continuous families of kernels and of stabilized orientations

## The text, paraphrased

In the proofs of Lemmas 6.33–6.34 and Theorem 6.6.11 (preprint 6.35) the end-point operators `T_τ` in `DET(f, x)`
and the stabilizing maps vary continuously with a parameter `τ`; then the bundles of kernels vary
continuously, and the orientations they receive from `DET(f, x)` through the isomorphisms
`Φ_{E_τ}` vary continuously, so that a continuation argument applies.

## What is formalized

* `exists_subspaceFamily_ker`: the kernels of a norm-continuous family of surjective Fredholm
  operators over a connected base form a continuous family of subspaces (`SubspaceFamily`).
* `SubspaceFamily.exists_map`: the images of a continuous family of subspaces under a jointly
  continuous family of linear maps, injective on the subspaces, form one; `isLineOrientation_map`:
  orientations are carried along.
* `SubspaceFamily.exists_inf_ker`: cutting a continuous family by the kernel of a fixed
  `ℓ : W → ℝᵐ` onto on every member gives one (the text's `L_t = T S ∩ {dt = 0}`, Lemma 6.6.5 (preprint 6.30)).
* `isLineOrientation_stabRay`: for a continuous orientation `o` of `DET` over a set `C` of Fredholm
  operators, a norm-continuous family `T_q ∈ C` and a continuous stabilization `φ_q` with
  `T_q ⊕ φ_q` onto, the sign-normalized rays `α(T_q) Φ(o(T_q))` of `λ(ker(T_q ⊕ φ_q))`, with
  `α(T) = (−1)^{dim coker T}` (`stabSign`), form an orientation.
* `not_isLineOrientation_stabRay_uncorrected`: without `α` the rays `Φ(o(T_q))` need not form an
  orientation (an instance with `E = F = ℝ`, `k = 1`, `T_q = q / (1 + |q|)`, `φ = pr₀`, in the
  namespace `StabCounterexample`).
* On the way: `coord_stabIota`, the chart coordinate of `ι_ψ(x) ∈ det(S ⊕ ψ)` in a chart with the
  same projection `P` is `(−1)^{k · dim F/R(P) + dim coker S} D(S, ψ)` times that of `x`, with
  `D` continuous and nonvanishing near the centre (`stabD`, `continuousOn_stabD`, `stabD_ne_zero`).

## Reading

"Varies continuously" for a family of operators `T_τ ∈ DET(f, x)` is read in the operator norm
(the metric of p. 219), and for maps into a model space as joint continuity.

The isomorphism `Φ_E` of formula (94) (`stabIota` followed by `λ(ker(T ⊕ φ)) ≅ det(T ⊕ φ)`) is,
as we read it, not continuous in the topology of `DET` across the jumps of `dim coker T`: by
`coord_stabIota` it changes the chart coordinates by `(−1)^{dim coker T}` times a continuous
nonvanishing factor (the exponent `k · dim F/R(P)` is constant on a chart), and
`not_isLineOrientation_stabRay_uncorrected` is an instance where the orientations carried by
`Φ_E` jump.  We use the sign-normalized `α(T) Φ_E`; it differs from `Φ_E` by a sign that depends
only on `T` (not on `k` or on the index), so on each operator it carries the orientation of the
text or its opposite.
-/

open Module TensorProduct Bundle Topology Set

noncomputable section

namespace Polyfold

variable {Q : Type*} [TopologicalSpace Q]

/-! ### Families of kernels -/

section Ker

variable {V F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace V] [CompleteSpace F] in
/-- For a surjective operator `A`, the identity is a good left-projection (`R(1 ∘ A) = F`). -/
theorem isGoodLeftProj_id_of_surjective {A : V →L[ℝ] F} (hs : Function.Surjective A) :
    IsGoodLeftProj A (ContinuousLinearMap.id ℝ F) where
  isProj := ContinuousLinearMap.id_comp _
  finite_coker := by
    have htop : LinearMap.range ((ContinuousLinearMap.id ℝ F : F →L[ℝ] F) : F →ₗ[ℝ] F) = ⊤ :=
      LinearMap.range_eq_top.2 fun y => ⟨y, rfl⟩
    have : Subsingleton (F ⧸ LinearMap.range
        ((ContinuousLinearMap.id ℝ F : F →L[ℝ] F) : F →ₗ[ℝ] F)) :=
      Submodule.Quotient.subsingleton_iff.2 htop
    infer_instance
  range_comp := by
    rw [ContinuousLinearMap.id_comp, LinearMap.range_eq_top.2 hs]
    exact (LinearMap.range_eq_top.2 fun y => ⟨y, rfl⟩).symm

/-- **Local frames of the kernels** of a family of surjective Fredholm operators continuous on an
open set (Lemma 6.5.2 (preprint 6.18) with `P = 1`): near `x₀` the vectors `kᵢ + y(kᵢ, A x)`, for a basis `kᵢ` of
`ker A x₀`, are continuous, lie in `ker A x` and are independent, and
`dim ker A x = dim ker A x₀`. -/
theorem exists_kerFrame {X : Type*} [TopologicalSpace X] {A : X → V →L[ℝ] F} {U : Set X}
    (hU : IsOpen U) (hA : ContinuousOn A U) {x₀ : X} (hx₀ : x₀ ∈ U) (hF : (A x₀).IsFredholm)
    (hs : Function.Surjective (A x₀)) :
    ∃ U' : Set X, IsOpen U' ∧ x₀ ∈ U' ∧ U' ⊆ U ∧
      ∃ e : Fin (finrank ℝ (LinearMap.ker (A x₀ : V →ₗ[ℝ] F))) → X → V,
        (∀ i, ContinuousOn (e i) U') ∧ ∀ x ∈ U', (∀ i, A x (e i x) = 0) ∧
          LinearIndependent ℝ (fun i => e i x) ∧
          finrank ℝ (LinearMap.ker (A x : V →ₗ[ℝ] F)) =
            finrank ℝ (LinearMap.ker (A x₀ : V →ₗ[ℝ] F)) := by
  obtain ⟨c, hcT, hcP⟩ := exists_localDetChart_of_proj hF (isGoodLeftProj_id_of_surjective hs)
  have hker : ∀ S : V →L[ℝ] F, LinearMap.ker ((c.P ∘L S : V →L[ℝ] F) : V →ₗ[ℝ] F) =
      LinearMap.ker (S : V →ₗ[ℝ] F) := fun S => by rw [hcP, ContinuousLinearMap.id_comp]
  have hK : c.K = LinearMap.ker (A x₀ : V →ₗ[ℝ] F) := by
    change LinearMap.ker ((c.P ∘L c.T : V →L[ℝ] F) : V →ₗ[ℝ] F) = _
    rw [hker, hcT]
  have hn : finrank ℝ (LinearMap.ker (A x₀ : V →ₗ[ℝ] F)) = finrank ℝ c.K := by rw [hK]
  let b := Module.finBasis ℝ c.K
  refine ⟨U ∩ A ⁻¹' {S | ‖S - c.T‖ < c.ε}, hA.isOpen_inter_preimage hU
    (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const), ⟨hx₀, ?_⟩,
    inter_subset_left, fun i x => c.kerMap (A x) (b (Fin.cast hn i)), fun i => ?_,
    fun x hx => ?_⟩
  · change ‖A x₀ - c.T‖ < c.ε
    rw [hcT, sub_self, norm_zero]
    exact c.ε_pos
  · exact (c.continuousOn_kerMap_apply _).comp (hA.mono inter_subset_left) fun x hx => hx.2
  · have hS : ‖A x - c.T‖ < c.ε := hx.2
    refine ⟨fun i => ?_, ?_, ?_⟩
    · have h := (c.lemma_6_5_2).2.1 (A x) hS _ (b (Fin.cast hn i)).2
      rw [hker] at h
      exact h
    · have h1 : LinearIndependent ℝ (c.kerEquiv (A x) hS ∘ b) :=
        b.linearIndependent.map' _ (c.kerEquiv (A x) hS).ker
      exact (h1.map' _ (Submodule.ker_subtype _)).comp (Fin.cast hn) (Fin.cast_injective hn)
    · rw [← hker, ← (c.kerEquiv (A x) hS).finrank_eq, hn]

/-- **The kernels of a continuous family of surjective Fredholm operators** over a connected base
form a continuous family of subspaces (near `q₀`, `ker A_q` is the graph over `ker A_{q₀}` of
Lemma 6.5.2 (preprint 6.18) with `P = 1`). -/
theorem exists_subspaceFamily_ker [PreconnectedSpace Q] [Nonempty Q] (A : Q → V →L[ℝ] F)
    (hA : Continuous A) (hF : ∀ q, (A q).IsFredholm) (hs : ∀ q, Function.Surjective (A q)) :
    ∃ Λ : SubspaceFamily Q V, ∀ q, Λ.L q = LinearMap.ker (A q : V →ₗ[ℝ] F) := by
  have hloc : ∀ q₀, ∃ U : Set Q, IsOpen U ∧ q₀ ∈ U ∧
      ∃ e : Fin (finrank ℝ (LinearMap.ker (A q₀ : V →ₗ[ℝ] F))) → Q → V,
        (∀ i, ContinuousOn (e i) U) ∧ ∀ q ∈ U, (∀ i, A q (e i q) = 0) ∧
          LinearIndependent ℝ (fun i => e i q) ∧
          finrank ℝ (LinearMap.ker (A q : V →ₗ[ℝ] F)) =
            finrank ℝ (LinearMap.ker (A q₀ : V →ₗ[ℝ] F)) := fun q₀ => by
    obtain ⟨U, hU, hq₀, -, e, he, h⟩ :=
      exists_kerFrame isOpen_univ hA.continuousOn (mem_univ q₀) (hF q₀) (hs q₀)
    exact ⟨U, hU, hq₀, e, he, h⟩
  have hconst : IsLocallyConstant fun q => finrank ℝ (LinearMap.ker (A q : V →ₗ[ℝ] F)) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro q₀
    obtain ⟨U, hU, hq₀, e, -, h⟩ := hloc q₀
    filter_upwards [hU.mem_nhds hq₀] with q hq using (h q hq).2.2
  obtain ⟨q₁⟩ := ‹Nonempty Q›
  have hn : ∀ q, finrank ℝ (LinearMap.ker (A q : V →ₗ[ℝ] F)) =
      finrank ℝ (LinearMap.ker (A q₁ : V →ₗ[ℝ] F)) := fun q =>
    hconst.apply_eq_of_preconnectedSpace q q₁
  refine ⟨{ L := fun q => LinearMap.ker (A q : V →ₗ[ℝ] F)
            n := finrank ℝ (LinearMap.ker (A q₁ : V →ₗ[ℝ] F))
            finiteDimensional := fun q => (hF q).finite_ker
            finrank_eq := hn
            exists_frame := fun q₀ => ?_ }, fun q => rfl⟩
  obtain ⟨U, hU, hq₀, e, he, h⟩ := hloc q₀
  exact ⟨U, hU, hq₀, fun i => e (Fin.cast (hn q₀).symm i), fun i => he _, fun q hq =>
    ⟨fun i => LinearMap.mem_ker.2 ((h q hq).1 _),
      (h q hq).2.1.comp _ (Fin.cast_injective _)⟩⟩

end Ker

/-! ### Images and sections of families -/

namespace SubspaceFamily

variable {W W' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W']
  [NormedSpace ℝ W'] (Λ : SubspaceFamily Q W)

/-- **The image of a continuous family under a jointly continuous family of linear maps**,
injective on the members, is a continuous family. -/
theorem exists_map (J : Q → W →L[ℝ] W') (hJ : Continuous fun p : Q × W => J p.1 p.2)
    (hinj : ∀ q, Set.InjOn (J q) (Λ.L q)) :
    ∃ Λ' : SubspaceFamily Q W', ∀ q, Λ'.L q = (Λ.L q).map (J q : W →ₗ[ℝ] W') := by
  have hinj' : ∀ q, Function.Injective ((J q : W →ₗ[ℝ] W') ∘ₗ (Λ.L q).subtype) :=
    fun q x y hxy => Subtype.ext (hinj q x.2 y.2 hxy)
  refine ⟨{ L := fun q => (Λ.L q).map (J q : W →ₗ[ℝ] W')
            n := Λ.n
            finiteDimensional := fun q => inferInstance
            finrank_eq := fun q => ?_
            exists_frame := fun q₀ => ?_ }, fun q => rfl⟩
  · rw [← Submodule.range_subtype (Λ.L q), ← LinearMap.range_comp,
      LinearMap.finrank_range_of_inj (hinj' q), Λ.finrank_eq]
  · obtain ⟨U, hU, hq₀, e, he, h⟩ := Λ.exists_frame q₀
    refine ⟨U, hU, hq₀, fun i q => J q (e i q), fun i => ?_, fun q hq =>
      ⟨fun i => Submodule.mem_map_of_mem ((h q hq).1 i), ?_⟩⟩
    · exact hJ.comp_continuousOn (continuousOn_id.prodMk (he i))
    · have hv : LinearIndependent ℝ (fun i => (⟨e i q, (h q hq).1 i⟩ : Λ.L q)) :=
        LinearIndependent.of_comp (Λ.L q).subtype (h q hq).2
      exact hv.map' _ (LinearMap.ker_eq_bot.2 (hinj' q))

/-- **Orientations are carried along such an image**: `λ(J_q)` of a continuous orientation of
`λ(L)` is a continuous orientation of `λ(J L)`. -/
theorem isLineOrientation_map (J : Q → W →L[ℝ] W') (hJ : Continuous fun p : Q × W => J p.1 p.2)
    (Λ' : SubspaceFamily Q W') (e : ∀ q, Λ.L q ≃ₗ[ℝ] Λ'.L q)
    (he : ∀ q (v : Λ.L q), (e q v : W') = J q v) (o : LineOrientation Λ.det) :
    IsLineOrientation Λ'.det fun q => Module.Ray.map (maxPowEquiv (e q)) (o q) := by
  intro q₀
  obtain ⟨U, hU, σ, hσ, hσo⟩ := o.2 q₀
  have hn : Λ'.n = Λ.n := by rw [← Λ'.finrank_eq q₀, ← Λ.finrank_eq q₀, (e q₀).finrank_eq]
  refine ⟨U, hU, fun q => maxPowEquiv (e q) (σ q), fun q hq => ?_, fun q hq => ?_⟩
  · set ε := Λ.frameAt q
    have hqε : q ∈ ε.U := Λ.mem_frameAt q
    let ε' : Λ'.Frame :=
      { U := ε.U
        isOpen := ε.isOpen
        e := fun i b => J b (ε.e (Fin.cast hn i) b)
        continuousOn := fun i => hJ.comp_continuousOn (continuousOn_id.prodMk (ε.continuousOn _))
        mem := fun b hb i => by
          rw [← he b ⟨_, ε.mem b hb _⟩]
          exact (e b _).2
        linearIndependent := fun b hb => by
          have h1 := (((ε.linearIndependent_vec hb).map' (e b).toLinearMap (e b).ker).map'
            (Λ'.L b).subtype (Submodule.ker_subtype _)).comp _ (Fin.cast_injective hn)
          have hfun : (fun i => J b (ε.e (Fin.cast hn i) b)) =
              (⇑(Λ'.L b).subtype ∘ ⇑(e b).toLinearMap ∘ ε.vec hb) ∘ Fin.cast hn :=
            funext fun i => (he b (ε.vec hb (Fin.cast hn i))).symm
          change LinearIndependent ℝ (fun i => J b (ε.e (Fin.cast hn i) b))
          rw [hfun]
          exact h1 }
    have hvec : ∀ b (hb : b ∈ ε.U), ε'.vec hb = (e b ∘ ε.vec hb) ∘ Fin.cast hn := fun b hb =>
      funext fun i => Subtype.ext (he b (ε.vec hb (Fin.cast hn i))).symm
    have hkey : ∀ b ∈ ε.U, maxPowEquiv (e b) (σ b) = ε.coord b (σ b) • ε'.wedgeAt b := by
      intro b hb
      have h1 := ε.coord_smul_wedgeAt hb (σ b)
      have h2 : maxPowEquiv (e b) (ε.wedgeAt b) = ε'.wedgeAt b := by
        rw [ε.wedgeAt_of_mem hb, ε'.wedgeAt_of_mem hb, maxPowEquiv_wedge, hvec b hb,
          wedge_cast]
      calc maxPowEquiv (e b) (σ b) = maxPowEquiv (e b) (ε.coord b (σ b) • ε.wedgeAt b) := by
            rw [h1]
        _ = ε.coord b (σ b) • maxPowEquiv (e b) (ε.wedgeAt b) := LinearEquiv.map_smul _ _ _
        _ = _ := congrArg (ε.coord b (σ b) • ·) h2
    refine (Λ'.continuousWithinAt_section_iff ε' hqε).2 ?_
    refine ((Λ.continuousWithinAt_section_iff ε hqε).1 (hσ q hq)).congr_of_eventuallyEq ?_ ?_
    · exact eventually_nhdsWithin_of_eventually_nhds (Filter.eventually_of_mem
        (ε.isOpen.mem_nhds hqε) fun b hb => by
          change ε'.coord b (maxPowEquiv (e b) (σ b)) = _
          rw [hkey b hb, map_smul, ε'.coord_wedgeAt hb, smul_eq_mul, mul_one])
    · rw [hkey q hqε, map_smul, ε'.coord_wedgeAt hqε, smul_eq_mul, mul_one]
  · obtain ⟨h0, hoq⟩ := hσo q hq
    exact ⟨(maxPowEquiv (e q)).map_ne_zero_iff.2 h0,
      (congrArg (Module.Ray.map (maxPowEquiv (e q))) hoq).trans (Module.Ray.map_apply _ _ _)⟩

/-- **Cutting a continuous family by the kernel of a fixed map onto `ℝᵐ`** on every member: the
text's `L_t = T_{(t, φ(t), 0)} S ∩ {dt = 0}` (Lemma 6.6.5 (preprint 6.30)). -/
theorem exists_inf_ker {m : ℕ} (ℓ : W →L[ℝ] (Fin m → ℝ))
    (hℓ : ∀ q, (Λ.L q).map (ℓ : W →ₗ[ℝ] Fin m → ℝ) = ⊤) :
    ∃ Λ' : SubspaceFamily Q W, ∀ q, Λ'.L q = Λ.L q ⊓ LinearMap.ker (ℓ : W →ₗ[ℝ] Fin m → ℝ) := by
  have hdim : ∀ q, finrank ℝ ↥(Λ.L q ⊓ LinearMap.ker (ℓ : W →ₗ[ℝ] Fin m → ℝ)) + m = Λ.n := by
    intro q
    have h := LinearMap.finrank_range_add_finrank_ker
      ((ℓ : W →ₗ[ℝ] Fin m → ℝ).domRestrict (Λ.L q))
    rw [LinearMap.range_domRestrict, hℓ q, finrank_top, Module.finrank_fin_fun,
      LinearMap.ker_domRestrict, Λ.finrank_eq q] at h
    rw [← Submodule.map_comap_subtype, Submodule.finrank_map_subtype_eq]
    omega
  refine ⟨{ L := fun q => Λ.L q ⊓ LinearMap.ker (ℓ : W →ₗ[ℝ] Fin m → ℝ)
            n := Λ.n - m
            finiteDimensional := fun q => inferInstance
            finrank_eq := fun q => by have := hdim q; omega
            exists_frame := fun q₀ => ?_ }, fun q => rfl⟩
  obtain ⟨U, hU, hq₀, e, he, h⟩ := Λ.exists_frame q₀
  -- the matrices `A q : ℝⁿ → ℝᵐ`, `c ↦ ℓ(∑ cⱼ eⱼ(q))`
  let A : Q → (Fin Λ.n → ℝ) →L[ℝ] (Fin m → ℝ) := fun q =>
    ∑ j, (ContinuousLinearMap.proj j : (Fin Λ.n → ℝ) →L[ℝ] ℝ).smulRight (ℓ (e j q))
  have hAapp : ∀ q c, A q c = ℓ (∑ j, c j • e j q) := fun q c => by
    simp [A, map_sum, map_smul]
  have hAc : ContinuousOn A U := continuousOn_finsetSum _ fun j _ =>
    (ContinuousLinearMap.smulRightL ℝ (Fin Λ.n → ℝ) (Fin m → ℝ)
      (ContinuousLinearMap.proj j)).continuous.comp_continuousOn
        (ℓ.continuous.comp_continuousOn (he j))
  have hspan : ∀ q ∈ U, ∀ x ∈ Λ.L q, ∃ c : Fin Λ.n → ℝ, ∑ j, c j • e j q = x := by
    intro q hq x hx
    let v : Fin Λ.n → Λ.L q := fun j => ⟨e j q, (h q hq).1 j⟩
    have hv : LinearIndependent ℝ v := LinearIndependent.of_comp (Λ.L q).subtype (h q hq).2
    have htop := hv.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin, Λ.finrank_eq q])
    have hx' : (⟨x, hx⟩ : Λ.L q) ∈ Submodule.span ℝ (Set.range v) := htop ▸ Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx'
    refine ⟨c, ?_⟩
    have := congrArg Subtype.val hc
    simpa [v] using this
  have hAs : ∀ q ∈ U, Function.Surjective (A q) := by
    intro q hq y
    have hy : y ∈ (Λ.L q).map (ℓ : W →ₗ[ℝ] Fin m → ℝ) := (hℓ q).symm ▸ Submodule.mem_top
    obtain ⟨x, hx, rfl⟩ := hy
    obtain ⟨c, hc⟩ := hspan q hq x hx
    exact ⟨c, by rw [hAapp, hc]; rfl⟩
  have hAF : (A q₀).IsFredholm :=
    isFredholm_of_banach (A q₀) inferInstance (Submodule.closed_of_finiteDimensional _)
      inferInstance
  have hk : finrank ℝ (LinearMap.ker (A q₀ : (Fin Λ.n → ℝ) →ₗ[ℝ] Fin m → ℝ)) = Λ.n - m := by
    have h := LinearMap.finrank_range_add_finrank_ker (A q₀ : (Fin Λ.n → ℝ) →ₗ[ℝ] Fin m → ℝ)
    rw [LinearMap.range_eq_top.2 (hAs q₀ hq₀), finrank_top, Module.finrank_fin_fun,
      Module.finrank_fin_fun] at h
    omega
  obtain ⟨U', hU', hq₀', hU'U, c, hc, hc'⟩ := exists_kerFrame hU hAc hq₀ hAF (hAs q₀ hq₀)
  refine ⟨U', hU', hq₀', fun i q => ∑ j, c (Fin.cast hk.symm i) q j • e j q, fun i => ?_,
    fun q hq => ⟨fun i => ⟨Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ ((h q (hU'U hq)).1 j), ?_⟩, ?_⟩⟩
  · exact continuousOn_finsetSum _ fun j _ =>
      ((continuous_apply j).comp_continuousOn (hc _)).smul ((he j).mono hU'U)
  · change ℓ (∑ j, c (Fin.cast hk.symm i) q j • e j q) = 0
    rw [← hAapp]
    exact (hc' q hq).1 _
  · let g := Fintype.linearCombination ℝ (fun j => e j q)
    have hg : LinearMap.ker g = ⊥ := LinearMap.ker_eq_bot'.2 fun a ha =>
      funext (Fintype.linearIndependent_iff.1 (h q (hU'U hq)).2 a ha)
    have h1 := (((hc' q hq).2.1.comp _ (Fin.cast_injective hk.symm))).map' g hg
    exact h1

end SubspaceFamily

/-! ### Continuity of the stabilized orientations -/

/-! ### Swapping two blocks of a wedge -/

section Swap

variable {W : Type*} [AddCommGroup W] [Module ℝ W]

open ExteriorAlgebra in
/-- `x ∧ (b₁ ∧ … ∧ bₙ) = (−1)ⁿ (b₁ ∧ … ∧ bₙ) ∧ x` in the exterior algebra. -/
theorem ι_mul_ιMulti_comm (x : W) :
    ∀ {n : ℕ} (b : Fin n → W),
      ι ℝ x * ιMulti ℝ n b = (-1 : ℝ) ^ n • (ιMulti ℝ n b * ι ℝ x)
  | 0, b => by rw [ιMulti_zero_apply, mul_one, one_mul, pow_zero, one_smul]
  | n + 1, b => by
    have ih := ι_mul_ιMulti_comm x (Matrix.vecTail b)
    have hs : ι ℝ x * ι ℝ (b 0) = -(ι ℝ (b 0) * ι ℝ x) :=
      eq_neg_of_add_eq_zero_left (ι_add_mul_swap _ _)
    rw [ιMulti_succ_apply]
    calc ι ℝ x * (ι ℝ (b 0) * ιMulti ℝ n (Matrix.vecTail b))
        = -(ι ℝ (b 0) * (ι ℝ x * ιMulti ℝ n (Matrix.vecTail b))) := by
          rw [← mul_assoc, hs, neg_mul, mul_assoc]
      _ = -((-1 : ℝ) ^ n • (ι ℝ (b 0) * ιMulti ℝ n (Matrix.vecTail b) * ι ℝ x)) := by
          rw [ih, mul_smul_comm, mul_assoc]
      _ = (-1 : ℝ) ^ (n + 1) • (ι ℝ (b 0) * ιMulti ℝ n (Matrix.vecTail b) * ι ℝ x) := by
          rw [pow_succ, mul_neg_one, neg_smul]

open ExteriorAlgebra in
/-- `(a₁ ∧ … ∧ aₘ) ∧ (b₁ ∧ … ∧ bₙ) = (−1)^{mn} (b₁ ∧ … ∧ bₙ) ∧ (a₁ ∧ … ∧ aₘ)`. -/
theorem ιMulti_mul_comm :
    ∀ {m : ℕ} (a : Fin m → W) {n : ℕ} (b : Fin n → W),
      ιMulti ℝ m a * ιMulti ℝ n b = (-1 : ℝ) ^ (m * n) • (ιMulti ℝ n b * ιMulti ℝ m a)
  | 0, a, n, b => by rw [ιMulti_zero_apply, one_mul, mul_one, zero_mul, pow_zero, one_smul]
  | m + 1, a, n, b => by
    have ih := ιMulti_mul_comm (Matrix.vecTail a) b
    have h1 := ι_mul_ιMulti_comm (a 0) b
    rw [ιMulti_succ_apply]
    calc ι ℝ (a 0) * ιMulti ℝ m (Matrix.vecTail a) * ιMulti ℝ n b
        = (-1 : ℝ) ^ (m * n) • (ι ℝ (a 0) * ιMulti ℝ n b * ιMulti ℝ m (Matrix.vecTail a)) := by
          rw [mul_assoc, ih, mul_smul_comm, mul_assoc]
      _ = ((-1 : ℝ) ^ (m * n) * (-1) ^ n) •
            (ιMulti ℝ n b * (ι ℝ (a 0) * ιMulti ℝ m (Matrix.vecTail a))) := by
          rw [h1, smul_mul_assoc, smul_smul, mul_assoc]
      _ = (-1 : ℝ) ^ ((m + 1) * n) •
            (ιMulti ℝ n b * (ι ℝ (a 0) * ιMulti ℝ m (Matrix.vecTail a))) := by
          rw [← pow_add, add_one_mul]

/-- **Swapping two blocks**: `u ∧ v = (−1)^{pq} v ∧ u` for `p` vectors `u` and `q` vectors `v`. -/
theorem wedge_append_swap {p q : ℕ} (u : Fin p → W) (v : Fin q → W)
    (h1 : p + q = finrank ℝ W) (h2 : q + p = finrank ℝ W) :
    wedge (Fin.append u v) h1 = (-1 : ℝ) ^ (p * q) • wedge (Fin.append v u) h2 := by
  apply Subtype.ext
  simp only [coe_wedge, SetLike.val_smul]
  rw [← ExteriorAlgebra.ιMulti_mul_ιMulti, ← ExteriorAlgebra.ιMulti_mul_ιMulti, ιMulti_mul_comm]

open ExteriorAlgebra in
/-- **Reordering four blocks**: `(u ∧ v) ∧ (w ∧ x) = (−1)^{(q + r) s + q r} (u ∧ x) ∧ (w ∧ v)` for
blocks of `p`, `q`, `r`, `s` vectors. -/
theorem wedge_reorder {p q r s : ℕ} (u : Fin p → W) (v : Fin q → W) (w : Fin r → W)
    (x : Fin s → W) (h1 : p + q + (r + s) = finrank ℝ W) (h2 : p + s + (r + q) = finrank ℝ W) :
    wedge (Fin.append (Fin.append u v) (Fin.append w x)) h1 =
      (-1 : ℝ) ^ ((q + r) * s + q * r) •
        wedge (Fin.append (Fin.append u x) (Fin.append w v)) h2 := by
  apply Subtype.ext
  simp only [coe_wedge, SetLike.val_smul]
  rw [← ιMulti_mul_ιMulti, ← ιMulti_mul_ιMulti, ← ιMulti_mul_ιMulti, ← ιMulti_mul_ιMulti,
    ← ιMulti_mul_ιMulti]
  have e1 := ιMulti_mul_comm (Fin.append v w) x
  have e2 := ιMulti_mul_comm v w
  rw [← ιMulti_mul_ιMulti] at e1
  calc ιMulti ℝ p u * ιMulti ℝ q v * (ιMulti ℝ r w * ιMulti ℝ s x)
      = ιMulti ℝ p u * (ιMulti ℝ q v * ιMulti ℝ r w * ιMulti ℝ s x) := by
        rw [mul_assoc, mul_assoc]
    _ = (-1 : ℝ) ^ ((q + r) * s) •
          (ιMulti ℝ p u * (ιMulti ℝ s x * (ιMulti ℝ q v * ιMulti ℝ r w))) := by
        rw [e1, mul_smul_comm]
    _ = ((-1 : ℝ) ^ ((q + r) * s) * (-1 : ℝ) ^ (q * r)) •
          (ιMulti ℝ p u * ιMulti ℝ s x * (ιMulti ℝ r w * ιMulti ℝ q v)) := by
        rw [e2, mul_smul_comm, mul_smul_comm, smul_smul, mul_assoc]
    _ = _ := by rw [← pow_add, ← ιMulti_mul_ιMulti]

end Swap

/-! ### Wedges adapted to a short exact sequence -/

section Block

variable {V U : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup U] [Module ℝ U]

/-- **Wedges adapted to `0 → U → V → ℝᵏ → 0`**: for `ι : U → V` with image `ker pr`, a basis `β`
of `U` and a linear lift `L` of `pr`, `ι(v) ∧ w = det_β(v) det(pr w) · ι(β) ∧ L(e)`. -/
theorem wedge_append_block {p k : ℕ} (ιU : U →ₗ[ℝ] V) (pr : V →ₗ[ℝ] (Fin k → ℝ))
    (L : (Fin k → ℝ) →ₗ[ℝ] V) (hπL : ∀ r, pr (L r) = r)
    (hker : ∀ v, pr v = 0 → v ∈ LinearMap.range ιU) (β : Basis (Fin p) ℝ U) (v : Fin p → U)
    (w : Fin k → V) (h : p + k = finrank ℝ V) :
    wedge (Fin.append (ιU ∘ v) w) h =
      (β.det v * (Pi.basisFun ℝ (Fin k)).det (pr ∘ w)) •
        wedge (Fin.append (ιU ∘ β) (L ∘ Pi.basisFun ℝ (Fin k))) h := by
  rw [wedge_append_basis_left ιU β v w h]
  have hw : w = (⇑L ∘ (pr ∘ w)) + (w - ⇑L ∘ (pr ∘ w)) := by abel
  have hx : ∀ i, (w - ⇑L ∘ (pr ∘ w)) i ∈ Submodule.span ℝ (Set.range (ιU ∘ β)) := by
    intro i
    obtain ⟨y, hy⟩ := hker ((w - ⇑L ∘ (pr ∘ w)) i) (by simp [hπL])
    rw [← hy, Set.range_comp, Submodule.span_image, β.span_eq, Submodule.map_top]
    exact ⟨y, rfl⟩
  conv_lhs => rw [hw, wedge_append_add_right _ _ _ hx]
  rw [wedge_append_basis_right L _ (Pi.basisFun ℝ (Fin k)) (pr ∘ w) h, smul_smul]

/-- `wedge_append_block` for families indexed by `Fin p` and `Fin q` with `p = p'`, `q = k`. -/
theorem wedge_append_block' {p p' q k : ℕ} (ιU : U →ₗ[ℝ] V) (pr : V →ₗ[ℝ] (Fin k → ℝ))
    (L : (Fin k → ℝ) →ₗ[ℝ] V) (hπL : ∀ r, pr (L r) = r)
    (hker : ∀ v, pr v = 0 → v ∈ LinearMap.range ιU) (β : Basis (Fin p') ℝ U) (v : Fin p → U)
    (w : Fin q → V) (hp : p = p') (hq : q = k) (h : p + q = finrank ℝ V)
    (h' : p' + k = finrank ℝ V) :
    wedge (Fin.append (ιU ∘ v) w) h =
      (β.det (v ∘ Fin.cast hp.symm) * (Pi.basisFun ℝ (Fin k)).det ((pr ∘ w) ∘ Fin.cast hq.symm)) •
        wedge (Fin.append (ιU ∘ β) (L ∘ Pi.basisFun ℝ (Fin k))) h' := by
  subst hp hq
  exact wedge_append_block ιU pr L hπL hker β v w h

/-- The wedge `ι(β) ∧ L(e)` adapted to `0 → U → V → ℝᵏ → 0` is not zero. -/
theorem wedge_append_block_ne_zero [FiniteDimensional ℝ V] {p k : ℕ} (ιU : U →ₗ[ℝ] V)
    (pr : V →ₗ[ℝ] (Fin k → ℝ)) (L : (Fin k → ℝ) →ₗ[ℝ] V) (hπL : ∀ r, pr (L r) = r)
    (hker : ∀ v, pr v = 0 → v ∈ LinearMap.range ιU) (β : Basis (Fin p) ℝ U)
    (h : p + k = finrank ℝ V) :
    wedge (Fin.append (ιU ∘ β) (L ∘ Pi.basisFun ℝ (Fin k))) h ≠ 0 := by
  refine wedge_ne_zero_of_span_eq_top h fun v _ => ?_
  have hv : v = (v - L (pr v)) + L (pr v) := by abel
  rw [hv]
  refine Submodule.add_mem _ ?_ ?_
  · obtain ⟨y, hy⟩ := hker (v - L (pr v)) (by simp [hπL])
    rw [← hy, ← β.sum_repr y, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.castAdd k i, by simp⟩)
  · rw [← (Pi.basisFun ℝ (Fin k)).sum_repr (pr v), map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Fin.natAdd p i, by simp⟩)

end Block

/-! ### A good left-projection of `T` is one of `T ⊕ φ` -/

/-- **`Π_T ⊆ Π_{T ⊕ φ}`**: `R(P (T ⊕ φ)) = R(P)` as soon as `R(P T) = R(P)`. -/
theorem IsGoodLeftProj.coprod {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ} {T : E →L[ℝ] F} {P : F →L[ℝ] F}
    (hP : IsGoodLeftProj T P) (φ : (Fin k → ℝ) →L[ℝ] F) : IsGoodLeftProj (T.coprod φ) P where
  isProj := hP.isProj
  finite_coker := hP.finite_coker
  range_comp := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨_, rfl⟩
    · rw [← hP.range_comp]
      rintro _ ⟨x, rfl⟩
      exact ⟨(x, 0), by simp⟩

/-! ### The kernels of `P S` and of `P (S ⊕ ψ)` -/

section KerPS

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- `ker(P₁ S) → ker(P₂ (S ⊕ ψ))`, `e ↦ (e, 0)`, for `P₂ = P₁`. -/
def stabKerInl {P₁ P₂ : F →L[ℝ] F} (hP : P₂ = P₁) (S : E →L[ℝ] F) (ψ : (Fin k → ℝ) →L[ℝ] F) :
    LinearMap.ker ((P₁ ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F) →ₗ[ℝ]
      LinearMap.ker ((P₂ ∘L S.coprod ψ : E × (Fin k → ℝ) →L[ℝ] F) :
        E × (Fin k → ℝ) →ₗ[ℝ] F) :=
  LinearMap.codRestrict _ (LinearMap.inl ℝ E (Fin k → ℝ) ∘ₗ Submodule.subtype _) fun x => by
    subst hP
    change P₂ (S x + ψ 0) = 0
    rw [map_zero, add_zero]
    exact x.2

/-- `stabKerInl` is `e ↦ (e, 0)`. -/
@[simp] theorem coe_stabKerInl {P₁ P₂ : F →L[ℝ] F} (hP : P₂ = P₁) (S : E →L[ℝ] F)
    (ψ : (Fin k → ℝ) →L[ℝ] F) (x : LinearMap.ker ((P₁ ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) :
    (stabKerInl hP S ψ x : E × (Fin k → ℝ)) = ((x : E), 0) := rfl

/-- `ker(P (S ⊕ ψ)) → ℝᵏ`, `(e, r) ↦ r`. -/
def stabKerSnd (P : F →L[ℝ] F) (S : E →L[ℝ] F) (ψ : (Fin k → ℝ) →L[ℝ] F) :
    LinearMap.ker ((P ∘L S.coprod ψ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F) →ₗ[ℝ]
      (Fin k → ℝ) :=
  LinearMap.snd ℝ E (Fin k → ℝ) ∘ₗ Submodule.subtype _

/-- `stabKerSnd` is `(e, r) ↦ r`. -/
@[simp] theorem stabKerSnd_apply (P : F →L[ℝ] F) (S : E →L[ℝ] F) (ψ : (Fin k → ℝ) →L[ℝ] F)
    (v : LinearMap.ker ((P ∘L S.coprod ψ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F)) : stabKerSnd P S ψ v = (v : E × (Fin k → ℝ)).2 := rfl

/-- `e ↦ (e, 0)` is injective. -/
theorem stabKerInl_injective {P₁ P₂ : F →L[ℝ] F} (hP : P₂ = P₁) (S : E →L[ℝ] F)
    (ψ : (Fin k → ℝ) →L[ℝ] F) : Function.Injective (stabKerInl hP S ψ) := fun _ _ h =>
  Subtype.ext (congrArg Prod.fst (congrArg Subtype.val h))

/-- The kernel of the second component is the image of `e ↦ (e, 0)`. -/
theorem mem_range_stabKerInl {P₁ P₂ : F →L[ℝ] F} (hP : P₂ = P₁) (S : E →L[ℝ] F)
    (ψ : (Fin k → ℝ) →L[ℝ] F) (v : LinearMap.ker ((P₂ ∘L S.coprod ψ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F)) (hv : stabKerSnd P₂ S ψ v = 0) :
    v ∈ LinearMap.range (stabKerInl hP S ψ) := by
  have h2 : (v : E × (Fin k → ℝ)).2 = 0 := hv
  have hmem : (v : E × (Fin k → ℝ)).1 ∈ LinearMap.ker ((P₁ ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
    have := v.2
    rw [LinearMap.mem_ker] at this ⊢
    subst hP
    have hv' : (v : E × (Fin k → ℝ)) = ((v : E × (Fin k → ℝ)).1, 0) := Prod.ext rfl h2
    rw [hv'] at this
    simpa using this
  exact ⟨⟨_, hmem⟩, Subtype.ext (Prod.ext rfl h2.symm)⟩

/-- `(e, r) ↦ r` is onto `ℝᵏ` when `R(P S) = R(P)`. -/
theorem stabKerSnd_surjective {P : F →L[ℝ] F} {S : E →L[ℝ] F} (hP : IsGoodLeftProj S P)
    (ψ : (Fin k → ℝ) →L[ℝ] F) : Function.Surjective (stabKerSnd P S ψ) := by
  intro r
  have hr : -(P (ψ r)) ∈ LinearMap.range ((P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
    rw [hP.range_comp]
    exact ⟨-(ψ r), by simp⟩
  obtain ⟨e, he⟩ := hr
  refine ⟨⟨(e, r), ?_⟩, rfl⟩
  rw [LinearMap.mem_ker]
  have he' : P (S e) = -(P (ψ r)) := he
  simp [he']

/-- `dim ker(P (S ⊕ ψ)) = dim ker(P S) + k`. -/
theorem finrank_ker_comp_coprod {P : F →L[ℝ] F} {S : E →L[ℝ] F} (hP : IsGoodLeftProj S P)
    (ψ : (Fin k → ℝ) →L[ℝ] F)
    [FiniteDimensional ℝ (LinearMap.ker ((P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F))]
    [FiniteDimensional ℝ (LinearMap.ker ((P ∘L S.coprod ψ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F))] :
    finrank ℝ (LinearMap.ker ((P ∘L S.coprod ψ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F)) =
      finrank ℝ (LinearMap.ker ((P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) + k := by
  have h := LinearMap.finrank_range_add_finrank_ker (stabKerSnd P S ψ)
  have hker : LinearMap.ker (stabKerSnd P S ψ) = LinearMap.range (stabKerInl rfl S ψ) := by
    ext v
    refine ⟨fun hv => mem_range_stabKerInl rfl S ψ v hv, ?_⟩
    rintro ⟨x, rfl⟩
    rfl
  rw [LinearMap.range_eq_top.2 (stabKerSnd_surjective hP ψ), finrank_top, Module.finrank_fin_fun,
    hker, LinearMap.finrank_range_of_inj (stabKerInl_injective rfl S ψ)] at h
  omega

variable [CompleteSpace F] in
/-- **The index count of the projection sequence**: `dim ker(P S) + dim coker S =
dim ker S + dim F / R(P)`. -/
theorem finrank_ker_comp_add {P : F →L[ℝ] F} {S : E →L[ℝ] F} (hSF : S.IsFredholm)
    (hP : IsGoodLeftProj S P) :
    finrank ℝ (LinearMap.ker ((P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)) +
        finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) =
      finrank ℝ (LinearMap.ker (S : E →ₗ[ℝ] F)) +
        finrank ℝ (F ⧸ LinearMap.range (P : F →ₗ[ℝ] F)) := by
  have h := IsGoodLeftProj.fredholmIndex_comp hSF hP
  unfold fredholmIndex linIndex at h
  rw [(cokerCompEquiv hP).finrank_eq] at h
  omega

end KerPS

/-! ### The chart coordinate through `γ^P_S` -/

section Coord

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The chart coordinate through `γ^P_S`**: if `γ^P_S h = (v-wedge) ⊗ (w-wedge)*`, the coordinate
of `h` is `det(kerProj ∘ v) · det(w)⁻¹`. -/
theorem LocalDetChart.coord_eq_of_gamma (c : LocalDetChart E F) {S : FredholmOp E F}
    (hS : S ∈ c.baseSet) (h : DetFiber S) {k l : ℕ}
    (v : Fin k → LinearMap.ker ((c.P ∘L S.1 : E →L[ℝ] F) : E →ₗ[ℝ] F))
    (hk : k = finrank ℝ (LinearMap.ker ((c.P ∘L S.1 : E →L[ℝ] F) : E →ₗ[ℝ] F)))
    (w : Fin l → F ⧸ LinearMap.range ((c.P ∘L S.1 : E →L[ℝ] F) : E →ₗ[ℝ] F))
    (hl : l = finrank ℝ (F ⧸ LinearMap.range ((c.P ∘L S.1 : E →L[ℝ] F) : E →ₗ[ℝ] F)))
    (h1 : finrank ℝ c.K = k) (h2 : finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) = l)
    (hγ : gammaProj S.2 (c.isGoodLeftProj_of_lt S.1 hS) h =
      wedge v hk ⊗ₜ dualVec (wedge w hl)) :
    c.coord S h =
      ((Module.finBasis ℝ c.K).reindex (finCongr h1)).det (fun i => c.kerProj (v i)) *
        (((Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))).reindex
          (finCongr h2)).det
            (fun i => cokerCompEquiv (c.isGoodLeftProj_of_lt S.1 hS) (w i)))⁻¹ := by
  have hS' : ‖S.1 - c.T‖ < c.ε := hS
  have key := c.linDetEquivOfEq_wedge_tmul S.1 hS' rfl v hk w hl h1 h2
    (c.isGoodLeftProj_of_lt S.1 hS').range_comp
  rw [linDetEquivOfEq_self, LinearEquiv.refl_apply] at key
  have h1' := finrank_fredholmDet ((c.isGoodLeftProj_of_lt S.1 hS').isFredholm_comp S.2)
  rw [c.coord_apply hS', hγ, key, map_smul, dualVec_self h1' (c.frame_ne_zero S.1 hS'),
    smul_eq_mul, mul_one]
  rfl

omit [CompleteSpace E] [CompleteSpace F] in
/-- The determinant in `Module.finBasis` of `F / R(P)` does not depend on how `P` is written:
for vectors given by the same representatives in `F`, with a reindexing `Fin l₂ = Fin l₁`. -/
theorem det_finBasis_quot_congr {P₁ P₂ : F →L[ℝ] F} (h : P₂ = P₁)
    [FiniteDimensional ℝ (F ⧸ LinearMap.range (P₁ : F →ₗ[ℝ] F))]
    [FiniteDimensional ℝ (F ⧸ LinearMap.range (P₂ : F →ₗ[ℝ] F))] {l₁ l₂ : ℕ}
    (h₁ : finrank ℝ (F ⧸ LinearMap.range (P₁ : F →ₗ[ℝ] F)) = l₁)
    (h₂ : finrank ℝ (F ⧸ LinearMap.range (P₂ : F →ₗ[ℝ] F)) = l₂) (hl : l₂ = l₁)
    (w₁ : Fin l₁ → F ⧸ LinearMap.range (P₁ : F →ₗ[ℝ] F))
    (w₂ : Fin l₁ → F ⧸ LinearMap.range (P₂ : F →ₗ[ℝ] F))
    (hw : ∀ i, ∃ y : F, w₁ i = Submodule.Quotient.mk y ∧ w₂ i = Submodule.Quotient.mk y) :
    ((Module.finBasis ℝ (F ⧸ LinearMap.range (P₂ : F →ₗ[ℝ] F))).reindex (finCongr h₂)).det
        (w₂ ∘ Fin.cast hl) =
      ((Module.finBasis ℝ (F ⧸ LinearMap.range (P₁ : F →ₗ[ℝ] F))).reindex (finCongr h₁)).det
        w₁ := by
  subst h
  subst hl
  congr 1
  funext i
  obtain ⟨y, h1, h2⟩ := hw i
  exact h2.trans h1.symm

/-- **The chart coordinate of `a ⊗ d*`**: for the vectors of `gammaProj_wedge_tmul`, the coordinate
of `(a-wedge) ⊗ (d-wedge)*` is `det(kerProj (j a ∧ b)) · det(c ∧ Φ b)⁻¹`. -/
theorem LocalDetChart.coord_wedge_tmul (c : LocalDetChart E F) {T : E →L[ℝ] F}
    (hT : T.IsFredholm) (hTc : ‖T - c.T‖ < c.ε) {n l j : ℕ}
    {a : Fin n → LinearMap.ker (T : E →ₗ[ℝ] F)} (ha : LinearIndependent ℝ a)
    (hn : n = finrank ℝ (LinearMap.ker (T : E →ₗ[ℝ] F)))
    {d : Fin l → F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)} (hd : LinearIndependent ℝ d)
    (hl : l = finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)))
    {b : Fin j → LinearMap.ker ((c.P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)}
    (hb : LinearIndependent ℝ (Fin.append (projSeqJ T c.P ∘ a) b))
    (hj : n + j = finrank ℝ (LinearMap.ker ((c.P ∘L T : E →L[ℝ] F) : E →ₗ[ℝ] F)))
    {cc : Fin l → F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)}
    (hc : ∀ i, projSeqPi (T := T) (c.isGoodLeftProj_of_lt T hTc).isProj (cc i) = d i)
    (h1 : finrank ℝ c.K = n + j)
    (h2 : finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) = l + j) :
    c.coord ⟨T, hT⟩ (wedge a hn ⊗ₜ dualVec (wedge d hl)) =
      ((Module.finBasis ℝ c.K).reindex (finCongr h1)).det
          (fun i => c.kerProj (Fin.append (projSeqJ T c.P ∘ a) b i).1) *
        (((Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))).reindex
          (finCongr h2)).det (Fin.append cc (projSeqPhi T c.P ∘ b)))⁻¹ := by
  have hP := c.isGoodLeftProj_of_lt T hTc
  have hC : l + j = finrank ℝ (F ⧸ LinearMap.range ((c.P ∘L T : E →L[ℝ] F) :
      E →ₗ[ℝ] F)) := by
    rw [(cokerCompEquiv hP).finrank_eq]
    exact h2.symm
  have hγ := gammaProj_wedge_tmul hT hP ha hn hd hl hb hj hc hC
  rw [c.coord_eq_of_gamma (S := ⟨T, hT⟩) hTc _ _ hj _ hC h1 h2 hγ]
  simp only [Function.comp_apply, LinearEquiv.apply_symm_apply]

end Coord

/-! ### The key comparison of two charts with the same projection -/

section Key

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ}

/-- **The comparison function** `D(S, ψ)`: the `c'`-determinant of `(k(S), 0) ∧ k'(S ⊕ ψ)(t)`,
divided by the determinant of the `ℝᵏ`-components of `k'(S ⊕ ψ)(t)`. -/
def stabD (c : LocalDetChart E F) (c' : LocalDetChart (E × (Fin k → ℝ)) F)
    (hK : finrank ℝ c'.K = finrank ℝ c.K + k) (t : Fin k → c'.K) (S : E →L[ℝ] F)
    (ψ : (Fin k → ℝ) →L[ℝ] F) : ℝ :=
  ((Module.finBasis ℝ c'.K).reindex (finCongr hK)).det (fun i => c'.kerProj (Fin.append
      (fun i => ((c.kerMap S (Module.finBasis ℝ c.K i) : E), (0 : Fin k → ℝ)))
      (fun j => c'.kerMap (S.coprod ψ) (t j)) i)) /
    (Pi.basisFun ℝ (Fin k)).det (fun j => (c'.kerMap (S.coprod ψ) (t j)).2)

/-- **`D` through a lift**: `D(S, ψ)` is the `c'`-determinant of `(k(S), 0) ∧ L(e)` for any
linear lift `L` of `(e, r) ↦ r`. -/
theorem stabD_eq (c : LocalDetChart E F) (c' : LocalDetChart (E × (Fin k → ℝ)) F)
    (hP : c'.P = c.P) (hK : finrank ℝ c'.K = finrank ℝ c.K + k) (t : Fin k → c'.K)
    {S : E →L[ℝ] F} (hS : ‖S - c.T‖ < c.ε) {ψ : (Fin k → ℝ) →L[ℝ] F}
    (hA : ‖S.coprod ψ - c'.T‖ < c'.ε)
    (ht : (Pi.basisFun ℝ (Fin k)).det (fun j => (c'.kerMap (S.coprod ψ) (t j)).2) ≠ 0)
    (L : (Fin k → ℝ) →ₗ[ℝ] LinearMap.ker ((c'.P ∘L S.coprod ψ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F)) (hπL : ∀ r, stabKerSnd c'.P S ψ (L r) = r) :
    stabD c c' hK t S ψ = ((Module.finBasis ℝ c'.K).reindex (finCongr hK)).det (fun i =>
      c'.kerProj (Fin.append (stabKerInl hP S ψ ∘ (Module.finBasis ℝ c.K).map (c.kerEquiv S hS))
        (L ∘ Pi.basisFun ℝ (Fin k)) i).1) := by
  have := c.finiteDimensional_ker S hS
  have := c'.finiteDimensional_ker _ hA
  have hker : ∀ v, stabKerSnd c'.P S ψ v = 0 → v ∈ LinearMap.range (stabKerInl hP S ψ) :=
    mem_range_stabKerInl hP S ψ
  set β₀ := (Module.finBasis ℝ c.K).map (c.kerEquiv S hS) with hβ₀
  have hdim : finrank ℝ c.K + k = finrank ℝ (LinearMap.ker ((c'.P ∘L S.coprod ψ :
      E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)) :=
    hK.symm.trans (c'.kerEquiv _ hA).finrank_eq
  let t' : Fin k → LinearMap.ker ((c'.P ∘L S.coprod ψ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F) := fun i => c'.kerEquiv (S.coprod ψ) hA (t i)
  have ht' : (Pi.basisFun ℝ (Fin k)).det (⇑(stabKerSnd c'.P S ψ) ∘ t') ≠ 0 := ht
  have hD1 := wedge_append_block (stabKerInl hP S ψ) (stabKerSnd c'.P S ψ) L hπL hker β₀ β₀ t' hdim
  rw [Basis.det_self, one_mul] at hD1
  have E2 := c'.wedge_eq_det_smul_wedge_kerFrame (S.coprod ψ) hA
    (Fin.append (stabKerInl hP S ψ ∘ β₀) (L ∘ Pi.basisFun ℝ (Fin k))) hdim hK
  have E3 := c'.wedge_eq_det_smul_wedge_kerFrame (S.coprod ψ) hA
    (Fin.append (stabKerInl hP S ψ ∘ β₀) t') hdim hK
  rw [E2, E3, smul_smul] at hD1
  have key := smul_left_injective ℝ (c'.wedge_kerFrame_ne_zero (S.coprod ψ) hA) hD1
  have hf : (fun i => c'.kerProj (Fin.append
      (fun i => ((c.kerMap S (Module.finBasis ℝ c.K i) : E), (0 : Fin k → ℝ)))
      (fun j => c'.kerMap (S.coprod ψ) (t j)) i)) =
      (fun i => c'.kerProj (Fin.append (stabKerInl hP S ψ ∘ β₀) t' i).1) := by
    funext i
    induction i using Fin.addCases with
    | left i => simp only [Fin.append_left, Function.comp_apply]; rfl
    | right i => simp only [Fin.append_right]; rfl
  have hst : stabD c c' hK t S ψ = ((Module.finBasis ℝ c'.K).reindex (finCongr hK)).det
      (fun i => c'.kerProj (Fin.append (stabKerInl hP S ψ ∘ β₀) t' i).1) /
      (Pi.basisFun ℝ (Fin k)).det (⇑(stabKerSnd c'.P S ψ) ∘ t') := by
    unfold stabD
    rw [hf]
    rfl
  rw [hst, key, mul_div_cancel_left₀ _ ht']

/-- `D(S, ψ) ≠ 0`. -/
theorem stabD_ne_zero (c : LocalDetChart E F) (c' : LocalDetChart (E × (Fin k → ℝ)) F)
    (hP : c'.P = c.P) (hK : finrank ℝ c'.K = finrank ℝ c.K + k) (t : Fin k → c'.K)
    {S : E →L[ℝ] F} (hS : ‖S - c.T‖ < c.ε) {ψ : (Fin k → ℝ) →L[ℝ] F}
    (hA : ‖S.coprod ψ - c'.T‖ < c'.ε)
    (ht : (Pi.basisFun ℝ (Fin k)).det (fun j => (c'.kerMap (S.coprod ψ) (t j)).2) ≠ 0) :
    stabD c c' hK t S ψ ≠ 0 := by
  have := c.finiteDimensional_ker S hS
  have := c'.finiteDimensional_ker _ hA
  obtain ⟨L, hL⟩ := LinearMap.exists_rightInverse_of_surjective (stabKerSnd c'.P S ψ)
    (LinearMap.range_eq_top.2 (stabKerSnd_surjective (hP ▸ c.isGoodLeftProj_of_lt S hS) ψ))
  have hπL : ∀ r, stabKerSnd c'.P S ψ (L r) = r := fun r => LinearMap.congr_fun hL r
  have hdim : finrank ℝ c.K + k = finrank ℝ (LinearMap.ker ((c'.P ∘L S.coprod ψ :
      E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)) :=
    hK.symm.trans (c'.kerEquiv _ hA).finrank_eq
  rw [stabD_eq c c' hP hK t hS hA ht L hπL]
  intro h0
  have E2 := c'.wedge_eq_det_smul_wedge_kerFrame (S.coprod ψ) hA
    (Fin.append (stabKerInl hP S ψ ∘ (Module.finBasis ℝ c.K).map (c.kerEquiv S hS))
      (L ∘ Pi.basisFun ℝ (Fin k))) hdim hK
  rw [h0, zero_smul] at E2
  exact wedge_append_block_ne_zero (stabKerInl hP S ψ) (stabKerSnd c'.P S ψ) L hπL
    (mem_range_stabKerInl hP S ψ) _ hdim E2

/-- **The `c'`-determinant of a stabilized frame**: for `u, x` in `ker(P S)` and `v, w` in
`ker(P (S ⊕ ψ))`, `det((u,0) ∧ v ∧ w ∧ (x,0)) = ± det(u ∧ x) det(pr (w ∧ v)) D(S, ψ)`. -/
theorem det_kerProj_stab (c : LocalDetChart E F) (c' : LocalDetChart (E × (Fin k → ℝ)) F)
    (hP : c'.P = c.P) (hK : finrank ℝ c'.K = finrank ℝ c.K + k) (t : Fin k → c'.K)
    {S : E →L[ℝ] F} (hS : ‖S - c.T‖ < c.ε) {ψ : (Fin k → ℝ) →L[ℝ] F}
    (hA : ‖S.coprod ψ - c'.T‖ < c'.ε)
    (ht : (Pi.basisFun ℝ (Fin k)).det (fun j => (c'.kerMap (S.coprod ψ) (t j)).2) ≠ 0)
    {n l m j : ℕ} (u : Fin n → LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F))
    (x : Fin j → LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F))
    (v : Fin l → LinearMap.ker ((c'.P ∘L S.coprod ψ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F))
    (w : Fin m → LinearMap.ker ((c'.P ∘L S.coprod ψ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F))
    (h1 : finrank ℝ c'.K = n + l + (m + j)) (hp : finrank ℝ c.K = n + j) (hq : m + l = k) :
    ((Module.finBasis ℝ c'.K).reindex (finCongr h1)).det (fun i => c'.kerProj
        (Fin.append (Fin.append (stabKerInl hP S ψ ∘ u) v)
          (Fin.append w (stabKerInl hP S ψ ∘ x)) i).1) =
      (-1 : ℝ) ^ ((l + m) * j + l * m) *
        (((Module.finBasis ℝ c.K).reindex (finCongr hp)).det
            (fun i => c.kerProj (Fin.append u x i).1) *
          (Pi.basisFun ℝ (Fin k)).det ((stabKerSnd c'.P S ψ ∘ Fin.append w v) ∘ Fin.cast hq.symm)) *
        stabD c c' hK t S ψ := by
  have := c.finiteDimensional_ker S hS
  have := c'.finiteDimensional_ker _ hA
  obtain ⟨L, hL⟩ := LinearMap.exists_rightInverse_of_surjective (stabKerSnd c'.P S ψ)
    (LinearMap.range_eq_top.2 (stabKerSnd_surjective (hP ▸ c.isGoodLeftProj_of_lt S hS) ψ))
  have hπL : ∀ r, stabKerSnd c'.P S ψ (L r) = r := fun r => LinearMap.congr_fun hL r
  rw [stabD_eq c c' hP hK t hS hA ht L hπL]
  set β₀ := (Module.finBasis ℝ c.K).map (c.kerEquiv S hS) with hβ₀
  have hdim1 : n + l + (m + j) = finrank ℝ (LinearMap.ker ((c'.P ∘L S.coprod ψ :
      E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)) :=
    h1.symm.trans (c'.kerEquiv _ hA).finrank_eq
  have hdim2 : n + j + (m + l) = finrank ℝ (LinearMap.ker ((c'.P ∘L S.coprod ψ :
      E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)) := by omega
  have hdim3 : finrank ℝ c.K + k = finrank ℝ (LinearMap.ker ((c'.P ∘L S.coprod ψ :
      E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)) := by omega
  have hW := wedge_reorder (stabKerInl hP S ψ ∘ u) v w (stabKerInl hP S ψ ∘ x) hdim1 hdim2
  rw [← comp_append (stabKerInl hP S ψ) u x,
    wedge_append_block' (stabKerInl hP S ψ) (stabKerSnd c'.P S ψ) L hπL
      (mem_range_stabKerInl hP S ψ) β₀ (Fin.append u x) (Fin.append w v) hp.symm hq hdim2 hdim3,
    smul_smul] at hW
  have E1 := c'.wedge_eq_det_smul_wedge_kerFrame (S.coprod ψ) hA
    (Fin.append (Fin.append (stabKerInl hP S ψ ∘ u) v) (Fin.append w (stabKerInl hP S ψ ∘ x)))
    hdim1 h1
  have E2 := c'.wedge_eq_det_smul_wedge_kerFrame (S.coprod ψ) hA
    (Fin.append (stabKerInl hP S ψ ∘ β₀) (L ∘ Pi.basisFun ℝ (Fin k))) hdim3 hK
  rw [E1, E2, smul_smul] at hW
  rw [smul_left_injective ℝ (c'.wedge_kerFrame_ne_zero (S.coprod ψ) hA) hW, hβ₀,
    Basis.det_map, Basis.det_reindex (Module.finBasis ℝ c.K)]
  rfl

/-- The parity count behind the sign: `(l + m) j + l m ≡ (m + l)(m + j) + m (mod 2)`. -/
theorem neg_one_pow_stab (m l j : ℕ) :
    (-1 : ℝ) ^ ((l + m) * j + l * m) = (-1) ^ ((m + l) * (m + j) + m) := by
  obtain ⟨r, hr⟩ := Nat.even_mul_succ_self m
  have he : (m + l) * (m + j) + m = (l + m) * j + l * m + 2 * r := by nlinarith [hr]
  rw [he, pow_add _ ((l + m) * j + l * m) (2 * r), pow_mul, neg_one_sq, one_pow, mul_one]

/-- **The comparison on adapted vectors** (the computation behind `coord_stabIota`): for the
vectors of Proposition 6.4.15 (preprint 6.15) and of `gammaProj_wedge_tmul`, the two chart coordinates differ by
`(−1)^{k dim F/R(P) + dim coker S} D(S, ψ)`. -/
theorem coord_stabIota_aux (c : LocalDetChart E F) (c' : LocalDetChart (E × (Fin k → ℝ)) F)
    (hP : c'.P = c.P) (hK : finrank ℝ c'.K = finrank ℝ c.K + k) (t : Fin k → c'.K)
    {S : E →L[ℝ] F} (hSF : S.IsFredholm) (hS : ‖S - c.T‖ < c.ε) {ψ : (Fin k → ℝ) →L[ℝ] F}
    (hψ : Function.Surjective (S.coprod ψ)) (hAF : (S.coprod ψ).IsFredholm)
    (hA : ‖S.coprod ψ - c'.T‖ < c'.ε)
    (ht : (Pi.basisFun ℝ (Fin k)).det (fun j => (c'.kerMap (S.coprod ψ) (t j)).2) ≠ 0)
    {n m l j : ℕ} (a : Basis (Fin n) ℝ (LinearMap.ker (S : E →ₗ[ℝ] F)))
    (hn : n = finrank ℝ (LinearMap.ker (S : E →ₗ[ℝ] F))) (cbar : Fin m → Fin k → ℝ)
    (hd : LinearIndependent ℝ (stabClass S ψ ∘ cbar))
    (hm : m = finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)))
    (bbar : Fin l → LinearMap.ker ((S.coprod ψ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F))
    (hbbar : LinearIndependent ℝ (Fin.append (stabJ S ψ ∘ a) bbar))
    (hkl : n + l = finrank ℝ (LinearMap.ker ((S.coprod ψ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F)))
    (hml : m + l = k) (b : Fin j → LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F))
    (hb : LinearIndependent ℝ (Fin.append (projSeqJ S c.P ∘ a) b))
    (hj : n + j = finrank ℝ (LinearMap.ker ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F)))
    (hjm : m + j = finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))) (e' : Fin m → E)
    (he' : ∀ i, c.P (S (e' i)) = -(c.P (ψ (cbar i)))) :
    c'.coord ⟨S.coprod ψ, hAF⟩
        (stabIota hSF hψ (wedge a hn ⊗ₜ dualVec (wedge (stabClass S ψ ∘ cbar) hm))) =
      ((-1 : ℝ) ^ (k * finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) + m) *
          stabD c c' hK t S ψ) *
        c.coord ⟨S, hSF⟩ (wedge a hn ⊗ₜ dualVec (wedge (stabClass S ψ ∘ cbar) hm)) := by
  have hPS : IsGoodLeftProj S c.P := c.isGoodLeftProj_of_lt S hS
  have := hSF.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) := hSF.finite_coker
  have := c.finiteDimensional_ker S hS
  have := c'.finiteDimensional_ker _ hA
  have := finiteDimensional_ker_coprod (T := S) (φ := ψ)
  have hK1 : finrank ℝ c.K = n + j := (c.kerEquiv S hS).finrank_eq.trans hj.symm
  have hK1A : finrank ℝ c'.K = n + l + (m + j) := by omega
  have hdimA : n + l + (m + j) = finrank ℝ (LinearMap.ker ((c'.P ∘L S.coprod ψ :
      E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)) :=
    hK1A.symm.trans (c'.kerEquiv _ hA).finrank_eq
  -- the `S`-side coordinate
  let cc : Fin m → F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F) :=
    fun i => Submodule.Quotient.mk (S (e' i) + ψ (cbar i))
  have hcc : ∀ i, projSeqPi (T := S) hPS.isProj (cc i) = (stabClass S ψ ∘ cbar) i := by
    intro i
    change Submodule.Quotient.mk ((LinearMap.id - (c.P : F →ₗ[ℝ] F) : F →ₗ[ℝ] F)
      (S (e' i) + ψ (cbar i))) = Submodule.Quotient.mk (ψ (cbar i))
    rw [Submodule.Quotient.eq]
    refine ⟨e' i, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, ContinuousLinearMap.coe_coe, map_add,
      he']
    abel
  have hcS := c.coord_wedge_tmul hSF hS a.linearIndependent hn hd hm hb hj hcc hK1 hjm.symm
  -- the vectors `b₁ᵢ = (e'ᵢ, c̄ᵢ) ∈ ker(P (S ⊕ ψ))`
  have hb₁ : ∀ i, ((e' i, cbar i) : E × (Fin k → ℝ)) ∈ LinearMap.ker
      ((c'.P ∘L S.coprod ψ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F) := by
    intro i
    rw [LinearMap.mem_ker]
    change c'.P (S (e' i) + ψ (cbar i)) = 0
    rw [hP, map_add, he', neg_add_cancel]
  let b₁ : Fin m → LinearMap.ker ((c'.P ∘L S.coprod ψ : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F) := fun i => ⟨(e' i, cbar i), hb₁ i⟩
  have hδ := det_kerProj_stab c c' hP hK t hS hA ht (projSeqJ S c.P ∘ a) b
    (projSeqJ (S.coprod ψ) c'.P ∘ bbar) b₁ hK1A hK1 hml
  have hpr : ⇑(stabKerSnd c'.P S ψ) ∘ Fin.append b₁ (⇑(projSeqJ (S.coprod ψ) c'.P) ∘ bbar) =
      Fin.append cbar (fun i => ((bbar i : E × (Fin k → ℝ))).2) := by
    rw [comp_append]
    rfl
  rw [hpr] at hδ
  have hvec_eq : Fin.append (⇑(projSeqJ (S.coprod ψ) c'.P) ∘ Fin.append (⇑(stabJ S ψ) ∘ a) bbar)
      (Fin.append b₁ (⇑(stabKerInl hP S ψ) ∘ b)) =
      Fin.append (Fin.append (⇑(stabKerInl hP S ψ) ∘ (⇑(projSeqJ S c.P) ∘ a))
        (⇑(projSeqJ (S.coprod ψ) c'.P) ∘ bbar)) (Fin.append b₁ (⇑(stabKerInl hP S ψ) ∘ b)) := by
    rw [comp_append]
    rfl
  -- `det(c̄, b̄₂) ≠ 0` and `det_c(j a ∧ b) ≠ 0`
  have hx₀ : (wedge a hn ⊗ₜ dualVec (wedge (stabClass S ψ ∘ cbar) hm) : fredholmDet S) ≠ 0 :=
    tmul_ne_zero_of_ne_zero (wedge_basis_ne_zero' a hn)
      (dualVec_ne_zero finrank_maxPow ((wedge_ne_zero_iff hm).2 hd))
  have hprop := proposition_6_4_15 hSF hψ a cbar hd hm bbar hbbar hkl hml
  have hcdet : (Pi.basisFun ℝ (Fin k)).det
      (Fin.append cbar (fun i => ((bbar i : E × (Fin k → ℝ))).2) ∘ Fin.cast hml.symm) ≠ 0 := by
    intro h0
    rw [h0, inv_zero, zero_smul] at hprop
    exact hx₀ ((stabIota_bijective hSF hψ).1 (hprop.trans (map_zero _).symm))
  have hδS : ((Module.finBasis ℝ c.K).reindex (finCongr hK1)).det
      (fun i => c.kerProj (Fin.append (projSeqJ S c.P ∘ a) b i).1) ≠ 0 := by
    intro h0
    have E := c.wedge_eq_det_smul_wedge_kerFrame S hS (Fin.append (projSeqJ S c.P ∘ a) b) hj hK1
    rw [h0, zero_smul] at E
    exact (wedge_ne_zero_iff hj).2 hb E
  -- the `S ⊕ ψ`-side coordinate
  have hvec : LinearIndependent ℝ (Fin.append
      (⇑(projSeqJ (S.coprod ψ) c'.P) ∘ Fin.append (⇑(stabJ S ψ) ∘ a) bbar)
      (Fin.append b₁ (⇑(stabKerInl hP S ψ) ∘ b))) := by
    rw [hvec_eq, ← wedge_ne_zero_iff hdimA,
      c'.wedge_eq_det_smul_wedge_kerFrame (S.coprod ψ) hA _ hdimA hK1A, hδ]
    exact smul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (mul_ne_zero hδS hcdet)) (stabD_ne_zero c c' hP hK t hS hA ht))
      (c'.wedge_kerFrame_ne_zero _ hA)
  have hM' : finrank ℝ (F ⧸ LinearMap.range (c'.P : F →ₗ[ℝ] F)) = 0 + (m + j) := by
    rw [hP]
    omega
  have hcA : c'.coord ⟨S.coprod ψ, hAF⟩
      (wedge (Fin.append (stabJ S ψ ∘ a) bbar) hkl ⊗ₜ stabOne hψ) = _ :=
    c'.coord_wedge_tmul hAF hA hbbar hkl (d := Fin.elim0) linearIndependent_empty_type
      (finrank_coker_coprod hψ).symm hvec hdimA (cc := Fin.elim0) (fun i => i.elim0) hK1A hM'
  have hden : ((Module.finBasis ℝ (F ⧸ LinearMap.range (c'.P : F →ₗ[ℝ] F))).reindex
      (finCongr hM')).det (Fin.append Fin.elim0
        (projSeqPhi (S.coprod ψ) c'.P ∘ Fin.append b₁ (stabKerInl hP S ψ ∘ b))) =
      ((Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))).reindex
        (finCongr hjm.symm)).det (Fin.append cc (projSeqPhi S c.P ∘ b)) := by
    rw [Fin.elim0_append]
    refine det_finBasis_quot_congr hP hjm.symm hM' (Nat.zero_add _) _ _ fun i => ?_
    induction i using Fin.addCases with
    | left i =>
      exact ⟨S (e' i) + ψ (cbar i), by simp only [Fin.append_left]; rfl,
        by simp only [Function.comp_apply, Fin.append_left]; rfl⟩
    | right i =>
      refine ⟨S (b i), by simp only [Fin.append_right, Function.comp_apply]; rfl, ?_⟩
      simp only [Function.comp_apply, Fin.append_right]
      change Submodule.Quotient.mk ((S.coprod ψ) ((b i : E), (0 : Fin k → ℝ))) = _
      rw [ContinuousLinearMap.coprod_apply, map_zero, add_zero]
  rw [hvec_eq, hδ, hden] at hcA
  have hsign : (-1 : ℝ) ^ ((l + m) * j + l * m) =
      (-1) ^ (k * finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) + m) := by
    rw [← hjm, ← hml]
    exact neg_one_pow_stab m l j
  rw [hprop]
  refine ((c'.coord _).map_smul _ _).trans ?_
  rw [smul_eq_mul, hcA, hcS, ← hsign]
  have h1 := inv_mul_cancel₀ hcdet
  linear_combination ((-1 : ℝ) ^ ((l + m) * j + l * m) *
    ((Module.finBasis ℝ c.K).reindex (finCongr hK1)).det
      (fun i => c.kerProj (Fin.append (projSeqJ S c.P ∘ a) b i).1) * stabD c c' hK t S ψ *
    (((Module.finBasis ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))).reindex
        (finCongr hjm.symm)).det (Fin.append cc (projSeqPhi S c.P ∘ b)))⁻¹) * h1

/-- **The chart coordinate of the stabilization**: in charts `c` of `DET(E, F)` and `c'` of
`DET(E × ℝᵏ, F)` with the same projection `P`, the coordinate of `ι_ψ(x)` is
`(−1)^{k · dim F/R(P) + dim coker S} D(S, ψ)` times the coordinate of `x`. -/
theorem coord_stabIota (c : LocalDetChart E F) (c' : LocalDetChart (E × (Fin k → ℝ)) F)
    (hP : c'.P = c.P) (hK : finrank ℝ c'.K = finrank ℝ c.K + k) (t : Fin k → c'.K)
    {S : E →L[ℝ] F} (hSF : S.IsFredholm) (hS : ‖S - c.T‖ < c.ε) {ψ : (Fin k → ℝ) →L[ℝ] F}
    (hψ : Function.Surjective (S.coprod ψ)) (hAF : (S.coprod ψ).IsFredholm)
    (hA : ‖S.coprod ψ - c'.T‖ < c'.ε)
    (ht : (Pi.basisFun ℝ (Fin k)).det (fun j => (c'.kerMap (S.coprod ψ) (t j)).2) ≠ 0)
    (x : fredholmDet S) :
    c'.coord ⟨S.coprod ψ, hAF⟩ (stabIota hSF hψ x) =
      ((-1 : ℝ) ^ (k * finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) +
          finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F))) * stabD c c' hK t S ψ) *
        c.coord ⟨S, hSF⟩ x := by
  classical
  have hPS : IsGoodLeftProj S c.P := c.isGoodLeftProj_of_lt S hS
  have := hSF.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) := hSF.finite_coker
  have := c.finiteDimensional_ker S hS
  have := finiteDimensional_ker_coprod (T := S) (φ := ψ)
  have := hPS.finite_coker
  choose cbar hcbar using fun i =>
    stabClass_surjective hψ (Module.finBasis ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) i)
  have hd : LinearIndependent ℝ (stabClass S ψ ∘ cbar) := by
    have : stabClass S ψ ∘ cbar = Module.finBasis ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) :=
      funext hcbar
    rw [this]
    exact (Module.finBasis ℝ _).linearIndependent
  obtain ⟨l, bbar, hbbar, hkl⟩ := exists_linearIndependent_append (stabJ S ψ) stabJ_injective
    (Module.finBasis ℝ (LinearMap.ker (S : E →ₗ[ℝ] F))).linearIndependent rfl
  have hml := stab_card_eq hSF hψ rfl hkl
  obtain ⟨j, b, hb, hj⟩ := exists_linearIndependent_append (projSeqJ S c.P) (proposition_6_4_10 hPS).1
    (Module.finBasis ℝ (LinearMap.ker (S : E →ₗ[ℝ] F))).linearIndependent rfl
  have hidx := finrank_ker_comp_add hSF hPS
  have hjm : finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) + j =
      finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) := by omega
  have hex : ∀ i, ∃ e : E, c.P (S e) = -(c.P (ψ (cbar i))) := fun i => by
    have h : -(c.P (ψ (cbar i))) ∈ LinearMap.range ((c.P ∘L S : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
      rw [hPS.range_comp]
      exact ⟨-(ψ (cbar i)), by simp⟩
    obtain ⟨e, he⟩ := h
    exact ⟨e, he⟩
  choose e' he' using hex
  have key := coord_stabIota_aux c c' hP hK t hSF hS hψ hAF hA ht _ rfl cbar hd rfl bbar hbbar
    hkl hml b hb hj hjm e' he'
  have hx₀ : (wedge (Module.finBasis ℝ (LinearMap.ker (S : E →ₗ[ℝ] F))) rfl ⊗ₜ
      dualVec (wedge (stabClass S ψ ∘ cbar) rfl) : fredholmDet S) ≠ 0 :=
    tmul_ne_zero_of_ne_zero (wedge_basis_ne_zero' _ rfl)
      (dualVec_ne_zero finrank_maxPow ((wedge_ne_zero_iff rfl).2 hd))
  obtain ⟨r, rfl⟩ := exists_smul_eq_of_finrank_eq_one (finrank_fredholmDet hSF) hx₀ x
  rw [LinearMap.map_smul]
  refine ((c'.coord _).map_smul _ _).trans ?_
  refine Eq.trans ?_ (congrArg (fun y => ((-1 : ℝ) ^ (k * finrank ℝ (F ⧸ LinearMap.range
    (c.P : F →ₗ[ℝ] F)) + finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F))) *
      stabD c c' hK t S ψ) * y) ((c.coord ⟨S, hSF⟩).map_smul r _)).symm
  rw [smul_eq_mul, smul_eq_mul, key]
  ring

end Key

/-! ### Assembly -/

section Stab

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {k : ℕ}

omit [CompleteSpace E] [CompleteSpace F] in
/-- **The sign normalization `(−1)^{dim coker T}`** of the stabilization isomorphism `Φ`
(it depends neither on `k` nor on the index). -/
def stabSign (T : E →L[ℝ] F) : ℝˣ := (-1) ^ finrank ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F))

/-- A stabilization `T ⊕ φ` onto `F` of a Fredholm operator is Fredholm. -/
theorem isFredholm_coprod_of_surjective {T : E →L[ℝ] F} {φ : (Fin k → ℝ) →L[ℝ] F}
    (hT : T.IsFredholm) (hφ : Function.Surjective (T.coprod φ)) : (T.coprod φ).IsFredholm := by
  have := hT.finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (T : E →ₗ[ℝ] F)) := hT.finite_coker
  have hr : (T.coprod φ).range = ⊤ := LinearMap.range_eq_top.2 hφ
  refine isFredholm_of_banach _ finiteDimensional_ker_coprod ?_ ?_
  · rw [hr]
    exact isClosed_univ
  · rw [hr]
    exact Submodule.CoFG.top

/-- **Sections of `DET` over `C` in a chart**: a section continuous on `U` has a continuous chart
coordinate on `U ∩ ball`. -/
theorem continuousOn_coord_of_section {C : Set (E →L[ℝ] F)} {hC : ∀ T ∈ C, T.IsFredholm}
    {σ : ∀ b : C, DetOn C hC b} {U : Set C}
    (hσ : ContinuousOn (fun b => TotalSpace.mk' ℝ b (σ b)) U) (c : LocalDetChart E F) :
    ContinuousOn (fun b : C => c.coord (fredholmIncl hC b) (σ b))
      (U ∩ {b | ‖(b : E →L[ℝ] F) - c.T‖ < c.ε}) := by
  let e := (detPrebundle E F).trivializationOfMemPretrivializationAtlas ⟨c, rfl⟩
  have h1 : ContinuousOn
      (fun b => Pullback.lift (fredholmIncl hC) (TotalSpace.mk' ℝ b (σ b))) U :=
    (Pullback.continuous_lift ℝ (DetFiber (E := E) (F := F)) (fredholmIncl hC)).comp_continuousOn hσ
  have h2 : ContinuousOn
      (fun b => e (Pullback.lift (fredholmIncl hC) (TotalSpace.mk' ℝ b (σ b))))
      (U ∩ {b | ‖(b : E →L[ℝ] F) - c.T‖ < c.ε}) :=
    e.continuousOn.comp (h1.mono inter_subset_left) fun b hb => hb.2
  exact continuous_snd.comp_continuousOn h2

/-- **Chart coordinates of a section along a continuous family in `C`**: for continuous
`g : X → C`, the chart coordinate of `σ ∘ g` is continuous where `g` lands in `U` and the ball. -/
theorem continuousOn_coord_of_section_comp {X : Type*} [TopologicalSpace X]
    {C : Set (E →L[ℝ] F)} {hC : ∀ T ∈ C, T.IsFredholm}
    {σ : ∀ b : C, DetOn C hC b} {U : Set C}
    (hσ : ContinuousOn (fun b => TotalSpace.mk' ℝ b (σ b)) U) (c : LocalDetChart E F)
    {g : X → E →L[ℝ] F} (hg : Continuous g) (hgC : ∀ x, g x ∈ C) :
    ContinuousOn (fun x => c.coord ⟨g x, hC _ (hgC x)⟩ (σ ⟨g x, hgC x⟩))
      {x | (⟨g x, hgC x⟩ : C) ∈ U ∧ ‖g x - c.T‖ < c.ε} := by
  have h := (continuousOn_coord_of_section hσ c).comp (hg.subtype_mk hgC).continuousOn
    (s := {x | (⟨g x, hgC x⟩ : C) ∈ U ∧ ‖g x - c.T‖ < c.ε}) fun _ hx => ⟨hx.1, hx.2⟩
  exact h

/-- **Frames of a family of kernels from the chart with `P = 1`**: for surjective `A_q` and the
chart `c` at `A_{q₀}` with `P = 1`, the frame `c.kerMap (A q) (bᵢ)` of `ker A_q` reads
`λ(ker A_q) ≅ det(A_q)` as the chart coordinate of `c`. -/
theorem exists_frame_coord_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [CompleteSpace V] {A : Q → V →L[ℝ] F} (hAc : Continuous A) (hAF : ∀ q, (A q).IsFredholm)
    (hAs : ∀ q, Function.Surjective (A q)) (Λ : SubspaceFamily Q V)
    (hΛ : ∀ q, Λ.L q = LinearMap.ker (A q : V →ₗ[ℝ] F)) (c : LocalDetChart V F) (q₀ : Q)
    (hcT : c.T = A q₀) (hcP : c.P = ContinuousLinearMap.id ℝ F) :
    ∃ ε : Λ.Frame, ε.U = {q | ‖A q - c.T‖ < c.ε} ∧ ∀ q ∈ ε.U, ∀ y : fredholmDet (A q),
      ε.coord q (maxPowEquiv (LinearEquiv.ofEq _ _ (hΛ q).symm)
        (detEquivOfSurjective (hAs q) y)) = c.coord ⟨A q, hAF q⟩ y := by
  classical
  have hker : ∀ S : V →L[ℝ] F, LinearMap.ker ((c.P ∘L S : V →L[ℝ] F) : V →ₗ[ℝ] F) =
      LinearMap.ker (S : V →ₗ[ℝ] F) := fun S => by rw [hcP, ContinuousLinearMap.id_comp]
  have hdim : ∀ q, ‖A q - c.T‖ < c.ε →
      finrank ℝ (LinearMap.ker (A q : V →ₗ[ℝ] F)) = finrank ℝ c.K := fun q hq => by
    rw [← hker, ← (c.kerEquiv (A q) hq).finrank_eq]
  have hq₀ : ‖A q₀ - c.T‖ < c.ε := by
    rw [hcT, sub_self, norm_zero]
    exact c.ε_pos
  have hn : Λ.n = finrank ℝ c.K := by rw [← Λ.finrank_eq q₀, hΛ q₀, hdim q₀ hq₀]
  let b := Module.finBasis ℝ c.K
  let ε : Λ.Frame :=
    { U := {q | ‖A q - c.T‖ < c.ε}
      isOpen := isOpen_lt ((hAc.sub continuous_const).norm) continuous_const
      e := fun i q => c.kerMap (A q) (b (Fin.cast hn i))
      continuousOn := fun i =>
        (c.continuousOn_kerMap_apply _).comp hAc.continuousOn fun q hq => hq
      mem := fun q hq i => by
        rw [hΛ q, ← hker]
        exact (c.lemma_6_5_2).2.1 (A q) hq _ (b (Fin.cast hn i)).2
      linearIndependent := fun q hq => by
        have h1 : LinearIndependent ℝ (c.kerEquiv (A q) hq ∘ b) :=
          b.linearIndependent.map' _ (c.kerEquiv (A q) hq).ker
        exact (h1.map' _ (Submodule.ker_subtype _)).comp (Fin.cast hn) (Fin.cast_injective hn) }
  refine ⟨ε, rfl, fun q hq y => ?_⟩
  have hS : ‖A q - c.T‖ < c.ε := hq
  have := (hAF q).finite_ker
  have : FiniteDimensional ℝ (F ⧸ LinearMap.range (A q : V →ₗ[ℝ] F)) := (hAF q).finite_coker
  have hn' := hdim q hS
  let a : Fin (finrank ℝ (LinearMap.ker (A q : V →ₗ[ℝ] F))) → LinearMap.ker (A q : V →ₗ[ℝ] F) :=
    fun i => ⟨c.kerMap (A q) (b (Fin.cast hn' i)), by
      have h := (c.lemma_6_5_2).2.1 (A q) hS _ (b (Fin.cast hn' i)).2
      rwa [hker] at h⟩
  have ha : LinearIndependent ℝ a := LinearIndependent.of_comp (LinearMap.ker _).subtype
    ((ε.linearIndependent q hq).comp (Fin.cast (hn'.trans hn.symm)) (Fin.cast_injective _))
  have h0 : 0 = finrank ℝ (F ⧸ LinearMap.range (A q : V →ₗ[ℝ] F)) :=
    (finrank_coker_of_surjective (hAs q)).symm
  set y₀ : fredholmDet (A q) := wedge a rfl ⊗ₜ
    dualVec (wedge (Fin.elim0 : Fin 0 → F ⧸ LinearMap.range (A q : V →ₗ[ℝ] F)) h0) with hy₀
  have hy₀0 : y₀ ≠ 0 := tmul_ne_zero_of_ne_zero ((wedge_ne_zero_iff rfl).2 ha)
    (dualVec_ne_zero finrank_maxPow ((wedge_ne_zero_iff h0).2 linearIndependent_empty_type))
  -- the chart coordinate of `y₀` is `1`
  have hPq := c.isGoodLeftProj_of_lt (A q) hS
  have hb : LinearIndependent ℝ (Fin.append (projSeqJ (A q) c.P ∘ a)
      (Fin.elim0 : Fin 0 → LinearMap.ker ((c.P ∘L A q : V →L[ℝ] F) : V →ₗ[ℝ] F))) := by
    rw [Fin.append_elim0]
    exact (ha.map' _ (LinearMap.ker_eq_bot.2 (proposition_6_4_10 hPq).1)).comp _ (Fin.cast_injective _)
  have htop : LinearMap.range ((c.P : F →L[ℝ] F) : F →ₗ[ℝ] F) = ⊤ := by
    rw [hcP]
    exact LinearMap.range_eq_top.2 fun y => ⟨y, rfl⟩
  have : Subsingleton (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) :=
    Submodule.Quotient.subsingleton_iff.2 htop
  have h2 : finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F)) = 0 + 0 :=
    Module.finrank_zero_of_subsingleton
  have hc0 := c.coord_wedge_tmul (hAF q) hS ha rfl
    (d := (Fin.elim0 : Fin 0 → F ⧸ LinearMap.range (A q : V →ₗ[ℝ] F)))
    linearIndependent_empty_type h0 hb
    (hn'.trans (c.kerEquiv _ hS).finrank_eq) (cc := Fin.elim0) (fun i => i.elim0) hn'.symm h2
  have hf : (fun i => c.kerProj (Fin.append (projSeqJ (A q) c.P ∘ a)
      (Fin.elim0 : Fin 0 → LinearMap.ker ((c.P ∘L A q : V →L[ℝ] F) : V →ₗ[ℝ] F)) i).1) =
      ⇑((Module.finBasis ℝ c.K).reindex (finCongr hn'.symm)) := by
    funext i
    rw [Fin.append_elim0, Basis.reindex_apply]
    exact (c.lemma_6_5_2).2.2.2 (A q) _
  have : IsEmpty (Fin (0 + 0)) := ⟨fun i => Fin.elim0 i⟩
  rw [hf, Basis.det_self, Basis.det_isEmpty, AlternatingMap.constOfIsEmpty_apply,
    Function.const_apply, inv_one, mul_one] at hc0
  -- the frame coordinate of `y₀` is `1`
  have hξ : dualVec (wedge (Fin.elim0 : Fin 0 → F ⧸ LinearMap.range (A q : V →ₗ[ℝ] F)) h0)
      (emptyWedge _ (finrank_coker_of_surjective (hAs q))) = 1 :=
    dualVec_self finrank_maxPow ((wedge_ne_zero_iff h0).2 linearIndependent_empty_type)
  have hvec : ⇑(LinearEquiv.ofEq _ _ (hΛ q).symm) ∘ a =
      ε.vec hq ∘ Fin.cast (hn'.trans hn.symm) := funext fun i => Subtype.ext rfl
  have hε0 : ε.coord q (maxPowEquiv (LinearEquiv.ofEq _ _ (hΛ q).symm)
      (detEquivOfSurjective (hAs q) y₀)) = 1 := by
    rw [hy₀, detEquivOfSurjective_tmul, hξ, one_smul, maxPowEquiv_wedge, hvec,
      wedge_cast _ (Λ.finrank_eq q).symm, ← ε.wedgeAt_of_mem hq, ε.coord_wedgeAt hq]
  rw [← hy₀] at hc0
  obtain ⟨r, rfl⟩ := exists_smul_eq_of_finrank_eq_one (finrank_fredholmDet (hAF q)) hy₀0 y
  rw [LinearEquiv.map_smul, LinearEquiv.map_smul]
  refine ((ε.coord q).map_smul _ _).trans ?_
  refine Eq.trans ?_ ((c.coord ⟨A q, hAF q⟩).map_smul r y₀).symm
  rw [hε0, hc0]

omit [CompleteSpace E] [CompleteSpace F] in
/-- `q ↦ T_q ⊕ φ_q` is continuous. -/
theorem continuous_coprod {T : Q → E →L[ℝ] F} (hTc : Continuous T)
    {φ : Q → (Fin k → ℝ) →L[ℝ] F} (hφc : Continuous φ) :
    Continuous fun q => (T q).coprod (φ q) := by
  have h : (fun q => (T q).coprod (φ q)) = fun q =>
      (T q).comp (ContinuousLinearMap.fst ℝ E (Fin k → ℝ)) +
        (φ q).comp (ContinuousLinearMap.snd ℝ E (Fin k → ℝ)) :=
    funext fun q => (ContinuousLinearMap.comp_fst_add_comp_snd _ _).symm
  rw [h]
  exact (hTc.clm_comp continuous_const).add (hφc.clm_comp continuous_const)

omit [CompleteSpace F] in
/-- The denominator of `D(T_q, φ_q)` is continuous on the ball of `c'`. -/
theorem continuousOn_stabD_den (c' : LocalDetChart (E × (Fin k → ℝ)) F) (t : Fin k → c'.K)
    {A : Q → E × (Fin k → ℝ) →L[ℝ] F} (hA : Continuous A) :
    ContinuousOn (fun q => (Pi.basisFun ℝ (Fin k)).det (fun j => (c'.kerMap (A q) (t j)).2))
      {q | ‖A q - c'.T‖ < c'.ε} :=
  (continuous_basis_det _).comp_continuousOn (continuousOn_pi.2 fun _ =>
    continuous_snd.comp_continuousOn
      ((c'.continuousOn_kerMap_apply _).comp hA.continuousOn fun _ hq => hq))

/-- **`D(T_q, φ_q)` is continuous** where it is defined by two charts and its denominator does not
vanish. -/
theorem continuousOn_stabD (c : LocalDetChart E F) (c' : LocalDetChart (E × (Fin k → ℝ)) F)
    (hK : finrank ℝ c'.K = finrank ℝ c.K + k) (t : Fin k → c'.K) {T : Q → E →L[ℝ] F}
    (hTc : Continuous T) {φ : Q → (Fin k → ℝ) →L[ℝ] F} (hφc : Continuous φ) :
    ContinuousOn (fun q => stabD c c' hK t (T q) (φ q))
      {q | ‖T q - c.T‖ < c.ε ∧ ‖(T q).coprod (φ q) - c'.T‖ < c'.ε ∧
        (Pi.basisFun ℝ (Fin k)).det (fun j => (c'.kerMap ((T q).coprod (φ q)) (t j)).2) ≠ 0} := by
  have hA := continuous_coprod hTc hφc
  refine ContinuousOn.div ?_ ((continuousOn_stabD_den c' t hA).mono fun q hq => hq.2.1)
    fun q hq => hq.2.2
  refine (continuous_basis_det _).comp_continuousOn (continuousOn_pi.2 fun i => ?_)
  induction i using Fin.addCases with
  | left i =>
    simp only [Fin.append_left]
    exact c'.kerProj.continuous.comp_continuousOn
      ((((c.continuousOn_kerMap_apply _).comp hTc.continuousOn fun _ hq => hq.1).prodMk
        continuousOn_const))
  | right i =>
    simp only [Fin.append_right]
    exact c'.kerProj.continuous.comp_continuousOn
      ((c'.continuousOn_kerMap_apply _).comp hA.continuousOn fun _ hq => hq.2.1)

omit [CompleteSpace E] [CompleteSpace F] in
/-- The ray of `Φ(v)`, `v ≠ 0`, is that of `λ(ι)(det(T ⊕ φ) ≅ λ(ker)) (ι_φ v)`. -/
theorem stabRayEquiv_ray {T : E →L[ℝ] F} {φ : (Fin k → ℝ) →L[ℝ] F} (hT : T.IsFredholm)
    (hφ : Function.Surjective (T.coprod φ)) {W : Type*} [AddCommGroup W] [Module ℝ W]
    {L : Submodule ℝ W} [FiniteDimensional ℝ L]
    (ι : LinearMap.ker ((T.coprod φ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] L) (v : fredholmDet T) (hv : v ≠ 0) :
    ∃ h, stabRayEquiv hT hφ ι (rayOfNeZero ℝ v hv) =
      rayOfNeZero ℝ (maxPowEquiv ι (detEquivOfSurjective hφ (stabIota hT hφ v))) h :=
  ⟨_, rfl⟩

/-- Change of chart on one fibre: `c'(y) = c(y) · c'(c⁻¹(1))`. -/
theorem LocalDetChart.coord_eq_coord_mul (c c' : LocalDetChart E F) {S : FredholmOp E F}
    (hS : S ∈ c.baseSet) (y : DetFiber S) :
    c'.coord S y = c.coord S y * c'.coord S (c.coordInv S 1) := by
  conv_lhs => rw [← c.coordInv_coord hS y]
  have h : c.coordInv S (c.coord S y) = c.coord S y • c.coordInv S 1 := by
    rw [← map_smul, smul_eq_mul, mul_one]
  rw [h, map_smul, smul_eq_mul]

/-- On the ball, the chart coordinate of a nonzero vector is not zero. -/
theorem LocalDetChart.coord_ne_zero_of_ne_zero (c : LocalDetChart E F) {S : FredholmOp E F}
    (hS : S ∈ c.baseSet) {y : DetFiber S} (hy : y ≠ 0) : c.coord S y ≠ 0 := fun h0 => by
  apply hy
  rw [← c.coordInv_coord hS y, h0, map_zero]

/-- **The frame coordinate of the normalized stabilized vector**: if `f` reads
`λ(ker(S ⊕ ψ)) ≅ det(S ⊕ ψ)` as the coordinate of a chart `c''`, then `f` of
`(−1)^{dim coker S} λ(ι)(ι_ψ v)` is `(−1)^{k dim F/R(P)} D(S, ψ) c(v) c''(c'⁻¹(1))`. -/
theorem coord_stabSign_smul (c : LocalDetChart E F) (c' c'' : LocalDetChart (E × (Fin k → ℝ)) F)
    (hP : c'.P = c.P) (hK : finrank ℝ c'.K = finrank ℝ c.K + k) (t : Fin k → c'.K)
    {S : E →L[ℝ] F} (hSF : S.IsFredholm) (hS : ‖S - c.T‖ < c.ε) {ψ : (Fin k → ℝ) →L[ℝ] F}
    (hψ : Function.Surjective (S.coprod ψ)) (hAF : (S.coprod ψ).IsFredholm)
    (hA : ‖S.coprod ψ - c'.T‖ < c'.ε)
    (ht : (Pi.basisFun ℝ (Fin k)).det (fun j => (c'.kerMap (S.coprod ψ) (t j)).2) ≠ 0)
    {W : Type*} [AddCommGroup W] [Module ℝ W] {L : Submodule ℝ W} [FiniteDimensional ℝ L]
    (ι : LinearMap.ker ((S.coprod ψ : E × (Fin k → ℝ) →L[ℝ] F) : E × (Fin k → ℝ) →ₗ[ℝ] F)
      ≃ₗ[ℝ] L) (f : maxPow L →ₗ[ℝ] ℝ)
    (hf : ∀ y, f (maxPowEquiv ι (detEquivOfSurjective hψ y)) = c''.coord ⟨S.coprod ψ, hAF⟩ y)
    (v : fredholmDet S) :
    f (((stabSign S : ℝˣ) : ℝ) • maxPowEquiv ι (detEquivOfSurjective hψ (stabIota hSF hψ v))) =
      (-1 : ℝ) ^ (k * finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))) *
        (stabD c c' hK t S ψ * (c.coord ⟨S, hSF⟩ v *
          c''.coord ⟨S.coprod ψ, hAF⟩ (c'.coordInv ⟨S.coprod ψ, hAF⟩ 1))) := by
  rw [map_smul, smul_eq_mul, hf]
  erw [c'.coord_eq_coord_mul c'' (S := ⟨_, hAF⟩) hA,
    coord_stabIota c c' hP hK t hSF hS hψ hAF hA ht]
  have hs : ((stabSign S : ℝˣ) : ℝ) = (-1) ^ finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) := by
    simp [stabSign]
  have hm2 : ((-1 : ℝ) ^ finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F))) *
      (-1) ^ finrank ℝ (F ⧸ LinearMap.range (S : E →ₗ[ℝ] F)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [hs, pow_add]
  linear_combination ((-1 : ℝ) ^ (k * finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))) *
    stabD c c' hK t S ψ * c.coord ⟨S, hSF⟩ v *
    c''.coord ⟨S.coprod ψ, hAF⟩ (c'.coordInv ⟨S.coprod ψ, hAF⟩ 1)) * hm2

/-- **The frame coordinate of the normalized stabilized section is continuous** where the three
charts and the section of `o` are defined and `D`'s denominator does not vanish. -/
theorem continuousOn_stab_coord (c : LocalDetChart E F)
    (c' c'' : LocalDetChart (E × (Fin k → ℝ)) F) (hK : finrank ℝ c'.K = finrank ℝ c.K + k)
    (t : Fin k → c'.K) {C : Set (E →L[ℝ] F)} {hC : ∀ T ∈ C, T.IsFredholm} {T : Q → E →L[ℝ] F}
    (hTc : Continuous T) (hTC : ∀ q, T q ∈ C) {φ : Q → (Fin k → ℝ) →L[ℝ] F}
    (hφc : Continuous φ) (hAF : ∀ q, ((T q).coprod (φ q)).IsFredholm)
    {σ : ∀ b : C, DetOn C hC b} {Uo : Set C}
    (hσ : ContinuousOn (fun b => TotalSpace.mk' ℝ b (σ b)) Uo) :
    ContinuousOn (fun q => stabD c c' hK t (T q) (φ q) * (c.coord ⟨T q, hC _ (hTC q)⟩
        (σ ⟨T q, hTC q⟩) * c''.coord ⟨(T q).coprod (φ q), hAF q⟩
          (c'.coordInv ⟨(T q).coprod (φ q), hAF q⟩ 1)))
      {q | (⟨T q, hTC q⟩ : C) ∈ Uo ∧ ‖T q - c.T‖ < c.ε ∧
        ‖(T q).coprod (φ q) - c'.T‖ < c'.ε ∧ ‖(T q).coprod (φ q) - c''.T‖ < c''.ε ∧
        (Pi.basisFun ℝ (Fin k)).det (fun j => (c'.kerMap ((T q).coprod (φ q)) (t j)).2) ≠ 0} := by
  have hAc' : Continuous fun q =>
      (⟨(T q).coprod (φ q), hAF q⟩ : FredholmOp (E × (Fin k → ℝ)) F) :=
    (continuous_coprod hTc hφc).subtype_mk hAF
  refine ContinuousOn.mul ?_ (ContinuousOn.mul ?_ ?_)
  · exact (continuousOn_stabD c c' hK t hTc hφc).mono fun q hq =>
      ⟨hq.2.1, hq.2.2.1, hq.2.2.2.2⟩
  · exact (continuousOn_coord_of_section_comp hσ c hTc hTC).mono fun q hq => ⟨hq.1, hq.2.1⟩
  · exact (lemma_6_5_9 c' c'').1.comp hAc'.continuousOn fun q hq => ⟨hq.2.2.1, hq.2.2.2.1⟩

/-- **The local step of the orientation of stabilized rays**: from charts `c` at `T q₀`,
`c'` (same `P`) and `c''` (with `P = 1`) at `T q₀ ⊕ φ q₀`, a local section `σ` of `o` and the
frame `ε''` of `λ(Λ)` from `c''`, the normalized stabilized section is a local section
representing the rays `(−1)^{dim coker T_q} Φ(o(T_q))` near `q₀`. -/
theorem stabRay_local {C : Set (E →L[ℝ] F)} {hC : ∀ T ∈ C, T.IsFredholm}
    (o : LineOrientation (DetOn C hC)) {T : Q → E →L[ℝ] F} (hTc : Continuous T)
    (hTC : ∀ q, T q ∈ C) {φ : Q → (Fin k → ℝ) →L[ℝ] F} (hφc : Continuous φ)
    (hφ : ∀ q, Function.Surjective ((T q).coprod (φ q)))
    {Λ : SubspaceFamily Q (E × (Fin k → ℝ))}
    (hΛ : ∀ q, Λ.L q = LinearMap.ker (((T q).coprod (φ q) : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F))
    (hAF : ∀ q, ((T q).coprod (φ q)).IsFredholm)
    (c : LocalDetChart E F) (c' c'' : LocalDetChart (E × (Fin k → ℝ)) F) (hPP : c'.P = c.P)
    (hK : finrank ℝ c'.K = finrank ℝ c.K + k) (t : Fin k → c'.K) {q₀ : Q}
    (hq₀c : ‖T q₀ - c.T‖ < c.ε) (hq₀c' : ‖(T q₀).coprod (φ q₀) - c'.T‖ < c'.ε)
    (hq₀c'' : ‖(T q₀).coprod (φ q₀) - c''.T‖ < c''.ε)
    (ht₀ : (Pi.basisFun ℝ (Fin k)).det
      (fun j => (c'.kerMap ((T q₀).coprod (φ q₀)) (t j)).2) ≠ 0)
    {Uo : Set C} (hUo : Uo ∈ 𝓝 (⟨T q₀, hTC q₀⟩ : C)) {σ : ∀ b : C, DetOn C hC b}
    (hσ : ContinuousOn (fun b => TotalSpace.mk' ℝ b (σ b)) Uo)
    (hσo : ∀ b ∈ Uo, ∃ h : σ b ≠ 0, o b = rayOfNeZero ℝ (σ b) h)
    (ε'' : Λ.Frame) (hε''U : ε''.U = {q | ‖(T q).coprod (φ q) - c''.T‖ < c''.ε})
    (hε'' : ∀ q ∈ ε''.U, ∀ y : fredholmDet ((T q).coprod (φ q)),
      ε''.coord q (maxPowEquiv (LinearEquiv.ofEq _ _ (hΛ q).symm)
        (detEquivOfSurjective (hφ q) y)) = c''.coord ⟨(T q).coprod (φ q), hAF q⟩ y) :
    ∃ U ∈ 𝓝 q₀, ∃ σ' : ∀ q, Λ.det q,
      ContinuousOn (fun q => TotalSpace.mk' ℝ q (σ' q)) U ∧
      ∀ q ∈ U, ∃ h : σ' q ≠ 0, stabSign (T q) •
        stabRayEquiv (hC _ (hTC q)) (hφ q) (LinearEquiv.ofEq _ _ (hΛ q).symm)
          (o ⟨T q, hTC q⟩) = rayOfNeZero ℝ (σ' q) h := by
  classical
  have hTF : ∀ q, (T q).IsFredholm := fun q => hC _ (hTC q)
  have hAc := continuous_coprod hTc hφc
  have hgc : Continuous fun q => (⟨T q, hTC q⟩ : C) := hTc.subtype_mk hTC
  -- the neighbourhood
  let U : Set Q := {q | (⟨T q, hTC q⟩ : C) ∈ Uo ∧ ‖T q - c.T‖ < c.ε ∧
    ‖(T q).coprod (φ q) - c'.T‖ < c'.ε ∧ ‖(T q).coprod (φ q) - c''.T‖ < c''.ε ∧
    (Pi.basisFun ℝ (Fin k)).det (fun j => (c'.kerMap ((T q).coprod (φ q)) (t j)).2) ≠ 0}
  have hU : U ∈ 𝓝 q₀ := by
    have h1 : ∀ᶠ q in 𝓝 q₀, (⟨T q, hTC q⟩ : C) ∈ Uo := hgc.continuousAt.preimage_mem_nhds hUo
    have h2 : ∀ᶠ q in 𝓝 q₀, ‖T q - c.T‖ < c.ε :=
      (isOpen_lt (hTc.sub continuous_const).norm continuous_const).mem_nhds hq₀c
    have h3 : ∀ᶠ q in 𝓝 q₀, ‖(T q).coprod (φ q) - c'.T‖ < c'.ε :=
      (isOpen_lt (hAc.sub continuous_const).norm continuous_const).mem_nhds hq₀c'
    have h4 : ∀ᶠ q in 𝓝 q₀, ‖(T q).coprod (φ q) - c''.T‖ < c''.ε :=
      (isOpen_lt (hAc.sub continuous_const).norm continuous_const).mem_nhds hq₀c''
    have h5 := ((continuousOn_stabD_den c' t hAc).continuousAt h3).eventually_ne ht₀
    filter_upwards [h1, h2, h3, h4, h5] with q a1 a2 a3 a4 a5 using ⟨a1, a2, a3, a4, a5⟩
  -- the section and its frame coordinate
  let σ' : ∀ q, Λ.det q := fun q => ((stabSign (T q) : ℝ) •
    maxPowEquiv (LinearEquiv.ofEq _ _ (hΛ q).symm) (detEquivOfSurjective (hφ q)
      (stabIota (hTF q) (hφ q) (σ ⟨T q, hTC q⟩))) : maxPow (Λ.L q))
  let G : Q → ℝ := fun q => (-1 : ℝ) ^ (k * finrank ℝ (F ⧸ LinearMap.range (c.P : F →ₗ[ℝ] F))) *
    (stabD c c' hK t (T q) (φ q) * (c.coord ⟨T q, hTF q⟩ (σ ⟨T q, hTC q⟩) *
      c''.coord ⟨(T q).coprod (φ q), hAF q⟩ (c'.coordInv ⟨(T q).coprod (φ q), hAF q⟩ 1)))
  have hG : ∀ q ∈ U, ε''.coord q (σ' q) = G q := by
    intro q hq
    obtain ⟨-, h1, h2, h3, h4⟩ := hq
    have hq'' : q ∈ ε''.U := by
      rw [hε''U]
      exact h3
    exact coord_stabSign_smul c c' c'' hPP hK t (hTF q) h1 (hφ q) (hAF q) h2 h4
      (LinearEquiv.ofEq _ _ (hΛ q).symm) (ε''.coord q) (hε'' q hq'') _
  have hGc : ContinuousOn G U := by
    have h := continuousOn_stab_coord c c' c'' hK t hTc hTC hφc hAF hσ
    exact continuousOn_const.mul h
  have hG0 : ∀ q ∈ U, G q ≠ 0 := by
    intro q hq
    obtain ⟨h0, h1, h2, h3, h4⟩ := hq
    obtain ⟨hne, -⟩ := hσo _ h0
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (mul_ne_zero
      (stabD_ne_zero c c' hPP hK t h1 h2 h4) (mul_ne_zero
        (c.coord_ne_zero_of_ne_zero (S := ⟨T q, hTF q⟩) h1 hne)
        ((lemma_6_5_9 c' c'').2 _ ⟨h2, h3⟩)))
  refine ⟨U, hU, σ', fun q hq => ?_, fun q hq => ?_⟩
  · have hq'' : q ∈ ε''.U := by
      rw [hε''U]
      exact hq.2.2.2.1
    have h := (hGc q hq).congr (fun x hx => hG x hx) (hG q hq)
    exact (Λ.continuousWithinAt_section_iff ε'' hq'').2 h
  · have hne : σ' q ≠ 0 := fun h => hG0 q hq (by rw [← hG q hq, h, map_zero])
    refine ⟨hne, ?_⟩
    obtain ⟨h0, hob⟩ := hσo _ hq.1
    obtain ⟨h', hr⟩ := stabRayEquiv_ray (hTF q) (hφ q) (LinearEquiv.ofEq _ _ (hΛ q).symm)
      (σ ⟨T q, hTC q⟩) h0
    have e1 : stabRayEquiv (hC _ (hTC q)) (hφ q) (LinearEquiv.ofEq _ _ (hΛ q).symm)
        (o ⟨T q, hTC q⟩) = rayOfNeZero ℝ _ h' :=
      (congrArg (stabRayEquiv (hC _ (hTC q)) (hφ q) (LinearEquiv.ofEq _ _ (hΛ q).symm))
        hob).trans hr
    exact (congrArg (fun r => stabSign (T q) • r) e1).trans rfl

/-- **The orientations received from `DET` through `Φ_{E_q}` vary continuously**: for a
continuous orientation `o` of `DET` over a set `C` of Fredholm operators, a norm-continuous family
`T_q ∈ C`, a continuous family `φ_q : ℝᵏ → F` with `T_q ⊕ φ_q` onto, and the family `Λ` of the
kernels `ker(T_q ⊕ φ_q)`, the sign-normalized rays `q ↦ (−1)^{dim coker T_q} Φ(o(T_q))` form an
orientation of `λ(Λ)`.  Without the sign this does not hold as we read it
(`not_isLineOrientation_stabRay_uncorrected`). -/
theorem isLineOrientation_stabRay {C : Set (E →L[ℝ] F)} {hC : ∀ T ∈ C, T.IsFredholm}
    (o : LineOrientation (DetOn C hC)) (T : Q → E →L[ℝ] F) (hTc : Continuous T)
    (hTC : ∀ q, T q ∈ C) (φ : Q → (Fin k → ℝ) →L[ℝ] F) (hφc : Continuous φ)
    (hφ : ∀ q, Function.Surjective ((T q).coprod (φ q)))
    (Λ : SubspaceFamily Q (E × (Fin k → ℝ)))
    (hΛ : ∀ q, Λ.L q = LinearMap.ker (((T q).coprod (φ q) : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F)) :
    IsLineOrientation Λ.det fun q => stabSign (T q) •
      stabRayEquiv (hC _ (hTC q)) (hφ q) (LinearEquiv.ofEq _ _ (hΛ q).symm) (o ⟨T q, hTC q⟩) := by
  classical
  intro q₀
  have hTF : ∀ q, (T q).IsFredholm := fun q => hC _ (hTC q)
  have hAF : ∀ q, ((T q).coprod (φ q)).IsFredholm := fun q =>
    isFredholm_coprod_of_surjective (hTF q) (hφ q)
  have hAc := continuous_coprod hTc hφc
  -- the charts at `T q₀` and at `T q₀ ⊕ φ q₀`
  obtain ⟨P, hP⟩ := exists_isGoodLeftProj (hTF q₀)
  obtain ⟨c, hcT, hcP⟩ := exists_localDetChart_of_proj (hTF q₀) hP
  obtain ⟨c', hc'T, hc'P⟩ := exists_localDetChart_of_proj (hAF q₀) (hP.coprod (φ q₀))
  obtain ⟨c'', hc''T, hc''P⟩ :=
    exists_localDetChart_of_proj (hAF q₀) (isGoodLeftProj_id_of_surjective (hφ q₀))
  have hPP : c'.P = c.P := hc'P.trans hcP.symm
  have hK : finrank ℝ c'.K = finrank ℝ c.K + k := by
    have := (hP.isFredholm_comp (hTF q₀)).finite_ker
    have := ((hP.coprod (φ q₀)).isFredholm_comp (hAF q₀)).finite_ker
    have h := finrank_ker_comp_coprod hP (φ q₀)
    change finrank ℝ (LinearMap.ker ((c'.P ∘L c'.T : E × (Fin k → ℝ) →L[ℝ] F) :
      E × (Fin k → ℝ) →ₗ[ℝ] F)) =
      finrank ℝ (LinearMap.ker ((c.P ∘L c.T : E →L[ℝ] F) : E →ₗ[ℝ] F)) + k
    rw [hc'T, hc'P, hcT, hcP]
    exact h
  have hq₀c : ‖T q₀ - c.T‖ < c.ε := by
    rw [hcT, sub_self, norm_zero]
    exact c.ε_pos
  have hq₀c' : ‖(T q₀).coprod (φ q₀) - c'.T‖ < c'.ε := by
    rw [hc'T, sub_self, norm_zero]
    exact c'.ε_pos
  have hq₀c'' : ‖(T q₀).coprod (φ q₀) - c''.T‖ < c''.ε := by
    rw [hc''T, sub_self, norm_zero]
    exact c''.ε_pos
  -- the vectors `t` with `det(kerMap(t)₂) = 1` at `q₀`
  obtain ⟨L, hL⟩ := LinearMap.exists_rightInverse_of_surjective (stabKerSnd c'.P (T q₀) (φ q₀))
    (LinearMap.range_eq_top.2 (stabKerSnd_surjective (hPP ▸ c.isGoodLeftProj_of_lt _ hq₀c) (φ q₀)))
  let t : Fin k → c'.K := fun j => c'.kerProj (L (Pi.basisFun ℝ (Fin k) j) : E × (Fin k → ℝ))
  have ht₀ : (Pi.basisFun ℝ (Fin k)).det
      (fun j => (c'.kerMap ((T q₀).coprod (φ q₀)) (t j)).2) ≠ 0 := by
    have h : (fun j => (c'.kerMap ((T q₀).coprod (φ q₀)) (t j)).2) = Pi.basisFun ℝ (Fin k) := by
      funext j
      rw [show (c'.kerMap ((T q₀).coprod (φ q₀)) (t j) : E × (Fin k → ℝ)) =
        (L (Pi.basisFun ℝ (Fin k) j) : E × (Fin k → ℝ)) from
          (c'.lemma_6_5_2).2.2.1 _ hq₀c' _ (L _).2]
      exact LinearMap.congr_fun hL _
    rw [h, Basis.det_self]
    exact one_ne_zero
  -- a local section of `o` and the frame of `λ(Λ)` from the chart with `P = 1`
  obtain ⟨Uo, hUo, σ, hσ, hσo⟩ := o.2 ⟨T q₀, hTC q₀⟩
  obtain ⟨ε'', hε''U, hε''⟩ := exists_frame_coord_eq hAc hAF hφ Λ hΛ c'' q₀ hc''T hc''P
  exact stabRay_local o hTc hTC hφc hφ hΛ hAF c c' c'' hPP hK t hq₀c hq₀c' hq₀c'' ht₀ hUo hσ hσo
    ε'' hε''U hε''

end Stab

/-! ### Without the sign: an instance

The rays `q ↦ Φ(o(T_q))` without the sign `(−1)^{dim coker T_q}` need not form an orientation.
`E = F = ℝ`, `k = 1`, `Q = ℝ`, `T_q = f(q) · 1` with `f(q) = q / (1 + |q|)`, `φ = pr₀`,
`Λ_q = ker(T_q ⊕ φ)` with the frame `(1, −f(q))`, `C` the ball of the chart of `DET` at `0` with
`P = 0`, and `o` the orientation of that chart's section `S ↦ (γ^0_S)⁻¹ ω(S)`.

In the frame, `Φ(o(T_q))` is the ray of `−(D₂(1)/D₁)` for `q ≠ 0` (Proposition 6.4.15 (preprint 6.15) with
`c̄, a` empty, `det(r) = −f(q)`) and of `+(D₂(1)/D₁)` at `q = 0` (`c̄ = (1)`, `b̄` empty):
the sign jumps where `dim coker T_q` jumps from `1` to `0`.
-/

namespace StabCounterexample

/-- Every operator `ℝ → ℝ` is Fredholm. -/
theorem isFredholm_real (S : ℝ →L[ℝ] ℝ) : S.IsFredholm :=
  isFredholm_of_banach S inferInstance (Submodule.closed_of_finiteDimensional _) inferInstance

/-- `P = 0` is a good left-projection for every `S : ℝ → ℝ`. -/
theorem isGoodLeftProj_zero (S : ℝ →L[ℝ] ℝ) : IsGoodLeftProj S (0 : ℝ →L[ℝ] ℝ) where
  isProj := ContinuousLinearMap.zero_comp _
  finite_coker := inferInstance
  range_comp := by rw [ContinuousLinearMap.zero_comp]

/-- The range of `0 : ℝ → ℝ` is a zero space. -/
scoped instance subsingleton_range_zero :
    Subsingleton (LinearMap.range ((0 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ)) :=
  ⟨fun x y => by
    have h0 : ∀ z : LinearMap.range ((0 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ), (z : ℝ) = 0 := fun z => by
      obtain ⟨a, ha⟩ := z.2
      rw [← ha]
      rfl
    exact Subtype.ext ((h0 x).trans (h0 y).symm)⟩

/-- The local determinant chart of `DET(ℝ, ℝ)` centred at `0`, with `P = 0`, `Y = 0`, `ε = 1`. -/
def chart0 : LocalDetChart ℝ ℝ where
  T := 0
  isFredholm := isFredholm_real 0
  P := 0
  isGoodLeftProj := isGoodLeftProj_zero 0
  Y := ⊥
  isTopCompl := by
    have h : LinearMap.ker (((0 : ℝ →L[ℝ] ℝ) ∘L (0 : ℝ →L[ℝ] ℝ) : ℝ →L[ℝ] ℝ) :
        ℝ →ₗ[ℝ] ℝ) = ⊤ := by
      ext x; simp
    rw [h]
    exact ⟨isCompl_top_bot, LinearMap.continuous_of_finiteDimensional _⟩
  ε := 1
  ε_pos := one_pos
  isGoodLeftProj_of_lt S _ := isGoodLeftProj_zero S
  exists_equiv_of_lt S _ :=
    ⟨(LinearEquiv.ofSubsingleton _ _).toContinuousLinearEquiv,
      ContinuousLinearMap.ext fun _ => Subsingleton.elim _ _⟩

/-- `f(q) = q / (1 + |q|)`. -/
def f (q : ℝ) : ℝ := q / (1 + |q|)

/-- `f` is continuous. -/
theorem continuous_f : Continuous f :=
  continuous_id.div (continuous_const.add continuous_abs) fun q => by positivity

/-- `|f(q)| < 1`. -/
theorem abs_f_lt (q : ℝ) : |f q| < 1 := by
  rw [f, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + |q|), div_lt_one (by positivity)]
  linarith

/-- `f(q) ≠ 0` for `q ≠ 0`. -/
theorem f_ne_zero {q : ℝ} (hq : q ≠ 0) : f q ≠ 0 := div_ne_zero hq (by positivity)

/-- `f(0) = 0`. -/
theorem f_zero : f 0 = 0 := by simp [f]

/-- `T q = f(q) · 1`. -/
def T (q : ℝ) : ℝ →L[ℝ] ℝ := f q • ContinuousLinearMap.id ℝ ℝ

/-- `T_q x = f(q) x`. -/
theorem T_apply (q x : ℝ) : T q x = f q * x := rfl

/-- `q ↦ T_q` is norm-continuous. -/
theorem continuous_T : Continuous T := continuous_f.smul continuous_const

/-- The ball of the chart. -/
def C : Set (ℝ →L[ℝ] ℝ) := {S | ‖S - chart0.T‖ < chart0.ε}

/-- Every `T_q` lies in the ball `C`. -/
theorem T_mem (q : ℝ) : T q ∈ C := by
  change ‖T q - 0‖ < 1
  rw [sub_zero]
  calc ‖T q‖ ≤ ‖f q‖ * ‖ContinuousLinearMap.id ℝ ℝ‖ := norm_smul_le _ _
    _ ≤ ‖f q‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
    _ < 1 := by rw [mul_one, Real.norm_eq_abs]; exact abs_f_lt q

/-- Every operator of `C` is Fredholm. -/
theorem hC : ∀ S ∈ C, S.IsFredholm := fun S _ => isFredholm_real S

/-- `φ = pr₀ : ℝ¹ → ℝ`. -/
def φ : (Fin 1 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj 0

/-- `T_q ⊕ φ` is onto. -/
theorem hφ (q : ℝ) : Function.Surjective ((T q).coprod φ) := fun y =>
  ⟨(0, fun _ => y), by simp [φ]⟩

/-- The kernel vector `(1, −f(q))` of `T q ⊕ φ`. -/
def kv (q : ℝ) : ℝ × (Fin 1 → ℝ) := (1, fun _ => -f q)

/-- `(1, −f(q)) ≠ 0`. -/
theorem kv_ne_zero (q : ℝ) : kv q ≠ 0 := fun h => one_ne_zero (congrArg Prod.fst h)

/-- `ker(T_q ⊕ φ) = ℝ (1, −f(q))`. -/
theorem ker_eq_span (q : ℝ) :
    LinearMap.ker (((T q).coprod φ : ℝ × (Fin 1 → ℝ) →L[ℝ] ℝ) : ℝ × (Fin 1 → ℝ) →ₗ[ℝ] ℝ) =
      Submodule.span ℝ {kv q} := by
  ext ⟨e, r⟩
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coprod_apply,
    Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨e, Prod.ext (by simp [kv]) (funext fun i => ?_)⟩
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have h' : f q * e + r 0 = 0 := h
    simp only [kv, Prod.smul_mk, smul_eq_mul, mul_one, Pi.smul_apply, mul_neg]
    linarith
  · rintro ⟨a, ha⟩
    have h1 : a = e := by simpa [kv] using congrArg Prod.fst ha
    have h2 : r 0 = -(a * f q) := by simpa [kv] using (congrArg (fun p => p.2 0) ha).symm
    change f q * e + r 0 = 0
    rw [h2, h1]
    ring

/-- `(1, −f(q)) ∈ ker(T_q ⊕ φ)`. -/
theorem kv_mem (q : ℝ) :
    kv q ∈ LinearMap.ker (((T q).coprod φ : ℝ × (Fin 1 → ℝ) →L[ℝ] ℝ) :
      ℝ × (Fin 1 → ℝ) →ₗ[ℝ] ℝ) := by
  rw [ker_eq_span]
  exact Submodule.mem_span_singleton_self _

/-- The kernel family `ker(T q ⊕ φ)`. -/
def Λ : SubspaceFamily ℝ (ℝ × (Fin 1 → ℝ)) where
  L q := LinearMap.ker (((T q).coprod φ : ℝ × (Fin 1 → ℝ) →L[ℝ] ℝ) : ℝ × (Fin 1 → ℝ) →ₗ[ℝ] ℝ)
  n := 1
  finiteDimensional _ := inferInstance
  finrank_eq q := by rw [ker_eq_span, finrank_span_singleton (kv_ne_zero q)]
  exists_frame _ := ⟨univ, isOpen_univ, mem_univ _, fun _ q => kv q,
    fun _ => ((continuous_const.prodMk (continuous_pi fun _ => continuous_f.neg))).continuousOn,
    fun q _ => ⟨fun _ => kv_mem q, linearIndependent_unique_iff.2 (kv_ne_zero q)⟩⟩

/-- The global frame `(1, −f(q))` of `Λ`. -/
def ε : Λ.Frame where
  U := univ
  isOpen := isOpen_univ
  e _ q := kv q
  continuousOn _ :=
    ((continuous_const.prodMk (continuous_pi fun _ => continuous_f.neg))).continuousOn
  mem q _ _ := kv_mem q
  linearIndependent q _ := by
    change LinearIndependent ℝ (fun _ : Fin 1 => kv q)
    exact linearIndependent_unique_iff.2 (kv_ne_zero q)

/-! ### The orientation of `DET` over the ball given by the chart -/

/-- On the ball, the chart section `S ↦ (γ^0_S)⁻¹ ω(S)` does not vanish. -/
theorem coordInv_one_ne_zero {S : FredholmOp ℝ ℝ} (hS : S ∈ chart0.baseSet) :
    chart0.coordInv S 1 ≠ 0 := by
  intro h
  have := chart0.coord_coordInv hS 1
  rw [h, map_zero] at this
  exact zero_ne_one this

/-- The chart section is continuous on the ball. -/
theorem continuousOn_coordInv_one :
    ContinuousOn (fun S : FredholmOp ℝ ℝ =>
      (⟨S, chart0.coordInv S 1⟩ : TotalSpace ℝ (DetFiber (E := ℝ) (F := ℝ)))) chart0.baseSet := by
  let e := (detPrebundle ℝ ℝ).trivializationOfMemPretrivializationAtlas ⟨chart0, rfl⟩
  exact e.continuousOn_symm_prodMk_left (v := 1)

/-- **The orientation `o` of `DET` over the ball**: the rays of the chart section. -/
def o : LineOrientation (DetOn C hC) :=
  ⟨fun S => rayOfNeZero ℝ (chart0.coordInv (fredholmIncl hC S) 1)
      (coordInv_one_ne_zero (S := fredholmIncl hC S) S.2), fun S₀ => by
    refine ⟨univ, Filter.univ_mem, fun S => chart0.coordInv (fredholmIncl hC S) 1, ?_,
      fun S _ => ⟨coordInv_one_ne_zero (S := fredholmIncl hC S) S.2, rfl⟩⟩
    rw [continuousOn_univ]
    refine (inducing_pullbackTotalSpaceEmbedding ℝ _ _).continuous_iff.2 ?_
    exact continuous_id.prodMk (continuousOn_coordInv_one.comp_continuous
      (fredholmIncl hC).continuous fun S => S.2)⟩

/-! ### The chart coordinate -/

/-- `ker(P S) = ℝ`, as `P = 0`. -/
theorem mem_ker_P (S : ℝ →L[ℝ] ℝ) (x : ℝ) :
    x ∈ LinearMap.ker ((chart0.P ∘L S : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) := by
  rw [LinearMap.mem_ker]
  rfl

/-- `dim ker(P S) = 1`. -/
theorem finrank_ker_P (S : ℝ →L[ℝ] ℝ) :
    finrank ℝ (LinearMap.ker ((chart0.P ∘L S : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ)) = 1 := by
  rw [(eq_top_iff.2 fun x _ => mem_ker_P S x :
    LinearMap.ker ((chart0.P ∘L S : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = ⊤), finrank_top,
    Module.finrank_self]

/-- `dim K = 1` for the chart kernel `K = ker(P T)`. -/
theorem finrank_K : finrank ℝ chart0.K = 1 := finrank_ker_P 0

/-- `R(P) = 0`. -/
theorem range_P : LinearMap.range ((chart0.P : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨x, rfl⟩
  exact (Submodule.mem_bot ℝ).2 rfl

/-- `dim F / R(P) = 1`. -/
theorem finrank_coker_P :
    finrank ℝ (ℝ ⧸ LinearMap.range ((chart0.P : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ)) = 1 := by
  rw [(Submodule.quotEquivOfEqBot _ range_P).finrank_eq, Module.finrank_self]

/-- `dim F / R(P S) = 1`. -/
theorem finrank_coker_PS (S : ℝ →L[ℝ] ℝ) :
    finrank ℝ (ℝ ⧸ LinearMap.range ((chart0.P ∘L S : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ)) = 1 := by
  exact (cokerCompEquiv (isGoodLeftProj_zero S : IsGoodLeftProj S chart0.P)).finrank_eq.trans
    finrank_coker_P

/-- The determinant, in the chart's kernel basis, of the vector `1`. -/
def D₁ : ℝ :=
  ((Module.finBasis ℝ chart0.K).reindex (finCongr finrank_K)).det fun _ => chart0.kerProj 1

/-- The determinant, in the chart's cokernel basis, of the class `[t]`. -/
def D₂ (t : ℝ) : ℝ :=
  ((Module.finBasis ℝ (ℝ ⧸ LinearMap.range ((chart0.P : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ))).reindex
    (finCongr finrank_coker_P)).det fun _ => Submodule.Quotient.mk t

/-- `D₂(t) = t D₂(1)`. -/
theorem D₂_eq (t : ℝ) : D₂ t = t * D₂ 1 := by
  simp only [D₂, Basis.det_apply, Matrix.det_unique, Basis.toMatrix_apply]
  have : (Submodule.Quotient.mk t : ℝ ⧸ LinearMap.range ((chart0.P : ℝ →L[ℝ] ℝ) :
      ℝ →ₗ[ℝ] ℝ)) = t • Submodule.Quotient.mk 1 := by
    rw [← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- **The chart coordinate through `γ^0_S`**: if `γ^0_S h = (v-wedge) ⊗ (w-wedge)*`, the
coordinate of `h` is `det(kerProj ∘ v) · det(w)⁻¹`. -/
theorem coord_eq_of_gamma {S : FredholmOp ℝ ℝ} (hS : S ∈ chart0.baseSet) (h : DetFiber S)
    {k l : ℕ} (v : Fin k → LinearMap.ker ((chart0.P ∘L S.1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ))
    (hk : k = finrank ℝ (LinearMap.ker ((chart0.P ∘L S.1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ)))
    (w : Fin l → ℝ ⧸ LinearMap.range ((chart0.P ∘L S.1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ))
    (hl : l = finrank ℝ (ℝ ⧸ LinearMap.range ((chart0.P ∘L S.1 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ)))
    (h1 : finrank ℝ chart0.K = k)
    (h2 : finrank ℝ (ℝ ⧸ LinearMap.range ((chart0.P : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ)) = l)
    (hγ : gammaProj S.2 (chart0.isGoodLeftProj_of_lt S.1 hS) h =
      wedge v hk ⊗ₜ dualVec (wedge w hl)) :
    chart0.coord S h =
      ((Module.finBasis ℝ chart0.K).reindex (finCongr h1)).det (fun i => chart0.kerProj (v i)) *
        (((Module.finBasis ℝ (ℝ ⧸ LinearMap.range ((chart0.P : ℝ →L[ℝ] ℝ) :
          ℝ →ₗ[ℝ] ℝ))).reindex (finCongr h2)).det (fun i => Submodule.quotEquivOfEq _ _
            (chart0.isGoodLeftProj_of_lt S.1 hS).range_comp (w i)))⁻¹ := by
  have hS' : ‖S.1 - chart0.T‖ < chart0.ε := hS
  have key := chart0.linDetEquivOfEq_wedge_tmul S.1 hS' rfl v hk w hl h1 h2
    (chart0.isGoodLeftProj_of_lt S.1 hS').range_comp
  rw [linDetEquivOfEq_self, LinearEquiv.refl_apply] at key
  have h1' := finrank_fredholmDet ((chart0.isGoodLeftProj_of_lt S.1 hS').isFredholm_comp S.2)
  rw [chart0.coord_apply hS', hγ, key, map_smul, dualVec_self h1' (chart0.frame_ne_zero S.1 hS'),
    smul_eq_mul, mul_one]

/-! ### The values at `q ≠ 0` -/

/-- `ker T_q = 0` for `q ≠ 0`. -/
theorem ker_T_ne {q : ℝ} (hq : q ≠ 0) : LinearMap.ker (T q : ℝ →ₗ[ℝ] ℝ) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, T_apply] at hx
  exact (Submodule.mem_bot ℝ).2 ((mul_eq_zero.1 hx).resolve_left (f_ne_zero hq))

/-- `dim ker T_q = 0` for `q ≠ 0`. -/
theorem finrank_ker_T_ne {q : ℝ} (hq : q ≠ 0) :
    finrank ℝ (LinearMap.ker (T q : ℝ →ₗ[ℝ] ℝ)) = 0 := by
  rw [ker_T_ne hq, finrank_bot]

/-- `R(T_q) = ℝ` for `q ≠ 0`. -/
theorem range_T_ne {q : ℝ} (hq : q ≠ 0) : LinearMap.range (T q : ℝ →ₗ[ℝ] ℝ) = ⊤ :=
  LinearMap.range_eq_top.2 fun y => ⟨y / f q, by
    rw [ContinuousLinearMap.coe_coe, T_apply, mul_div_cancel₀ _ (f_ne_zero hq)]⟩

/-- `dim coker T_q = 0` for `q ≠ 0`. -/
theorem finrank_coker_T_ne {q : ℝ} (hq : q ≠ 0) :
    finrank ℝ (ℝ ⧸ LinearMap.range (T q : ℝ →ₗ[ℝ] ℝ)) = 0 := by
  have : Subsingleton (ℝ ⧸ LinearMap.range (T q : ℝ →ₗ[ℝ] ℝ)) :=
    Submodule.Quotient.subsingleton_iff.2 (range_T_ne hq)
  exact finrank_zero_of_subsingleton

/-- The empty basis of `ker T_q = 0`. -/
def aNe {q : ℝ} (hq : q ≠ 0) : Basis (Fin 0) ℝ (LinearMap.ker (T q : ℝ →ₗ[ℝ] ℝ)) :=
  Module.finBasisOfFinrankEq ℝ _ (finrank_ker_T_ne hq)

/-- `1 ⊗ 1* ∈ det(T_q)`. -/
def xNe {q : ℝ} (hq : q ≠ 0) : fredholmDet (T q) :=
  wedge (aNe hq) (by rw [Module.finrank_eq_card_basis (aNe hq), Fintype.card_fin]) ⊗ₜ
    dualVec (wedge (stabClass (T q) φ ∘ (Fin.elim0 : Fin 0 → Fin 1 → ℝ))
      (finrank_coker_T_ne hq).symm)

/-- The chart coordinate of `1 ⊗ 1*` at `q ≠ 0` is `D₁ D₂(f(q))⁻¹`. -/
theorem coord_xNe {q : ℝ} (hq : q ≠ 0) :
    chart0.coord ⟨T q, hC _ (T_mem q)⟩ (xNe hq) = D₁ * (D₂ (f q))⁻¹ := by
  have hS : (⟨T q, hC _ (T_mem q)⟩ : FredholmOp ℝ ℝ) ∈ chart0.baseSet := T_mem q
  let b : Fin 1 → LinearMap.ker ((chart0.P ∘L T q : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) :=
    fun _ => ⟨1, mem_ker_P _ 1⟩
  have hb : LinearIndependent ℝ (Fin.append (projSeqJ (T q) chart0.P ∘ ⇑(aNe hq)) b) := by
    rw [Fin.append_left_nil _ _ rfl]
    exact (linearIndependent_unique_iff.2 fun h => one_ne_zero (congrArg Subtype.val h)).comp _
      (Fin.cast_injective _)
  have hγ := gammaProj_wedge_tmul (isFredholm_real (T q))
    (chart0.isGoodLeftProj_of_lt (T q) (T_mem q)) (aNe hq).linearIndependent
    (by rw [finrank_ker_T_ne hq]) (d := stabClass (T q) φ ∘ (Fin.elim0 : Fin 0 → Fin 1 → ℝ))
    linearIndependent_empty_type (finrank_coker_T_ne hq).symm hb (by rw [finrank_ker_P])
    (c := Fin.elim0) (fun i => i.elim0) (by rw [finrank_coker_PS])
  rw [coord_eq_of_gamma hS (xNe hq) _ _ _ _ finrank_K finrank_coker_P hγ,
    Fin.append_left_nil (⇑(projSeqJ (T q) chart0.P) ∘ ⇑(aNe hq)) b rfl, Fin.elim0_append]
  simp only [Function.comp_apply, b, cokerCompEquiv, LinearEquiv.apply_symm_apply]
  have hΦ : projSeqPhi (T q) chart0.P ⟨1, mem_ker_P _ 1⟩ = Submodule.Quotient.mk (f q) := by
    change Submodule.Quotient.mk (T q 1) = _
    rw [T_apply, mul_one]
  rw [hΦ]
  rfl

/-- `ker(T_q ⊕ φ)`. -/
abbrev KS (q : ℝ) : Submodule ℝ (ℝ × (Fin 1 → ℝ)) :=
  LinearMap.ker (((T q).coprod φ : ℝ × (Fin 1 → ℝ) →L[ℝ] ℝ) : ℝ × (Fin 1 → ℝ) →ₗ[ℝ] ℝ)

/-- The frame vector `(1, −f(q)) ∈ ker(T_q ⊕ φ)`. -/
def kvK (q : ℝ) : Fin 1 → KS q := fun _ => ⟨kv q, kv_mem q⟩

/-- `det(r) = −f(q)` for the second component `r = −f(q)` of the frame vector. -/
theorem det_kv (q : ℝ) {m : ℕ} (cbar : Fin m → Fin 1 → ℝ) (hm : m = 0) (hn : m + 1 = 1) :
    (Pi.basisFun ℝ (Fin 1)).det
      (Fin.append cbar (fun i => ((kvK q i : ℝ × (Fin 1 → ℝ)).2)) ∘ Fin.cast hn.symm) =
      -f q := by
  subst hm
  rw [Basis.det_apply, Matrix.det_unique]
  simp [Basis.toMatrix_apply, Fin.append, Fin.addCases, kvK, kv]

/-- `1*(1) = 1` for the empty wedge of `{0} = F / R(T_q ⊕ φ)`. -/
theorem stabOne_one (q : ℝ) :
    stabOne (hφ q) (emptyWedge _ (finrank_coker_of_surjective (hφ q))) = 1 := by
  have := finiteDimensional_coker_coprod (hφ q)
  exact dualVec_self finrank_maxPow ((wedge_ne_zero_iff _).2 linearIndependent_empty_type)

/-- A wedge `a ∧ b` with an empty `a` is the wedge `b`. -/
theorem wedge_append_nil {W : Type*} [AddCommGroup W] [Module ℝ W] {l : ℕ} (u : Fin 0 → W)
    (v : Fin l → W) (h : 0 + l = finrank ℝ W) :
    wedge (Fin.append u v) h = wedge v ((zero_add l).symm.trans h) := by
  rw [Fin.append_left_nil u v rfl]
  exact wedge_cast v _ (zero_add l)

set_option maxHeartbeats 400000 in
-- The final `rfl` compares two instance paths to `λ(ker(T_q ⊕ φ))`.
/-- The stabilization at `q ≠ 0` (Proposition 6.4.15 (preprint 6.15) with `a`, `c̄` empty and `b̄ = (1, −f(q))`):
`det(T_q ⊕ φ) ≅ λ(ker)` sends `ι_φ(1 ⊗ 1*)` to `(−f(q))⁻¹ (1, −f(q))`. -/
theorem stab_xNe {q : ℝ} (hq : q ≠ 0) :
    detEquivOfSurjective (hφ q) (stabIota (hC _ (T_mem q)) (hφ q) (xNe hq)) =
      ((-f q)⁻¹ : ℝ) • (wedge (kvK q) (Λ.finrank_eq q).symm : maxPow (KS q)) := by
  have hb : LinearIndependent ℝ (Fin.append (stabJ (T q) φ ∘ ⇑(aNe hq)) (kvK q)) := by
    rw [Fin.append_left_nil _ _ rfl]
    exact (linearIndependent_unique_iff.2 fun h => kv_ne_zero q (congrArg Subtype.val h)).comp _
      (Fin.cast_injective _)
  have h615 := proposition_6_4_15 (hC _ (T_mem q)) (hφ q) (aNe hq)
    (Fin.elim0 : Fin 0 → Fin 1 → ℝ) linearIndependent_empty_type (finrank_coker_T_ne hq).symm
    (kvK q) hb (by rw [zero_add]; exact (Λ.finrank_eq q).symm) (zero_add 1)
  unfold xNe
  rw [h615, det_kv q _ rfl, LinearEquiv.map_smul, detEquivOfSurjective_tmul, stabOne_one,
    one_smul]
  · rw [wedge_append_nil]
  · exact zero_add 1

/-- A wedge `a ∧ b` with an empty `b` is the wedge `a`. -/
theorem wedge_append_right_nil {W : Type*} [AddCommGroup W] [Module ℝ W] {m : ℕ} (u : Fin m → W)
    (v : Fin 0 → W) (h : m + 0 = finrank ℝ W) :
    wedge (Fin.append u v) h = wedge u ((add_zero m).symm.trans h) := by
  rw [Fin.append_right_nil u v rfl]
  exact wedge_cast u _ (add_zero m)

/-! ### The values at `q = 0` -/

/-- `ker T_0 = ℝ`. -/
theorem mem_ker_T_zero (x : ℝ) : x ∈ LinearMap.ker (T 0 : ℝ →ₗ[ℝ] ℝ) := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, T_apply, f_zero, zero_mul]

/-- `dim ker T_0 = 1`. -/
theorem finrank_ker_T_zero : finrank ℝ (LinearMap.ker (T 0 : ℝ →ₗ[ℝ] ℝ)) = 1 := by
  rw [(eq_top_iff.2 fun x _ => mem_ker_T_zero x : LinearMap.ker (T 0 : ℝ →ₗ[ℝ] ℝ) = ⊤),
    finrank_top, Module.finrank_self]

/-- `R(T_0) = 0`. -/
theorem range_T_zero : LinearMap.range (T 0 : ℝ →ₗ[ℝ] ℝ) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨x, rfl⟩
  rw [Submodule.mem_bot, ContinuousLinearMap.coe_coe, T_apply, f_zero, zero_mul]

/-- `dim coker T_0 = 1`. -/
theorem finrank_coker_T_zero : finrank ℝ (ℝ ⧸ LinearMap.range (T 0 : ℝ →ₗ[ℝ] ℝ)) = 1 := by
  rw [(Submodule.quotEquivOfEqBot _ range_T_zero).finrank_eq, Module.finrank_self]

/-- The vector `1 ∈ ker T_0 = ℝ`. -/
def one0 : LinearMap.ker (T 0 : ℝ →ₗ[ℝ] ℝ) := ⟨1, mem_ker_T_zero 1⟩

/-- The basis `(1)` of `ker T_0`. -/
def a0 : Basis (Fin 1) ℝ (LinearMap.ker (T 0 : ℝ →ₗ[ℝ] ℝ)) :=
  basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_unique_iff.2 fun h => one_ne_zero (congrArg Subtype.val h) :
      LinearIndependent ℝ fun _ : Fin 1 => one0)
    (by rw [Fintype.card_fin, finrank_ker_T_zero])

/-- The basis `a0` is `(1)`. -/
theorem a0_apply (i : Fin 1) : a0 i = one0 := by
  simp [a0]

/-- `c̄ = (1) ∈ ℝ¹`. -/
def cbar0 : Fin 1 → Fin 1 → ℝ := fun _ _ => 1

/-- `[1] ≠ 0` in `F / R(T_0)`. -/
theorem mk_one_ne_zero :
    (Submodule.Quotient.mk 1 : ℝ ⧸ LinearMap.range (T 0 : ℝ →ₗ[ℝ] ℝ)) ≠ 0 := by
  rw [Ne, Submodule.Quotient.mk_eq_zero, range_T_zero, Submodule.mem_bot]
  exact one_ne_zero

/-- The class `[φ(c̄)] = [1]` is a basis of `F / R(T_0)`. -/
theorem linearIndependent_d0 : LinearIndependent ℝ (stabClass (T 0) φ ∘ cbar0) :=
  linearIndependent_unique_iff.2 mk_one_ne_zero

/-- `1 ⊗ [1]* ∈ det(T_0)`. -/
def x0 : fredholmDet (T 0) :=
  wedge a0 (by rw [Module.finrank_eq_card_basis a0, Fintype.card_fin]) ⊗ₜ
    dualVec (wedge (stabClass (T 0) φ ∘ cbar0) finrank_coker_T_zero.symm)

/-- `det(c̄) = 1`. -/
theorem det_cbar0 (r : Fin 0 → Fin 1 → ℝ) (hn : 1 + 0 = 1) :
    (Pi.basisFun ℝ (Fin 1)).det (Fin.append cbar0 r ∘ Fin.cast hn.symm) = 1 := by
  rw [Basis.det_apply, Matrix.det_unique]
  simp [Basis.toMatrix_apply, Fin.append, Fin.addCases, cbar0]

/-- `j(a0) = (1, 0) = (1, −f(0))`. -/
theorem stabJ_a0 : ⇑(stabJ (T 0) φ) ∘ ⇑a0 = kvK 0 := by
  funext i
  refine Subtype.ext (Prod.ext ?_ (funext fun _ => ?_))
  · simp [a0_apply, one0, kvK, kv]
  · simp [kvK, kv, f_zero]

set_option maxHeartbeats 400000 in
-- The final `rfl` compares two instance paths to `λ(ker(T_0 ⊕ φ))`.
/-- The stabilization at `q = 0` (Proposition 6.4.15 (preprint 6.15) with `a = (1)`, `c̄ = (1)`, `b̄` empty). -/
theorem stab_x0 :
    detEquivOfSurjective (hφ 0) (stabIota (hC _ (T_mem 0)) (hφ 0) x0) =
      (1 : ℝ) • (wedge (kvK 0) (Λ.finrank_eq 0).symm : maxPow (KS 0)) := by
  have hb : LinearIndependent ℝ (Fin.append (stabJ (T 0) φ ∘ ⇑a0) (Fin.elim0 : Fin 0 → KS 0)) := by
    rw [Fin.append_right_nil _ _ rfl, stabJ_a0]
    exact (linearIndependent_unique_iff.2 fun h => kv_ne_zero 0 (congrArg Subtype.val h)).comp _
      (Fin.cast_injective _)
  have h615 := proposition_6_4_15 (hC _ (T_mem 0)) (hφ 0) a0 cbar0 linearIndependent_d0
    finrank_coker_T_zero.symm (Fin.elim0 : Fin 0 → KS 0) hb
    (by rw [add_zero]; exact (Λ.finrank_eq 0).symm) (add_zero 1)
  unfold x0
  rw [h615, det_cbar0, inv_one, one_smul, detEquivOfSurjective_tmul, stabOne_one, one_smul,
    wedge_append_right_nil, stabJ_a0]
  · exact (one_smul ℝ _).symm
  · exact add_zero 1

/-- `[1] ∈ F / R(P)` is sent by `π` to `[1] = φ(c̄) ∈ F / R(T_0)`. -/
theorem projSeqPi_mk_one (i : Fin 1) :
    projSeqPi (T := T 0) (chart0.isGoodLeftProj_of_lt (T 0) (T_mem 0)).isProj
      (Submodule.Quotient.mk 1) = (stabClass (T 0) φ ∘ cbar0) i := by
  change Submodule.Quotient.mk ((LinearMap.id - ((chart0.P : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) :
    ℝ →ₗ[ℝ] ℝ) 1) =
    Submodule.Quotient.mk (φ (cbar0 i))
  congr 1
  change 1 - (0 : ℝ) = 1
  rw [sub_zero]

/-- The chart coordinate of `1 ⊗ [1]*` at `q = 0` is `D₁ D₂(1)⁻¹`. -/
theorem coord_x0 : chart0.coord ⟨T 0, hC _ (T_mem 0)⟩ x0 = D₁ * (D₂ 1)⁻¹ := by
  have hS : (⟨T 0, hC _ (T_mem 0)⟩ : FredholmOp ℝ ℝ) ∈ chart0.baseSet := T_mem 0
  have hb : LinearIndependent ℝ (Fin.append (projSeqJ (T 0) chart0.P ∘ ⇑a0)
      (Fin.elim0 : Fin 0 → LinearMap.ker ((chart0.P ∘L T 0 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ))) := by
    rw [Fin.append_right_nil _ _ rfl]
    refine LinearIndependent.comp ?_ _ (Fin.cast_injective _)
    refine linearIndependent_unique_iff.2 fun h => ?_
    have := congrArg Subtype.val h
    rw [Function.comp_apply, a0_apply] at this
    exact one_ne_zero (α := ℝ) this
  have hγ := gammaProj_wedge_tmul (isFredholm_real (T 0))
    (chart0.isGoodLeftProj_of_lt (T 0) (T_mem 0)) a0.linearIndependent
    (by rw [Module.finrank_eq_card_basis a0, Fintype.card_fin]) linearIndependent_d0
    finrank_coker_T_zero.symm hb (by rw [finrank_ker_P])
    (c := fun _ => (Submodule.Quotient.mk 1 :
      ℝ ⧸ LinearMap.range ((chart0.P : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ))) projSeqPi_mk_one
    (by rw [finrank_coker_PS])
  rw [coord_eq_of_gamma hS x0 _ _ _ _ finrank_K finrank_coker_P hγ,
    Fin.append_right_nil (⇑(projSeqJ (T 0) chart0.P) ∘ ⇑a0) _ rfl, Fin.append_right_nil _ _ rfl]
  simp only [Function.comp_apply, cokerCompEquiv, LinearEquiv.apply_symm_apply, a0_apply]
  rfl

/-- On the ball, `(γ^0_S)⁻¹ ω(S) = coord(x)⁻¹ x` for every `x ∈ det(S)` with `coord(x) ≠ 0`. -/
theorem coordInv_one_eq {S : FredholmOp ℝ ℝ} (hS : S ∈ chart0.baseSet) (x : fredholmDet S.1)
    (hx : chart0.coord S x ≠ 0) :
    (chart0.coordInv S 1 : fredholmDet S.1) = (chart0.coord S x)⁻¹ • x := by
  have h1 : (1 : ℝ) = (chart0.coord S x)⁻¹ • chart0.coord S x := by
    rw [smul_eq_mul, inv_mul_cancel₀ hx]
  rw [h1, map_smul, chart0.coordInv_coord hS x]
  rfl

/-! ### The stabilized rays and the sign jump -/

/-- `Λ_q = ker(T_q ⊕ φ)`. -/
theorem hΛ (q : ℝ) : Λ.L q = LinearMap.ker (((T q).coprod φ : ℝ × (Fin 1 → ℝ) →L[ℝ] ℝ) :
    ℝ × (Fin 1 → ℝ) →ₗ[ℝ] ℝ) := rfl

/-- The rays `Φ(o(T_q))` of `λ(Λ_q)` of `isLineOrientation_stabRay`, for `φ_q = φ` and
`Λ_q = ker(T_q ⊕ φ)`. -/
def stabRays (q : ℝ) : Module.Ray ℝ (Λ.det q) :=
  stabRayEquiv (hC _ (T_mem q)) (hφ q) (LinearEquiv.ofEq _ _ (hΛ q).symm)
    (o ⟨T q, T_mem q⟩)

set_option maxHeartbeats 600000 in
-- The rewriting compares two instance paths to `det(T_q)` and to `λ(ker(T_q ⊕ φ))`.
/-- **The stabilized ray in the frame**: if `det(T_q ⊕ φ) ≅ λ(ker)` sends `ι_φ(x)` to
`s (1, −f(q))`, then `Φ(o(T_q))` is the ray of `(coord x)⁻¹ s · (1, −f(q))`. -/
theorem stabRays_eq {q : ℝ} (x : fredholmDet (T q)) {s : ℝ} (hs0 : s ≠ 0)
    (hs : detEquivOfSurjective (hφ q) (stabIota (hC _ (T_mem q)) (hφ q) x) =
      s • (wedge (kvK q) (Λ.finrank_eq q).symm : maxPow (KS q))) :
    ∃ h, stabRays q = rayOfNeZero ℝ
      (((chart0.coord ⟨T q, hC _ (T_mem q)⟩ x)⁻¹ * s) • ε.wedgeAt q) h := by
  have hS : (⟨T q, hC _ (T_mem q)⟩ : FredholmOp ℝ ℝ) ∈ chart0.baseSet := T_mem q
  have hw : (wedge (kvK q) (Λ.finrank_eq q).symm : maxPow (KS q)) ≠ 0 :=
    (wedge_ne_zero_iff _).2
      (linearIndependent_unique_iff.2 fun h => kv_ne_zero q (congrArg Subtype.val h))
  have hx : chart0.coord ⟨T q, hC _ (T_mem q)⟩ x ≠ 0 := by
    intro h0
    have hx0 : x = 0 := by
      have := chart0.coordInv_coord hS x
      rw [h0, map_zero] at this
      exact this.symm
    rw [hx0, LinearMap.map_zero, LinearEquiv.map_zero] at hs
    exact hw ((smul_eq_zero.1 hs.symm).resolve_left hs0)
  have hinv : (chart0.coordInv ⟨T q, hC _ (T_mem q)⟩ 1 : fredholmDet (T q)) =
      (chart0.coord ⟨T q, hC _ (T_mem q)⟩ x)⁻¹ • x :=
    coordInv_one_eq hS x hx
  have hvec : maxPowEquiv (LinearEquiv.ofEq _ _ (hΛ q).symm)
      (detEquivOfSurjective (hφ q) (stabIota (hC _ (T_mem q)) (hφ q)
        (chart0.coordInv ⟨T q, hC _ (T_mem q)⟩ 1))) =
      ((chart0.coord ⟨T q, hC _ (T_mem q)⟩ x)⁻¹ * s) • ε.wedgeAt q := by
    rw [hinv, LinearMap.map_smul, LinearEquiv.map_smul, hs, smul_smul]
    have hw' : maxPowEquiv (LinearEquiv.ofEq _ _ (hΛ q).symm)
        (wedge (kvK q) (Λ.finrank_eq q).symm) = ε.wedgeAt q := by
      refine (maxPowEquiv_wedge _ _ _).trans ?_
      rw [ε.wedgeAt_of_mem (mem_univ q)]
      rfl
    exact ((maxPowEquiv _).map_smul _ _).trans (congrArg _ hw')
  have hne : ((chart0.coord ⟨T q, hC _ (T_mem q)⟩ x)⁻¹ * s) • ε.wedgeAt q ≠ 0 := fun h0 => by
    have := congrArg (ε.coord q) h0
    rw [LinearMap.map_smul, ε.coord_wedgeAt (mem_univ q), smul_eq_mul, mul_one,
      LinearMap.map_zero] at this
    exact mul_ne_zero (inv_ne_zero hx) hs0 this
  obtain ⟨h', hr⟩ := stabRayEquiv_ray (hC _ (T_mem q)) (hφ q)
    (LinearEquiv.ofEq _ _ (hΛ q).symm)
    (chart0.coordInv ⟨T q, hC _ (T_mem q)⟩ 1) (coordInv_one_ne_zero hS)
  refine ⟨hne, (show stabRays q = _ from hr).trans ((ray_eq_iff _ _).2 ?_)⟩
  rw [hvec]
  exact SameRay.rfl

/-- **The sign in the frame**: if the ray of `σ(b)` is that of `c · (1, −f(b))`, then the frame
coordinate of `σ(b)` has the sign of `c`. -/
theorem sign_of_ray {σ : ∀ b, Λ.det b} {b c : ℝ} (hc : c • ε.wedgeAt b ≠ 0) (h : σ b ≠ 0)
    (heq : rayOfNeZero ℝ (σ b) h = rayOfNeZero ℝ (c • ε.wedgeAt b) hc) :
    0 < c * ε.coord b (σ b) := by
  have hsr := ((ray_eq_iff _ _).1 heq).map (ε.coord b)
  rw [LinearMap.map_smul, ε.coord_wedgeAt (mem_univ b), smul_eq_mul, mul_one] at hsr
  have hc0 : c ≠ 0 := fun h0 => hc (by rw [h0, zero_smul])
  have hl0 : ε.coord b (σ b) ≠ 0 := fun h0 =>
    h (by rw [← ε.coord_smul_wedgeAt (mem_univ b) (σ b), h0, zero_smul])
  rw [mul_comm]
  exact (sameRay_real_iff hl0 hc0).1 hsr

/-- **The rays `Φ(o(T_q))` are not an orientation of `λ(Λ)`**: in the frame `(1, −f(q))` their
sign at `q = 0` is opposite to their sign at every `q ≠ 0`. -/
theorem not_isLineOrientation_stabRays : ¬ IsLineOrientation Λ.det stabRays := by
  intro hor
  obtain ⟨U, hU, σ, hσc, hσ⟩ := hor 0
  set K : ℝ := (D₁ * (D₂ 1)⁻¹)⁻¹ with hK
  -- the sign at `0`
  have hpos0 : 0 < K * ε.coord 0 (σ 0) := by
    obtain ⟨h0, hr0⟩ := stabRays_eq x0 one_ne_zero stab_x0
    obtain ⟨hσ0, hσr⟩ := hσ 0 (mem_of_mem_nhds hU)
    have := sign_of_ray h0 hσ0 (hσr.symm.trans hr0)
    rwa [coord_x0, mul_one] at this
  -- the sign at `q ≠ 0`
  have hneg : ∀ q ∈ U, q ≠ 0 → K * ε.coord q (σ q) < 0 := by
    intro q hq hq0
    obtain ⟨h1, hr1⟩ := stabRays_eq (xNe hq0) (inv_ne_zero (neg_ne_zero.2 (f_ne_zero hq0)))
      (stab_xNe hq0)
    obtain ⟨hσ1, hσr⟩ := hσ q hq
    have := sign_of_ray h1 hσ1 (hσr.symm.trans hr1)
    rw [coord_xNe, D₂_eq] at this
    have hc : (D₁ * (f q * D₂ 1)⁻¹)⁻¹ * (-f q)⁻¹ = -K := by
      have ht := f_ne_zero hq0
      rw [hK]
      by_cases hD₁ : D₁ = 0
      · simp [hD₁]
      by_cases hD₂ : D₂ 1 = 0
      · simp [hD₂]
      field_simp
    rw [hc, neg_mul] at this
    linarith
  -- continuity at `0`
  have hcont : ContinuousAt (fun b => K * ε.coord b (σ b)) 0 :=
    (((Λ.continuousWithinAt_section_iff ε (mem_univ 0)).1
      (hσc 0 (mem_of_mem_nhds hU))).continuousAt hU).const_mul K
  have hev : ∀ᶠ b in 𝓝 (0 : ℝ), b ∈ U ∧ 0 < K * ε.coord b (σ b) :=
    (Filter.eventually_of_mem hU fun _ h => h).and (hcont.eventually (lt_mem_nhds hpos0))
  obtain ⟨b, ⟨hbU, hb⟩, hb0⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := {(0 : ℝ)}ᶜ))).exists
  exact lt_asymm hb (hneg b hbU hb0)

end StabCounterexample

/-- **Without the sign normalization the stabilized rays need not form an orientation**: there
are `C`, a continuous orientation `o` of `DET` over `C`, norm-continuous `T_q ∈ C` and `φ_q` with
`T_q ⊕ φ_q` onto (here `E = F = ℝ`, `k = 1`, `Q = ℝ`), such that the rays `q ↦ Φ(o(T_q))` of
`λ(ker(T_q ⊕ φ_q))`, with `Φ` as in formula (94), are not an orientation; the sign of
`Φ(o(T_q))` in a continuous frame jumps where `dim coker T_q` does. This is why
`isLineOrientation_stabRay` carries the sign `stabSign (T q) = (−1)^{dim coker T_q}`. -/
theorem not_isLineOrientation_stabRay_uncorrected :
    ∃ (C : Set (ℝ →L[ℝ] ℝ)) (hC : ∀ T ∈ C, T.IsFredholm) (o : LineOrientation (DetOn C hC))
      (T : ℝ → ℝ →L[ℝ] ℝ) (_ : Continuous T) (hTC : ∀ q, T q ∈ C)
      (φ : ℝ → (Fin 1 → ℝ) →L[ℝ] ℝ) (_ : Continuous φ)
      (hφ : ∀ q, Function.Surjective ((T q).coprod (φ q)))
      (Λ : SubspaceFamily ℝ (ℝ × (Fin 1 → ℝ)))
      (hΛ : ∀ q, Λ.L q = LinearMap.ker (((T q).coprod (φ q) : ℝ × (Fin 1 → ℝ) →L[ℝ] ℝ) :
        ℝ × (Fin 1 → ℝ) →ₗ[ℝ] ℝ)),
      ¬ IsLineOrientation Λ.det fun q =>
        stabRayEquiv (hC _ (hTC q)) (hφ q) (LinearEquiv.ofEq _ _ (hΛ q).symm)
          (o ⟨T q, hTC q⟩) :=
  ⟨StabCounterexample.C, StabCounterexample.hC, StabCounterexample.o, StabCounterexample.T,
    StabCounterexample.continuous_T, StabCounterexample.T_mem, fun _ => StabCounterexample.φ,
    continuous_const, StabCounterexample.hφ, StabCounterexample.Λ, StabCounterexample.hΛ,
    StabCounterexample.not_isLineOrientation_stabRays⟩

end Polyfold
