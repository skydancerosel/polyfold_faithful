import Polyfold.Chapter3.StrongBundleSections

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory I* (2014 preprint), Part I, §3.1,
**Theorem 3.1.13 (preprint 3.12)** (local compactness for sc-Fredholm germs) and **Corollary 3.1.15 (preprint 3.13)** for sections of
strong bundles over M-polyfolds: the passage from their local form (`theorem_3_1_13_local`, Theorem
3.40 of §3.5, in `LocalCompactness.lean`) through a strong bundle chart, the filler and the
conjugation to a basic germ.

# Local compactness of the solution set of an sc-Fredholm germ

## The text, paraphrased

(Theorem 3.1.13 (preprint 3.12)) Let `f` be an sc-smooth section of the tame strong bundle `P : Y → X` and `x₀` a
smooth point such that `(f, x₀)` is an sc-Fredholm germ with `f(x₀) = 0`.  Then there is a nested
sequence `O(0) ⊃ O(1) ⊃ …` of open neighbourhoods of `x₀` in `X₀` such that for every `i` the
`X₀`-closure of `{x ∈ O(i) | f(x) = 0}` is a compact subset of `X_i`.  "The result is an immediate
consequence of Theorem 3.40."  (Corollary 3.1.15 (preprint 3.13)) If moreover `f(x_k) = 0` and `x_k → x` in `X₀`,
then for every `m`, `x_k ∈ X_m` for `k` large and `x_k → x` in `X_m`.

## What is formalized

* `Polyfold.theorem_3_1_13_wholeChart`: for a section `f` with `(f, x₀)` an sc-Fredholm germ (Definition 3.1.11 (preprint 3.11))
  and `f(x₀) = 0`, nested open `O(i) ∋ x₀` such that `closure {x ∈ O(i) | f(x) = 0}` is the image
  of a compact subset of `X_i` (`PX.Level i`, with the level topology of §2.2) under the inclusion
  `X_i → X`.
* `Polyfold.corollary_3_1_15_wholeChart` (the limit is the base point `x₀` of the germ) and
  `Polyfold.corollary_3_1_15_section_wholeChart` (for an sc-Fredholm section, Definition 3.1.16 (preprint 3.14), and any limit
  `x` of zeros, which is then itself a zero and a smooth point): lifts `y_k ∈ X_m` of the `x_k`
  for `k` large converging in `X_m` to the lift of the limit.
* The passage from the local statement: `Polyfold.theorem_3_1_13_local_subset` (the local theorem
  for any subset of the solution set), `Polyfold.IsStrongBundleIso.snd_eq_zero_iff` (the fibre
  maps of a strong bundle isomorphism are injective), `IsStrongBundleMap.base_isScSmooth`,
  `IsStrongBundleMap.toBase_shiftFiber_snd`; `Polyfold.MPolyfold.levelChartSymm` and
  `continuousOn_levelChartSymm` (`φ⁻¹ : O_m → X_m` is continuous for the level topology, the
  chart of `X_m` of the paragraph after Definition 2.3.8 (preprint 2.14) for every `m`);
  `Polyfold.tendsto_of_isCompact_of_tendsto_map` (convergence in `X_m` from convergence in `X`
  inside a compact subset of `X_m`).

## What the text leaves implicit, and the choices made (the findings)

* **Hypotheses actually used.**  Of "`f` an sc-smooth section of the tame strong bundle" only
  `P ∘ f = id` is used (`IsSection`); the sc-smoothness of `f` enters through the filled version
  `g` of Definition 3.1.11 (preprint 3.11) (which is sc-smooth), tameness not at all.  Corollary 3.1.15 (preprint 3.13) for an
  arbitrary limit `x` needs the germ property at `x` (Findings, Chapter 3, item 15): this is
  `corollary_3_1_15_section_wholeChart`, for an sc-Fredholm section, where the limit of zeros is a zero (the
  principal part is continuous) and a smooth point (regularizing).
* **"An immediate consequence of Theorem 3.40"** hides: (i) the identification of the zeros of
  `f` near `x₀` with those of the basic germ plus sc⁺-germ `h + t`, `t = Ψ_*(s)`, through
  `φ`, the filler (conditions (1) and (2) of Definition 3.1.4 (preprint 3.4)) and the fibre maps of `Ψ`
  (linear bijections: `g(u) = 0 ⟺ (Ψ(u, g(u)))₂ = 0`); (ii) the push-forward `t` is an sc⁺-germ
  because `Ψ[1]` is sc-smooth (Definition 2.6.1 (preprint 2.47)) and `s(0) = g(0) = f̂(0) = 0`; (iii) the closure
  of the solution set in `E₀` must stay inside the chart and inside the region where (i) holds,
  which is arranged by intersecting the `O(i)` of Theorem 3.5.1 (preprint 3.40) with a small ball (the closure
  of a subset of the solution set is compact, hence closed, so the compactness survives);
  (iv) the `E₀`-closure of the solutions is a set of solutions of `g` in `U`, hence lies in `O`
  by condition (2) of the filler; (v) `X₀`-closures of subsets of a chart domain can leave the
  domain, so the compactness in `E₀` is used first to see that the closure stays in `V`;
  (vi) the transport to `X_i` needs the inverse chart `O_i → X_i` to be continuous for the level
  topology, which is the compatibility of the charts on level `i` (sc⁰ transition maps).
* **Corollary 3.1.15 (preprint 3.13) in `X_m`**: `X_m` is not known to be first countable here (its metrizability
  is Theorem 2.3.10 (preprint 2.16), formalized in `Metrizable.lean` for `X` but not used), so the convergence of
  the lifts is proved with cluster points in the compact set, not with subsequences.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E F E' F' : ScBanach}

/-! ### Strong bundle maps and isomorphisms: base and fibre maps -/

namespace IsStrongBundleMap

variable {U : Set (E 0)} {U' : Set (E' 0)} {Ψ : E 0 × F 0 → E' 0 × F' 0}
  (hΨ : IsStrongBundleMap U U' Ψ)
include hΨ

/-- `Ψ(u, k) = (ψ(u), Γ(u, k))`. -/
lemma apply_eq {u : E 0} (hu : u ∈ U) (k : F 0) : Ψ (u, k) = (base Ψ u, (Ψ (u, k)).2) :=
  Prod.ext (hΨ.fst_independent u hu k 0) rfl

lemma base_mem {u : E 0} (hu : u ∈ U) : base Ψ u ∈ U' := (hΨ.mapsTo ⟨hu, mem_univ _⟩).1

lemma snd_zero {u : E 0} (hu : u ∈ U) : (Ψ (u, 0)).2 = 0 := (hΨ.fiber_linear u hu).map_zero

lemma snd_sub {u : E 0} (hu : u ∈ U) (k k' : F 0) :
    (Ψ (u, k - k')).2 = (Ψ (u, k)).2 - (Ψ (u, k')).2 :=
  (hΨ.fiber_linear u hu).map_sub k k'

/-- The base map `ψ` of a strong bundle map on `U ◁ F` is sc-smooth on `U` (it is
`pr₁ ∘ Ψ ∘ (u ↦ (u, 0))`). -/
theorem base_isScSmooth {C : Set (E 0)} (hU : IsRelOpenInQuadrant E C U) :
    IsScSmooth U (base Ψ) := by
  have hUF := (hU.prod_univ F).isScDomain
  have h1 : IsScSmooth (E := E) (F := E'.prod F') U (Ψ ∘ E.prodInlOp F 0) :=
    IsScSmooth.comp hU.isScDomain hUF hΨ.isScSmooth_zero
      ((E.prodInlOp F).isScSmooth hU.isScDomain) fun u hu =>
        show (u, (0 : F 0)) ∈ U ×ˢ univ from ⟨hu, mem_univ _⟩
  exact (IsScSmooth.comp hU.isScDomain (isScDomain_univ _)
    ((E'.prodFstOp F').isScSmooth (isScDomain_univ _)) h1 (mapsTo_univ _ _)).congr
    hU.isScDomain fun _ _ => rfl

/-- `ι(Ψ[1](u, k₁))₂ = (Ψ(u, ι k₁))₂`: the fibre component of `Ψ[1]` lifts that of `Ψ` to `F'₁`. -/
lemma toBase_shiftFiber_snd {p : (E.prod F.shift) 0} (hp : p.1 ∈ U) :
    F'.toBase 1 (shiftFiber Ψ p).2 = (Ψ (p.1, F.toBase 1 p.2)).2 :=
  Function.invFun_eq (hΨ.preserves_filtration 0 1 (by norm_num) p.1 hp ⟨p.1, rfl⟩
    (F.toBase 1 p.2) ⟨p.2, rfl⟩).2

end IsStrongBundleMap

namespace IsStrongBundleIso

variable {U : Set (E 0)} {U' : Set (E' 0)} {Ψ : E 0 × F 0 → E' 0 × F' 0}
  {Ψ' : E' 0 × F' 0 → E 0 × F 0} (hΨ : IsStrongBundleIso U U' Ψ Ψ')
include hΨ

/-- `ψ' ∘ ψ = id` on `U`. -/
lemma base_base {u : E 0} (hu : u ∈ U) :
    IsStrongBundleMap.base Ψ' (IsStrongBundleMap.base Ψ u) = u := by
  have h1 : (Ψ' (IsStrongBundleMap.base Ψ u, (Ψ (u, 0)).2)).1 = u := by
    have := congrArg Prod.fst (hΨ.left_inv (u, 0) ⟨hu, mem_univ _⟩)
    rw [hΨ.toFun.apply_eq hu 0] at this
    exact this
  calc IsStrongBundleMap.base Ψ' (IsStrongBundleMap.base Ψ u)
      = (Ψ' (IsStrongBundleMap.base Ψ u, (Ψ (u, 0)).2)).1 :=
        hΨ.invFun.fst_independent _ (hΨ.toFun.base_mem hu) 0 _
    _ = u := h1

/-- `ψ ∘ ψ' = id` on `U'`. -/
lemma base_base' {u' : E' 0} (hu' : u' ∈ U') :
    IsStrongBundleMap.base Ψ (IsStrongBundleMap.base Ψ' u') = u' := by
  have h1 : (Ψ (IsStrongBundleMap.base Ψ' u', (Ψ' (u', 0)).2)).1 = u' := by
    have := congrArg Prod.fst (hΨ.right_inv (u', 0) ⟨hu', mem_univ _⟩)
    rw [hΨ.invFun.apply_eq hu' 0] at this
    exact this
  calc IsStrongBundleMap.base Ψ (IsStrongBundleMap.base Ψ' u')
      = (Ψ (IsStrongBundleMap.base Ψ' u', (Ψ' (u', 0)).2)).1 :=
        hΨ.toFun.fst_independent _ (hΨ.invFun.base_mem hu') 0 _
    _ = u' := h1

/-- The fibre maps `k ↦ (Ψ(u, k))₂` of a strong bundle isomorphism are injective. -/
lemma snd_eq_zero_iff {u : E 0} (hu : u ∈ U) {k : F 0} : (Ψ (u, k)).2 = 0 ↔ k = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h]; exact hΨ.toFun.snd_zero hu⟩
  have h1 : Ψ (u, k) = Ψ (u, 0) := by
    rw [hΨ.toFun.apply_eq hu k, hΨ.toFun.apply_eq hu 0, h, hΨ.toFun.snd_zero hu]
  have h2 := congrArg Prod.snd (hΨ.left_inv (u, k) ⟨hu, mem_univ _⟩)
  rw [h1, hΨ.left_inv (u, 0) ⟨hu, mem_univ _⟩] at h2
  exact h2.symm

/-- `ψ'(0) = 0` when `ψ(0) = 0`. -/
lemma base_zero' (h0U : (0 : E 0) ∈ U) (h0 : IsStrongBundleMap.base Ψ 0 = 0) :
    IsStrongBundleMap.base Ψ' 0 = 0 := by
  have := hΨ.base_base h0U
  rwa [h0] at this

end IsStrongBundleIso

/-! ### Two topological lemmas -/

/-- A limit of points where `g = b`, lying in the domain of continuity of `g`, has `g u = b`. -/
theorem eq_of_mem_closure_of_continuousOn {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [T2Space β] {g : α → β} {U A : Set α} (hg : ContinuousOn g U) (hA : A ⊆ U) {b : β}
    (hA0 : ∀ a ∈ A, g a = b) {u : α} (hu : u ∈ U) (hcl : u ∈ closure A) : g u = b := by
  have h1 : Tendsto g (𝓝[A] u) (𝓝 (g u)) := (hg u hu).mono_left (nhdsWithin_mono _ hA)
  have h2 : Tendsto g (𝓝[A] u) (𝓝 b) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun a ha => (hA0 a ha).symm)
  have : NeBot (𝓝[A] u) := mem_closure_iff_nhdsWithin_neBot.1 hcl
  exact tendsto_nhds_unique h1 h2

/-- **Convergence inside a compact set from convergence of the images**: if `y_n ∈ K` eventually,
`K` compact, `v` continuous and injective, and `v(y_n) → v(y₀)`, then `y_n → y₀`.  (Used for the
level topology of `X_m`, which is not known to be first countable.) -/
theorem tendsto_of_isCompact_of_tendsto_map {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [T2Space β] {K : Set α} (hK : IsCompact K) {v : α → β} (hv : Continuous v) (hvi : Injective v)
    {y : ℕ → α} (hy : ∀ᶠ n in atTop, y n ∈ K) {y₀ : α}
    (hlim : Tendsto (fun n => v (y n)) atTop (𝓝 (v y₀))) : Tendsto y atTop (𝓝 y₀) := by
  by_contra hcon
  have : ∃ N, IsOpen N ∧ y₀ ∈ N ∧ ¬ ∀ᶠ n in atTop, y n ∈ N := by
    by_contra h'
    refine hcon (tendsto_nhds.2 fun N hN hyN => ?_)
    by_contra h''
    exact h' ⟨N, hN, hyN, h''⟩
  obtain ⟨N, hNo, hy₀N, hfreq⟩ := this
  rw [Filter.not_eventually] at hfreq
  have hfreq' : ∃ᶠ n in atTop, y n ∈ K ∩ Nᶜ :=
    (hfreq.and_eventually hy).mono fun n h => ⟨h.2, h.1⟩
  have hfreq'' : ∃ᶠ a in map y atTop, a ∈ K ∩ Nᶜ := Filter.frequently_map.2 hfreq'
  obtain ⟨a, ⟨-, haN⟩, hcl⟩ :=
    (hK.inter_right hNo.isClosed_compl).exists_clusterPt_of_frequently hfreq''
  have h1 : ClusterPt (v a) (map (fun n => v (y n)) atTop) :=
    hcl.map hv.continuousAt (le_of_eq (Filter.map_map))
  have h2 : v a = v y₀ := eq_of_nhds_neBot (h1.neBot.mono (inf_le_inf_left _ hlim))
  exact haN (hvi h2 ▸ hy₀N)

/-! ### The inverse chart `O_m → X_m` is continuous for the level topology -/

universe u v

namespace MPolyfold

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (P : MPolyfold X)
  {φ : MChart X}

open scoped Classical in
/-- The inverse `O_m → X_m` of the level-`m` chart, `z ↦ φ⁻¹(ι_m z)`, with the junk value `x₀`
off `O_m` (the paragraph after Definition 2.3.8 (preprint 2.14): "`φ : V_m → O_m` is a homeomorphism"). -/
def levelChartSymm (hφ : P.IsChart φ) (m : ℕ) (x₀ : P.Level m) (z : φ.model.E m) : P.Level m :=
  if h : φ.model.E.toBase m z ∈ φ.model.O then
    P.levelMk m (φ.symm (φ.model.E.toBase m z))
      ((P.mem_levelSet_iff hφ (φ.symm_mapsTo h)).2 (by rw [φ.apply_symm_apply h]; exact ⟨z, rfl⟩))
  else x₀

lemma levelVal_levelChartSymm (hφ : P.IsChart φ) (m : ℕ) (x₀ : P.Level m) {z : φ.model.E m}
    (hz : φ.model.E.toBase m z ∈ φ.model.O) :
    P.levelVal m (P.levelChartSymm hφ m x₀ z) = φ.symm (φ.model.E.toBase m z) := by
  rw [levelChartSymm, dif_pos hz]; rfl

/-- `φ⁻¹ : O_m → X_m` is continuous for the level topology of `X_m` (the transition maps to the
other charts are sc⁰, hence continuous on level `m`). -/
theorem continuousOn_levelChartSymm (hφ : P.IsChart φ) (m : ℕ) (x₀ : P.Level m) :
    ContinuousOn (P.levelChartSymm hφ m x₀) (φ.model.E.lvlSet φ.model.O m) := by
  rw [continuousOn_iff_continuous_domRestrict]
  refine continuous_generateFrom_iff.2 ?_
  rintro _ ⟨ψ, hψ, W, hW, rfl⟩
  obtain ⟨W₀, hW₀, hW₀eq⟩ := φ.exists_isOpen_image_eq (s := φ.source ∩ ψ.source) inter_subset_left
    (φ.isOpen_source.inter ψ.isOpen_source)
  have hcont : ContinuousOn (levelMap (φ.transition ψ) m) (φ.model.E.lvlSet (φ.overlap ψ) m) :=
    (hφ.compatible hψ (P := P)).1.continuousOn_levelMap (φ.isScRetract_overlap ψ) m
  obtain ⟨u, hu, hueq⟩ := (continuousOn_iff'.1 hcont) W hW
  have hov : φ.overlap ψ = φ.model.O ∩ W₀ := hW₀eq
  refine isOpen_induced_iff.2 ⟨φ.model.E.lvlSet W₀ m ∩ u,
    (φ.model.E.isOpen_lvlSet hW₀ m).inter hu, ?_⟩
  ext ⟨z, hz⟩
  rw [iff_comm]
  have hzO : φ.model.E.toBase m z ∈ φ.model.O := hz
  change (P.levelVal m (P.levelChartSymm hφ m x₀ z) ∈ ψ.source ∧
    levelLift ψ m (P.levelVal m (P.levelChartSymm hφ m x₀ z)) ∈ W) ↔ _
  rw [P.levelVal_levelChartSymm hφ m x₀ hzO]
  have hz1 : φ.model.E.toBase m z ∈ φ.overlap ψ ↔ φ.symm (φ.model.E.toBase m z) ∈ ψ.source := by
    constructor
    · rintro ⟨y, hy, hyeq⟩
      rw [← hyeq, φ.symm_apply_apply hy.1]; exact hy.2
    · intro h
      exact ⟨_, ⟨φ.symm_mapsTo hzO, h⟩, φ.apply_symm_apply hzO⟩
  have hz2 : levelLift ψ m (φ.symm (φ.model.E.toBase m z)) = levelMap (φ.transition ψ) m z := rfl
  rw [hz2]
  constructor
  · rintro ⟨h1, h2⟩
    have hzov : z ∈ φ.model.E.lvlSet (φ.overlap ψ) m := hz1.2 h1
    have : z ∈ levelMap (φ.transition ψ) m ⁻¹' W ∩ φ.model.E.lvlSet (φ.overlap ψ) m := ⟨h2, hzov⟩
    rw [hueq] at this
    refine ⟨?_, this.1⟩
    have h3 : φ.model.E.toBase m z ∈ φ.model.O ∩ W₀ := hov ▸ hzov
    exact h3.2
  · rintro ⟨h1, h2⟩
    have hzov : z ∈ φ.model.E.lvlSet (φ.overlap ψ) m := by
      change φ.model.E.toBase m z ∈ φ.overlap ψ
      rw [hov]; exact ⟨hzO, h1⟩
    refine ⟨hz1.1 hzov, ?_⟩
    have : z ∈ u ∩ φ.model.E.lvlSet (φ.overlap ψ) m := ⟨h2, hzov⟩
    rw [← hueq] at this
    exact this.1

end MPolyfold

/-! ### Theorem 3.1.13 (preprint 3.12) in its local form, for a subset of the solution set -/

/-- **Theorem 3.1.13 (preprint 3.12) in its local form, for any subset `S` of the solution set** of `h + t = 0`
(`h` a basic germ, `t` an sc⁺-germ with `t(0) = 0`): nested open `O(i) ∋ 0` in `E₀` with
`closure(S ∩ O(i)) = ι_i(K_i)`, `K_i ⊆ E_i` compact (Theorem 3.5.1 (preprint 3.40) with the compactness
argument, `theorem_3_5_1_compactness`). -/
theorem theorem_3_1_13_local_subset {Pn : Type} [NormedAddCommGroup Pn] [NormedSpace ℝ Pn]
    [FiniteDimensional ℝ Pn] {W : ScBanach} {Ct : Set Pn}
    {G : ScNbhdGerm (ScBanach.paramProd Pn W) (Ct ×ˢ univ)} {Q : Type} [NormedAddCommGroup Q]
    [NormedSpace ℝ Q] [FiniteDimensional ℝ Q] {f : Pn × W 0 → Q × W 0} {Bc : Pn × W 0 → W 0}
    (hf : IsBasicGerm Ct G f Bc) (hCt : IsClosed Ct) {s : Pn × W 0 → Q × W 1}
    (hs : IsSc0Germ (E := ScBanach.paramProd Pn W) (F := (ScBanach.paramProd Q W).shift) G s)
    (hs0 : s 0 = 0) {S : Set ((ScBanach.paramProd Pn W) 0)}
    (hS : S ⊆ {x | x ∈ G.U 0 ∧ f x + (ScBanach.paramProd Q W).toBase 1 (s x) = 0}) :
    ∃ O : ℕ → Set ((ScBanach.paramProd Pn W) 0), (∀ i, IsOpen (O i)) ∧
      (∀ i, (0 : Pn × W 0) ∈ O i) ∧ (∀ i, O (i + 1) ⊆ O i) ∧
      ∀ i, ∃ K : Set ((ScBanach.paramProd Pn W) i), IsCompact K ∧
        closure (S ∩ O i) = (ScBanach.paramProd Pn W).toBase i '' K := by
  have hsW : IsSc0Germ (E := ScBanach.paramProd Pn W) (F := W.shift) G (fun x => (s x).2) :=
    (ScBanach.sndOp (ScBanach.const Q) W.shift).isSc0Germ _ |>.comp hs (G.mapsToGerm_full _)
  have hsW0 : (s 0).2 = 0 := by rw [hs0]; rfl
  refine theorem_3_5_1_compactness hf.contraction hCt hsW hsW0 fun x hx => ⟨(hS hx).1, ?_⟩
  have h2 := congrArg Prod.snd (hS hx).2
  rw [ScBanach.paramProd_toBase] at h2
  change (f x).2 + W.toBase 1 (s x).2 = 0 at h2
  rw [hf.snd_eq x (hS hx).1] at h2
  have : x.2 - Bc x + W.toBase 1 (s x).2 = 0 := h2
  rw [sub_add_eq_add_sub, sub_eq_zero] at this
  exact eq_sub_of_add_eq this

/-! ### Theorem 3.1.13 (preprint 3.12) and Corollary 3.1.15 (preprint 3.13) for sections of strong bundles -/

section Bundle

variable {X : Type u} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type v} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle PX P}
  {f : X → Y}

/-- **Theorem 3.1.13 (preprint 3.12) (local compactness for sc-Fredholm germs)**: let `f` be a section of the
strong bundle `P : Y → X` and `x₀` a smooth point with `(f, x₀)` an sc-Fredholm germ and
`f(x₀) = 0`.  Then there are nested open neighbourhoods `O(0) ⊃ O(1) ⊃ …` of `x₀` in `X` such
that for every `i` the closure in `X` of `{x ∈ O(i) | f(x) = 0}` is the image of a compact subset
of `X_i` (with the level topology) under the inclusion `X_i → X`.  Only `P ∘ f = id` is used of
"`f` an sc-smooth section of the tame strong bundle". -/
theorem theorem_3_1_13_wholeChart (hf : IsSection P f) {x₀ : X} (hg : B.IsScFredholmGermWholeChart f x₀)
    (hx₀ : IsZeroAt P f x₀) :
    ∃ O : ℕ → Set X, (∀ i, IsOpen (O i)) ∧ (∀ i, x₀ ∈ O i) ∧ (∀ i, O (i + 1) ⊆ O i) ∧
      ∀ i, ∃ K : Set (PX.Level i), IsCompact K ∧
        PX.levelVal i '' K = closure {x ∈ O i | IsZeroAt P f x} := by
  obtain ⟨hxs, c, hc, hxV, h0, h0U, g, t₀, hfill, ht₀, ht₀0, hconj⟩ := hg
  obtain ⟨Pn, Q, i1, i2, i3, i4, i5, i6, W, Ct, U', Ψ, Ψ', G, h, Bc, hCt, hU', hΨ, hψ0, hG, hh,
    hev⟩ := hconj
  -- notation
  set ψ := IsStrongBundleMap.base Ψ with hψdef
  set ψ' := IsStrongBundleMap.base Ψ' with hψ'def
  have hψψ' : ∀ u ∈ c.U, ψ' (ψ u) = u := fun u hu => hΨ.base_base hu
  have hψ'ψ : ∀ u' ∈ U', ψ (ψ' u') = u' := fun u' hu' => hΨ.base_base' hu'
  set fb := c.principal f with hfbdef
  set sb : c.φ.model.E 0 → c.F 0 := fun u => c.F.toBase 1 (t₀ u) with hsbdef
  have hU := c.relOpen
  have hOU : c.φ.model.O ⊆ c.U := fun z hz => by
    rw [← c.r_image] at hz
    obtain ⟨v, hv, rfl⟩ := hz
    exact StrongRetr.r_mem c.isRetraction hv
  have h0O : (0 : c.φ.model.E 0) ∈ c.φ.model.O := h0 ▸ c.φ.mapsTo_model x₀ hxV
  have hC'closed : IsClosed (Ct ×ˢ (univ : Set (W 0))) := hU'.isPartialQuadrant.isClosed
  have hU'C : U' ⊆ Ct ×ˢ univ := by
    obtain ⟨Uo, -, rfl⟩ := hU'.relOpen; exact inter_subset_right
  have h0U' : (0 : (ScBanach.paramProd Pn W) 0) ∈ U' := hψ0 ▸ hΨ.toFun.base_mem h0U
  have hψ'0 : ψ' 0 = 0 := hΨ.base_zero' h0U hψ0
  -- `ψ'` is sc-smooth, hence sc⁰ and continuous on `U'`
  have hψ'sc : IsScSmooth U' ψ' := hΨ.invFun.base_isScSmooth hU'
  have hψ'sc0 : IsSc0 _ _ U' ψ' := hψ'sc.isSc1.isSc0
  have hψ'cont : ContinuousOn ψ' U' := hψ'sc0.continuousOn_base
  have hψcont : ContinuousOn ψ c.U := (hΨ.toFun.base_isScSmooth hU).isSc1.isSc0.continuousOn_base
  -- the neighbourhood `N₁` of `0` where the identities of the filler and the conjugation hold
  have hN₀ : ∀ᶠ u in 𝓝 (0 : c.φ.model.E 0), (u ∈ c.φ.model.O → fb u = g u) ∧
      (u ∈ c.U → g u = StrongRetr.ρ c.R (StrongRetr.r c.R u) (g u) → u ∈ c.φ.model.O) ∧
      (u ∈ c.U → (Ψ (u, g u - sb u)).2 = h (ψ u)) := by
    have h1 := hfill.filler.eq_on
    have h2 := hfill.filler.mem_of_fixed
    rw [c.r_image] at h1 h2
    refine (h1.and (h2.and hev)).mono fun u hu => ⟨hu.1, hu.2.1, fun huU => ?_⟩
    exact hu.2.2 huU
  obtain ⟨N₁, hN₁sub, hN₁open, h0N₁⟩ := mem_nhds_iff.1 hN₀
  have hN₁ : ∀ u ∈ N₁, (u ∈ c.φ.model.O → fb u = g u) ∧
      (u ∈ c.U → g u = StrongRetr.ρ c.R (StrongRetr.r c.R u) (g u) → u ∈ c.φ.model.O) ∧
      (u ∈ c.U → (Ψ (u, g u - sb u)).2 = h (ψ u)) := fun u hu => hN₁sub hu
  -- zeros of `g` in `U ∩ N₁` lie in `O`
  have hgO : ∀ u ∈ c.U, u ∈ N₁ → g u = 0 → u ∈ c.φ.model.O := fun u hu huN hgu =>
    (hN₁ u huN).2.1 hu (by
      rw [hgu]
      exact ((StrongRetr.ρ_isLinear c.isRetraction (StrongRetr.r_mem c.isRetraction hu)).map_zero).symm)
  -- `f̂(0) = g(0) = 0`, `t₀(0) = 0`
  have hfb0 : fb 0 = 0 := by
    have := (c.isZeroAt_iff hf hxV).1 hx₀
    rwa [h0] at this
  have hg0 : g 0 = 0 := by rw [← (hN₁ 0 h0N₁).1 h0O, hfb0]
  have ht00 : t₀ 0 = 0 := by
    apply c.F.toBase_injective 1
    rw [ht₀0, hg0, map_zero]
  -- the push-forward sc⁺-germ `t = Ψ[1]_*(t₀)` on `E'`
  set t : (ScBanach.paramProd Pn W) 0 → (ScBanach.paramProd Q W).shift 0 :=
    fun u' => (shiftFiber Ψ (ψ' u', t₀ (ψ' u'))).2 with htdef
  have htsc : IsScSmooth (E := ScBanach.paramProd Pn W) (F := (ScBanach.paramProd Q W).shift) U' t := by
    have hpair : IsScSmooth (E := ScBanach.paramProd Pn W) (F := c.φ.model.E.prod c.F.shift) U'
        (scPair (F := c.φ.model.E) (G := c.F.shift) ψ' (fun u' => t₀ (ψ' u'))) := by
      refine hψ'sc.scPair hU'.isScDomain ?_
      exact IsScSmooth.comp hU'.isScDomain hU.isScDomain ht₀ hψ'sc fun u' hu' =>
        hΨ.invFun.base_mem hu'
    have hUF := (hU.prod_univ c.F.shift).isScDomain
    have hmaps : MapsTo (scPair (F := c.φ.model.E) (G := c.F.shift) ψ' (fun u' => t₀ (ψ' u'))) U'
        (c.U ×ˢ univ) := fun u' hu' =>
      ⟨hΨ.invFun.base_mem hu', mem_univ _⟩
    have := IsScSmooth.comp hU'.isScDomain hUF hΨ.toFun.isScSmooth_one hpair hmaps
    exact (this.snd hU'.isScDomain).congr hU'.isScDomain fun _ _ => rfl
  have hGsub : ∀ m, G.U m ⊆ (ScBanach.paramProd Pn W).lvlSet U' m := fun m z hz =>
    hG (G.toBase_mem hz)
  have ht : IsSc0Germ (E := ScBanach.paramProd Pn W) (F := (ScBanach.paramProd Q W).shift) G t :=
    IsSc0Germ.mono (htsc.isScSmoothGerm (hU'.isPartialQuadrant.isQuadrantLike) hU'.relOpen h0U' 0)
      hGsub
  have ht0 : t 0 = 0 := by
    simp only [htdef, hψ'0, ht00]
    unfold shiftFiber
    simp only [map_zero]
    rw [hΨ.toFun.snd_zero h0U]
    have := Function.leftInverse_invFun ((ScBanach.paramProd Q W).toBase_injective 1) 0
    rw [map_zero] at this
    exact this
  -- the key identity: for `u ∈ U ∩ N₁`, `h(ψ u) + ι t(ψ u) = 0 ⟺ g(u) = 0`
  have hkey : ∀ u ∈ c.U, u ∈ N₁ →
      (h (ψ u) + (ScBanach.paramProd Q W).toBase 1 (t (ψ u)) = 0 ↔ g u = 0) := by
    intro u hu huN
    have e1 : t (ψ u) = (shiftFiber Ψ (u, t₀ u)).2 := by
      simp only [htdef]; rw [hψψ' u hu]
    have e2 : (ScBanach.paramProd Q W).toBase 1 (shiftFiber Ψ (u, t₀ u)).2 = (Ψ (u, sb u)).2 :=
      hΨ.toFun.toBase_shiftFiber_snd (p := (u, t₀ u)) hu
    have e3 : h (ψ u) = (Ψ (u, g u - sb u)).2 := ((hN₁ u huN).2.2 hu).symm
    rw [e1, e2, e3, hΨ.toFun.snd_sub hu, sub_add_cancel]
    exact hΨ.snd_eq_zero_iff hu
  -- a ball in `E'₀` whose closed version lies in `U'` and is mapped by `ψ'` into `N₁`
  have hW' : ∀ᶠ u' in 𝓝 (0 : (ScBanach.paramProd Pn W) 0), u' ∈ U' → ψ' u' ∈ N₁ := by
    have h1 : Tendsto ψ' (𝓝[U'] 0) (𝓝 0) := by
      have := hψ'cont 0 h0U'
      rwa [ContinuousWithinAt, hψ'0] at this
    exact eventually_nhdsWithin_iff.1 (h1 (hN₁open.mem_nhds h0N₁))
  obtain ⟨W', hW'sub, hW'open, h0W'⟩ := mem_nhds_iff.1 hW'
  obtain ⟨Uo, hUo, hU'eq⟩ := hU'.relOpen
  obtain ⟨ρ', hρ', hball⟩ := Metric.isOpen_iff.1 (hUo.inter hW'open) 0 ⟨hU'eq ▸ h0U' |>.1, h0W'⟩
  set r₀ := ρ' / 2 with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  have hcball : Metric.closedBall (0 : (ScBanach.paramProd Pn W) 0) r₀ ⊆ Uo ∩ W' :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hcl_mem : ∀ u' ∈ Metric.closedBall (0 : (ScBanach.paramProd Pn W) 0) r₀ ∩ Ct ×ˢ univ,
      u' ∈ U' ∧ u' ∈ W' := fun u' hu' =>
    ⟨hU'eq ▸ ⟨(hcball hu'.1).1, hu'.2⟩, (hcball hu'.1).2⟩
  -- the solution set on the `E'`-side and the local theorem
  set S : Set ((ScBanach.paramProd Pn W) 0) :=
    {u' | u' ∈ G.U 0 ∧ h u' + (ScBanach.paramProd Q W).toBase 1 (t u') = 0} ∩
      Metric.ball 0 r₀ with hSdef
  obtain ⟨O', hO'open, h0O', hO'nest, hK⟩ := theorem_3_1_13_local_subset hh hCt.isClosed ht ht0
    (S := S) inter_subset_left
  obtain ⟨Og, hOg, hGeq⟩ := G.relOpen 0
  have hGmem : ∀ u', u' ∈ G.U 0 ↔ u' ∈ Og ∧ u' ∈ Ct ×ˢ univ := fun u' => by
    rw [hGeq]; rfl
  -- the neighbourhoods `O(i)` in `X`
  set O : ℕ → Set X := fun i =>
    (c.φ.source ∩ c.φ ⁻¹' N₁) ∩
      (c.φ.source ∩ (ψ ∘ c.φ) ⁻¹' (O' i ∩ Og ∩ Metric.ball 0 r₀)) with hOdef
  have hψφ : ContinuousOn (ψ ∘ c.φ) c.φ.source :=
    hψcont.comp c.φ.continuousOn_toFun fun x hx => hOU (c.φ.mapsTo_model x hx)
  refine ⟨O, fun i => ?_, fun i => ?_, fun i x hx => ?_, fun i => ?_⟩
  · exact (c.φ.continuousOn_toFun.isOpen_inter_preimage c.φ.isOpen_source hN₁open).inter
      (hψφ.isOpen_inter_preimage c.φ.isOpen_source (((hO'open i).inter hOg).inter
        Metric.isOpen_ball))
  · refine ⟨⟨hxV, by rw [mem_preimage, h0]; exact h0N₁⟩, hxV, ?_⟩
    rw [mem_preimage, Function.comp_apply, h0, hψ0]
    exact ⟨⟨h0O' i, ((hGmem 0).1 (G.zero_mem 0)).1⟩, Metric.mem_ball_self hr₀pos⟩
  · exact ⟨hx.1, hx.2.1, ⟨⟨hO'nest i hx.2.2.1.1, hx.2.2.1.2⟩, hx.2.2.2⟩⟩
  -- the compactness statement on level `i`
  obtain ⟨K', hK'c, hK'eq⟩ := hK i
  set Z : Set X := {x ∈ O i | IsZeroAt P f x} with hZdef
  set A : Set ((ScBanach.paramProd Pn W) 0) := S ∩ O' i with hAdef
  -- (F1) the closure of `A` lies in `U' ∩ W'`
  have hAsub : A ⊆ Metric.closedBall 0 r₀ ∩ Ct ×ˢ univ := fun u' hu' =>
    ⟨Metric.ball_subset_closedBall hu'.1.2, hU'C (hG hu'.1.1.1)⟩
  have hclA : closure A ⊆ Metric.closedBall 0 r₀ ∩ Ct ×ˢ univ :=
    closure_minimal hAsub (Metric.isClosed_closedBall.inter hC'closed)
  have hclA' : ∀ u' ∈ closure A, u' ∈ U' ∧ ψ' u' ∈ c.U ∧ ψ' u' ∈ N₁ := fun u' hu' => by
    obtain ⟨h1, h2⟩ := hcl_mem u' (hclA hu')
    exact ⟨h1, hΨ.invFun.base_mem h1, hW'sub h2 h1⟩
  -- the zeros of `g` among the images `ψ'(A)`
  have hAzero : ∀ u' ∈ A, g (ψ' u') = 0 := fun u' hu' => by
    have hu'U' : u' ∈ U' := hG hu'.1.1.1
    obtain ⟨-, h2, h3⟩ := hclA' u' (subset_closure hu')
    refine (hkey (ψ' u') h2 h3).1 ?_
    rw [hψ'ψ u' hu'U']
    exact hu'.1.1.2
  -- (Claim 1) `φ(Z) = ψ'(A)`
  have hφZ : c.φ '' Z = ψ' '' A := by
    ext u
    constructor
    · rintro ⟨x, ⟨⟨⟨hxV', hxN⟩, -, hxψ⟩, hxz⟩, rfl⟩
      have huO : c.φ x ∈ c.φ.model.O := c.φ.mapsTo_model x hxV'
      have hfbu : fb (c.φ x) = 0 := (c.isZeroAt_iff hf hxV').1 hxz
      have hgu : g (c.φ x) = 0 := by rw [← (hN₁ _ hxN).1 huO, hfbu]
      have hψU' : ψ (c.φ x) ∈ U' := hΨ.toFun.base_mem (hOU huO)
      refine ⟨ψ (c.φ x), ⟨⟨⟨(hGmem _).2 ⟨hxψ.1.2, hU'C hψU'⟩, ?_⟩, hxψ.2⟩, hxψ.1.1⟩,
        hψψ' _ (hOU huO)⟩
      exact (hkey _ (hOU huO) hxN).2 hgu
    · rintro ⟨u', hu', rfl⟩
      have hu'U' : u' ∈ U' := hG hu'.1.1.1
      obtain ⟨-, h2, h3⟩ := hclA' u' (subset_closure hu')
      have hgu : g (ψ' u') = 0 := hAzero u' hu'
      have huO : ψ' u' ∈ c.φ.model.O := hgO _ h2 h3 hgu
      refine ⟨c.φ.symm (ψ' u'), ⟨⟨⟨c.φ.symm_mapsTo huO, ?_⟩, c.φ.symm_mapsTo huO, ?_⟩, ?_⟩,
        c.φ.apply_symm_apply huO⟩
      · rw [mem_preimage, c.φ.apply_symm_apply huO]; exact h3
      · rw [mem_preimage, Function.comp_apply, c.φ.apply_symm_apply huO, hψ'ψ u' hu'U']
        exact ⟨⟨hu'.2, ((hGmem _).1 hu'.1.1.1).1⟩, hu'.1.2⟩
      · rw [c.isZeroAt_iff hf (c.φ.symm_mapsTo huO), c.φ.apply_symm_apply huO]
        change fb (ψ' u') = 0
        rw [(hN₁ _ h3).1 huO, hgu]
  -- (Claim 2) `closure(φ(Z)) = ψ'(closure A) =: T`, compact and inside `O`
  set T := ψ' '' closure A with hTdef
  have hTc : IsCompact T := by
    have h1 : IsCompact (closure A) := by
      rw [hK'eq]
      exact hK'c.image ((ScBanach.paramProd Pn W).toBase i).continuous
    exact h1.image_of_continuousOn (hψ'cont.mono fun u' hu' => (hclA' u' hu').1)
  have hclφZ : closure (c.φ '' Z) = T := by
    rw [hφZ]
    refine le_antisymm (closure_minimal (image_mono subset_closure) hTc.isClosed) ?_
    exact ContinuousOn.image_closure (hψ'cont.mono fun u' hu' => (hclA' u' hu').1)
  have hTO : ∀ u ∈ T, u ∈ c.φ.model.O ∧ u ∈ c.U ∧ u ∈ N₁ := by
    rintro _ ⟨u', hu', rfl⟩
    obtain ⟨-, h2, h3⟩ := hclA' u' hu'
    have hgu : g (ψ' u') = 0 := by
      refine eq_of_mem_closure_of_continuousOn hfill.isScSmooth.isSc1.isSc0.continuousOn_base
        (A := ψ' '' A) ?_ ?_ h2 ?_
      · rintro _ ⟨v', hv', rfl⟩; exact (hclA' v' (subset_closure hv')).2.1
      · rintro _ ⟨v', hv', rfl⟩; exact hAzero v' hv'
      · exact ContinuousOn.image_closure (hψ'cont.mono fun v' hv' => (hclA' v' hv').1) ⟨u', hu', rfl⟩
    exact ⟨hgO _ h2 h3 hgu, h2, h3⟩
  -- (Claim 3) `closure Z = φ⁻¹(T)`
  have hZV : Z ⊆ c.φ.source := fun x hx => hx.1.1.1
  have hclZ : closure Z = c.φ.symm '' T := by
    have hsymmT : ContinuousOn c.φ.symm T := c.φ.continuousOn_invFun.mono fun u hu => (hTO u hu).1
    refine le_antisymm (closure_minimal ?_ (hTc.image_of_continuousOn hsymmT).isClosed) ?_
    · intro x hx
      refine ⟨c.φ x, ?_, c.φ.symm_apply_apply (hZV hx)⟩
      rw [← hclφZ]; exact subset_closure ⟨x, hx, rfl⟩
    · have := ContinuousOn.image_closure (s := c.φ '' Z) (f := c.φ.symm) (by rwa [hclφZ])
      rw [hclφZ, c.φ.toPartialEquiv.symm_image_image_of_subset_source hZV] at this
      exact this
  -- (Claim 4) the compact set in `X_i`
  have hx₀i : x₀ ∈ PX.levelSet i := mem_iInter.1 hxs i
  set x₀' : PX.Level i := PX.levelMk i x₀ hx₀i with hx₀'def
  set Θ : (ScBanach.paramProd Pn W) i → PX.Level i :=
    fun z => PX.levelChartSymm c.isChart i x₀' (levelMap ψ' i z) with hΘdef
  have hK'U' : K' ⊆ (ScBanach.paramProd Pn W).lvlSet U' i := fun z hz =>
    (hclA' _ (hK'eq ▸ ⟨z, hz, rfl⟩)).1
  have hK'T : ∀ z ∈ K', ψ' ((ScBanach.paramProd Pn W).toBase i z) ∈ T := fun z hz =>
    ⟨_, hK'eq ▸ ⟨z, hz, rfl⟩, rfl⟩
  have hlev : ∀ z ∈ K', c.φ.model.E.toBase i (levelMap ψ' i z) =
      ψ' ((ScBanach.paramProd Pn W).toBase i z) := fun z hz =>
    hψ'sc0.toBase_levelMap (hK'U' hz)
  have hlevO : ∀ z ∈ K', levelMap ψ' i z ∈ c.φ.model.E.lvlSet c.φ.model.O i := fun z hz => by
    rw [ScBanach.mem_lvlSet, hlev z hz]
    exact (hTO _ (hK'T z hz)).1
  refine ⟨Θ '' K', hK'c.image_of_continuousOn ?_, ?_⟩
  · exact (PX.continuousOn_levelChartSymm c.isChart i x₀').comp
      ((hψ'sc0.continuousOn i).mono hK'U') hlevO
  · rw [hclZ, image_image, hTdef, hK'eq, image_image, image_image]
    refine image_congr fun z hz => ?_
    simp only [hΘdef]
    rw [PX.levelVal_levelChartSymm c.isChart i x₀' (hlevO z hz), hlev z hz]

/-- **Corollary 3.1.15 (preprint 3.13)** (at the base point of the germ): let `(f, x₀)` be an sc-Fredholm germ with
`f(x₀) = 0`.  If `f(x_k) = 0` and `x_k → x₀` in `X`, then for every `m` there are lifts
`y_k ∈ X_m` of the `x_k` (for `k` large) converging in `X_m` to the lift of `x₀`. -/
theorem corollary_3_1_15_wholeChart (hf : IsSection P f) {x₀ : X} (hg : B.IsScFredholmGermWholeChart f x₀)
    (hx₀ : IsZeroAt P f x₀) {x : ℕ → X} (hx : ∀ n, IsZeroAt P f (x n))
    (hlim : Tendsto x atTop (𝓝 x₀)) (m : ℕ) :
    ∃ y₀ : PX.Level m, PX.levelVal m y₀ = x₀ ∧ ∃ y : ℕ → PX.Level m,
      (∀ᶠ n in atTop, PX.levelVal m (y n) = x n) ∧ Tendsto y atTop (𝓝 y₀) := by
  classical
  obtain ⟨O, hO, h0, -, hK⟩ := theorem_3_1_13_wholeChart hf hg hx₀
  obtain ⟨K, hKc, hKeq⟩ := hK m
  set y₀ : PX.Level m := PX.levelMk m x₀ (mem_iInter.1 hg.1 m) with hy₀
  have hev : ∀ᶠ n in atTop, x n ∈ O m := hlim.eventually ((hO m).mem_nhds (h0 m))
  have hmem : ∀ n, x n ∈ O m → x n ∈ PX.levelVal m '' K := fun n hn => by
    rw [hKeq]; exact subset_closure ⟨hn, hx n⟩
  refine ⟨y₀, rfl, fun n => if hn : x n ∈ O m then (hmem n hn).choose else y₀, ?_, ?_⟩
  · filter_upwards [hev] with n hn
    rw [dif_pos hn]; exact (hmem n hn).choose_spec.2
  · refine tendsto_of_isCompact_of_tendsto_map hKc (PX.continuous_levelVal m)
      (MPolyfold.levelVal_injective m) ?_ ?_
    · filter_upwards [hev] with n hn
      rw [dif_pos hn]; exact (hmem n hn).choose_spec.1
    · refine hlim.congr' ?_
      filter_upwards [hev] with n hn
      rw [dif_pos hn]; exact ((hmem n hn).choose_spec.2).symm

namespace StrongBundle

/-- The zero section takes values in `Y_{m,m+1}` over `X_m`: in a chart `Φ(0_x) = (φ(x), 0)`. -/
lemma fiberZero_mem_doubleLevel (B : StrongBundle PX P) {m : ℕ} {x : X} (hx : x ∈ PX.levelSet m) :
    fiberZero P x ∈ B.doubleLevel m (m + 1) := by
  intro c hc hmem
  have hxV : x ∈ c.φ.source := by rw [c.source_eq, mem_preimage, proj_fiberZero P] at hmem; exact hmem
  refine ⟨?_, ?_⟩
  · rw [c.fst_apply (by rw [proj_fiberZero P]; exact hxV), proj_fiberZero P]
    exact (PX.mem_levelSet_iff c.isChart hxV).1 hx
  · rw [c.snd_fiberZero hxV]; exact ⟨0, map_zero _⟩

/-- A zero of a regularizing section is a smooth point (the first sentence of the proof of
Theorem 3.6.8 (preprint 3.54)). -/
theorem IsScFredholmSectionWholeChart.mem_smoothSet_of_isZeroAt (hf : B.IsScFredholmSectionWholeChart f) {x : X}
    (hx : IsZeroAt P f x) : x ∈ PX.smoothSet := by
  refine mem_iInter.2 fun m => ?_
  induction m with
  | zero => rw [PX.levelSet_zero]; exact mem_univ _
  | succ m ih =>
    refine hf.regularizing m x ih ?_
    rw [hx]; exact B.fiberZero_mem_doubleLevel ih

/-- A limit of zeros of an sc-smooth section is a zero (the principal part is continuous). -/
theorem IsScSmoothSection.isZeroAt_of_tendsto (hf : B.IsScSmoothSection f) {x : ℕ → X}
    (hx : ∀ n, IsZeroAt P f (x n)) {x₀ : X} (hlim : Tendsto x atTop (𝓝 x₀)) :
    IsZeroAt P f x₀ := by
  obtain ⟨c, hc, hxV⟩ := B.exists_chart_mem x₀
  rw [c.isZeroAt_iff hf.1 hxV]
  have hev : ∀ᶠ n in atTop, x n ∈ c.φ.source := hlim.eventually (c.φ.isOpen_source.mem_nhds hxV)
  have h1 : Tendsto (fun n => c.φ (x n)) atTop (𝓝 (c.φ x₀)) :=
    ((c.φ.continuousOn_toFun x₀ hxV).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, hev⟩))
  have h2 : Tendsto (fun n => c.principal f (c.φ (x n))) atTop (𝓝 (c.principal f (c.φ x₀))) :=
    ((hf.continuousOn_principal (B.isChart_of_mem hc) _ (c.φ.mapsTo_model x₀ hxV)).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨h1, hev.mono fun n hn => c.φ.mapsTo_model _ hn⟩))
  have h3 : Tendsto (fun n => c.principal f (c.φ (x n))) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with n hn
    exact ((c.isZeroAt_iff hf.1 hn).1 (hx n)).symm
  exact tendsto_nhds_unique h2 h3

end StrongBundle

/-- **Corollary 3.1.15 (preprint 3.13) for sc-Fredholm sections** (Definition 3.1.16 (preprint 3.14)), with an arbitrary limit: if
`f(x_k) = 0` and `x_k → x` in `X`, then `x` is a zero of `f`, a smooth point, and for every `m`
there are lifts `y_k ∈ X_m` of the `x_k` (for `k` large) converging in `X_m` to the lift of `x`
(in particular `x_k ∈ X_m` for `k` large, "and `x_k → x` in `X_m`").  The text states this for a
germ `(f, x₀)`, where it holds for `x = x₀` (`corollary_3_1_15_wholeChart`). -/
theorem corollary_3_1_15_section_wholeChart (hf : B.IsScFredholmSectionWholeChart f) {x : ℕ → X}
    (hx : ∀ n, IsZeroAt P f (x n)) {x₀ : X} (hlim : Tendsto x atTop (𝓝 x₀)) (m : ℕ) :
    IsZeroAt P f x₀ ∧ x₀ ∈ PX.smoothSet ∧
      ∃ y₀ : PX.Level m, PX.levelVal m y₀ = x₀ ∧ ∃ y : ℕ → PX.Level m,
        (∀ᶠ n in atTop, PX.levelVal m (y n) = x n) ∧ Tendsto y atTop (𝓝 y₀) := by
  have hx₀ : IsZeroAt P f x₀ := hf.isScSmooth.isZeroAt_of_tendsto hx hlim
  have hxs : x₀ ∈ PX.smoothSet := hf.mem_smoothSet_of_isZeroAt hx₀
  exact ⟨hx₀, hxs, corollary_3_1_15_wholeChart hf.isScSmooth.1 (hf.germ x₀ hxs) hx₀ hx hlim m⟩

end Bundle

end Polyfold
