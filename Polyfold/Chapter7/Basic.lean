import Polyfold.Chapter7.EpGroupoid
import Polyfold.Chapter7.ProperMaps
import Polyfold.Chapter7.Discrete
import Polyfold.Chapter7.LocalDiffeo

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (2017, arXiv 1707.08941), Part II, §7.1,
pp. 228–230: the remark after **Definition 7.7** (pp. 228–229), **Propositions 7.1–7.3**
(p. 229, the proof of 7.3 ending on p. 230), **Lemma 7.1** and **Proposition 7.4** (p. 230), and
the conjugation `G_x ≅ G_y` after Proposition 7.4 (p. 230).  There is no 2014 preprint of Part II;
numbers and pages are the 2017 text's.

# Basic properties of ep-groupoids

## The text, paraphrased

(Remark after Definition 7.7, pp. 228–229) "It is sufficient to require that the functor `f` is
sc-smooth between the object spaces": given `φ ∈ 𝐗` and `f(φ) = ψ` there are open `U(φ)`, `U(ψ)`,
`U(s φ)`, `U(s ψ)` with `f(U(s φ)) ⊂ U(s ψ)`, `f(U(φ)) ⊂ U(ψ)`, `s : U(φ) → U(s φ)` and
`s : U(ψ) → U(s ψ)` sc-diffeomorphisms, and `f(γ) = (s|U(ψ))⁻¹(f(s γ))` for `γ ∈ U(φ)`.
(p. 229) `|X|` carries the quotient topology.  (Proposition 7.1) `π : X → |X|` is open: for open
`U`, a point `y` of `π⁻¹(π(U))` is the target of some `φ` with `s φ ∈ U`, and a sheet of `φ`
gives `O(y) ⊂ π⁻¹(π(U))`.  (Proposition 7.2) Every `z ∈ |X|` has a countable monotone basis of
open neighbourhoods `z ∈ V_k ⊂ V_{k-1} ⊂ … ⊂ V_1`: `V_k = π(B_{1/k}(x))` for a metric on `X`
(Theorem 2.2) and `π(x) = z`.  (Proposition 7.3) For every `z ∈ |X|` and every representative `x`
there is an open `U ∋ x` with `π(cl_X(A)) = cl_{|X|}(π(A))` for all `A ⊂ U`; the proof takes `U`
with `t : s⁻¹(cl_X(U)) → X` proper and argues with sequences `φ_k : x_k → y_k`, `x_k ∈ A`,
`y_k → y`.  (Lemma 7.1) If `t : s⁻¹(cl_X(U(x₀))) → X` is proper for an open `U(x₀) ∋ x₀`, only
finitely many `ψ` have `s(ψ) = x` and `t(ψ) ∈ U(x₀)`.  (Proposition 7.4, "as a consequence") `G_x`
is finite.  (p. 230) Isomorphic objects have isomorphic isotropy groups; there is no canonical
identification, each depends on a choice of `φ : x → y` and is `g ↦ φ ∘ g ∘ φ⁻¹`.

## What is formalized

* **The remark after Definition 7.7, with continuity on morphisms**:
  `EpGroupoid.mor_eq_srcInv_obj_src` (the text's formula `f(γ) = (s|U(ψ))⁻¹(f(s γ))`),
  `EpGroupoid.isScSmoothMap_mor_of_continuous` (a functor between ep-groupoids that is sc-smooth
  on objects and continuous on morphisms is sc-smooth on morphisms),
  `EpGroupoid.isScSmoothMap_mor_iff_continuous`, `EpFunctor.continuous_mor`, and the constructor
  `EpFunctor.ofContinuous`.
* **Proposition 7.1**: `proposition_7_1` (`IsOpenMap π`), `proposition_7_1_isOpenQuotientMap`,
  `proposition_7_1_map_nhds` (`map π (𝓝 x) = 𝓝 (π x)`).
* **Proposition 7.2**: `proposition_7_2` (an antitone countable basis of open neighbourhoods,
  `V_k = π(B_{1/(k+1)}(x))`), `proposition_7_2_of_hasAntitoneBasis` (the images `π(O_k)` of an
  antitone basis at a representative, as in the proof of Proposition 7.3), the instance
  `proposition_7_2_firstCountableTopology`.
* **Proposition 7.3**: `proposition_7_3`, and `proposition_7_3_of_isProperMap` (every `U` with
  `t : s⁻¹(cl U) → X` proper works, for all `A ⊆ cl U`).
* **Lemma 7.1**: `lemma_7_1` (the statement), `lemma_7_1_swap` (sources and targets exchanged,
  the form its proof treats), and the forms without the unused hypotheses and with `cl U(x₀)`,
  `lemma_7_1_of_isProperMap`, `lemma_7_1_swap_of_isProperMap`.
* **Proposition 7.4**: the instance `proposition_7_4 : Finite (X.Isotropy x)`.
* **p. 230, the conjugation**: `conjIsotropy φ : G_{s φ} ≃* G_{t φ}` (`GroupoidStr.isotropyConj`,
  `g ↦ φ ∘ g ∘ φ⁻¹`), `conjIsotropy_val`, `nonempty_isotropy_mulEquiv` and
  `nat_card_isotropy_eq` (isomorphic objects have isomorphic isotropy groups), and
  `isotropyConj_eq_isotropyConj_conj` (two choices `φ, φ' : x → y` differ by the inner
  automorphism of `G_x` by `φ⁻¹ ∘ φ'`).

## Reading

* **The remark after Definition 7.7** does not hold as we read it if only sc-smoothness on the
  objects is asked (PLAN II.6, 1): the choice of `U(φ)` with `f(U(φ)) ⊂ U(ψ)` uses the continuity
  of `f` on morphisms, which a functor sc-smooth on objects need not have.  The counterexample
  (`ℤ/3 × ℝ ⇉ ℝ` with the trivial action, the identity on objects, `(g, y) ↦ (g², y)` for `y > 0`
  and `(g, y)` for `y ≤ 0`) is not in this file (PLAN II.4, W5).  With continuity on morphisms
  added the remark holds, by the text's formula: `isScSmoothMap_mor_of_continuous`.  The proof
  needs only the sheet `U(ψ)` of `s` at `ψ = f(φ)` and `U(φ) = f⁻¹(U(ψ))`; the sheet of `s` at
  `φ` and the neighbourhoods `U(s φ)`, `U(s ψ)` of the text are not used, and on the source side
  only the sc-smoothness of `s` enters.
  Since every `EpFunctor` is continuous on morphisms (`EpFunctor.continuous_mor`), the corrected
  remark is the equivalence `isScSmoothMap_mor_iff_continuous` for functors sc-smooth on objects.
* **The quotient topology** (p. 229) is Mathlib's on `Quotient X.orbitSetoid`; `π = Quotient.mk`.
* **Proposition 7.1** is proved through the saturation `π⁻¹(π(U)) = t(s⁻¹(U))`: `s` is
  continuous and `t` is an open map, being a local sc-diffeomorphism.  This is the text's argument
  with the sheet `V(φ)` packaged into `IsLocalScDiffeo.isOpenMap`.
* **Proposition 7.2** is stated as `(𝓝 z).HasAntitoneBasis V` with every `V k` open and containing
  `z`; Mathlib's `HasAntitoneBasis` is "a basis, indexed by `ℕ`, and monotone", the text's
  "countable basis …, chosen in a monotone way".  The index starts at `0`, so the balls have radius
  `1/(k+1)` instead of `1/k`.  The metric is `metrizableSpaceMetric`, from Theorem 2.2 [2.16]
  (`MPolyfold.metrizableSpace`).
* **Proposition 7.3** is proved without sequences: since `π` is open and continuous,
  `π⁻¹(cl π(A)) = cl π⁻¹(π(A)) = cl t(s⁻¹(A))`, and `t(s⁻¹(cl A))` is closed, `t` being proper,
  hence closed, on the closed set `s⁻¹(cl A) ⊆ s⁻¹(cl U)`
  (`isClosed_image_preimage_of_isProperMap_domRestrict`).  This replaces the text's extraction of
  a convergent subsequence of `(φ_k)`, which uses the same properness.  The statement holds for
  every `A ⊆ cl U`, not only `A ⊆ U`.  "For every `z` and every representative `x` of `z`" is
  "for every `x`", with `z = π(x)`.
* **Lemma 7.1.**  The proof exchanges source and target of the statement (possible misprint): it
  takes `ψ_n : s(ψ_n) → x` with `s(ψ_n) ∈ U(x₀)`, i.e. `t(ψ_n) = x`, the inverses of the morphisms
  of the statement; it also writes `V(y)` for `V(x)` (possible misprint).  Both forms hold:
  `lemma_7_1_swap` is the proof's form (a compact discrete fibre of `t : s⁻¹(cl U(x₀)) → X`, by
  `MPolyfold.finite_setOf_mem_of_isLocalScDiffeo`), and `lemma_7_1`, the statement, follows by
  `ι`, which exchanges `s` and `t`.  The hypotheses "`U(x₀)` open" and "`x₀ ∈ U(x₀)`" are kept in
  `lemma_7_1` as in the text but are not used (named `_hU`, `_hx₀`); `t(ψ) ∈ U(x₀)` may be
  weakened to `t(ψ) ∈ cl_X(U(x₀))` (`lemma_7_1_of_isProperMap`).
* **Proposition 7.4** is derived from `lemma_7_1` with `x₀ = x` and `U(x₀) = V(x)` of Definition
  7.3 (3), as the text's "as a consequence" indicates.  It is an instance, so `Nat.card (G_x)` is
  the order of the group.
* **The conjugation** is Groupoid.lean's `isotropyConj` (through Mathlib's
  `vertexGroupIsomOfMap`).  "There is no canonical identification" is not a mathematical
  statement; its content, that the identification depends on `φ` only up to an inner automorphism
  of `G_x`, is `isotropyConj_eq_isotropyConj_conj`.
* **Hypotheses.**  No hypothesis of the form "for all charts" or "for every …" is added.  The
  properness hypotheses of `lemma_7_1` and `proposition_7_3_of_isProperMap` are satisfiable: by
  Definition 7.3 (3) every object `x₀` has such a `U(x₀) = V(x₀)` (`EpGroupoid.exists_isProperMap`;
  `proposition_7_3` and `proposition_7_4` use it).  The continuity hypothesis of `ofContinuous`
  holds for every `EpFunctor`, e.g. `EpFunctor.id`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

universe u v

namespace EpGroupoid

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] (X : EpGroupoid Obj Mor)

/-! ### The saturation of a set -/

/-- The saturation `π⁻¹(π(A))` is `t(s⁻¹(A))`, the targets of the morphisms with source in `A`. -/
private theorem preimage_π_image_eq (A : Set Obj) :
    X.π ⁻¹' (X.π '' A) = X.tgt '' (X.src ⁻¹' A) := by
  ext y
  constructor
  · rintro ⟨a, ha, hay⟩
    obtain ⟨φ, rfl, rfl⟩ := (X.π_eq_π_iff).1 hay
    exact ⟨φ, ha, rfl⟩
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨X.src φ, hφ, X.π_src_eq_π_tgt φ⟩

/-! ### Proposition 7.1 -/

/-- **Proposition 7.1 (openness of `π`)**: the quotient map `π : X → |X|` is open. -/
theorem proposition_7_1 : IsOpenMap X.π := by
  intro U hU
  have h : IsOpen (X.π ⁻¹' (X.π '' U)) := by
    rw [preimage_π_image_eq]
    exact X.isLocalScDiffeo_tgt.isOpenMap _ (hU.preimage X.continuous_src)
  exact isQuotientMap_quotient_mk'.isOpen_preimage.1 h

/-- **Proposition 7.1**: `π : X → |X|` is an open quotient map (surjective, continuous, open). -/
theorem proposition_7_1_isOpenQuotientMap : IsOpenQuotientMap X.π :=
  ⟨X.surjective_π, X.continuous_π, X.proposition_7_1⟩

/-- The neighbourhoods of `π(x)` are the images of the neighbourhoods of `x`. -/
theorem proposition_7_1_map_nhds (x : Obj) : map X.π (𝓝 x) = 𝓝 (X.π x) :=
  X.proposition_7_1_isOpenQuotientMap.map_nhds_eq x

/-! ### Proposition 7.2 -/

/-- The images `π(O_k)` of an antitone neighbourhood basis `(O_k)` of `x` are an antitone
neighbourhood basis of `π(x)` (the form used in the proof of Proposition 7.3). -/
theorem proposition_7_2_of_hasAntitoneBasis {x : Obj} {O : ℕ → Set Obj}
    (hO : (𝓝 x).HasAntitoneBasis O) : (𝓝 (X.π x)).HasAntitoneBasis fun k => X.π '' O k := by
  rw [← X.proposition_7_1_map_nhds x]
  exact hO.map X.π

/-- **Proposition 7.2 (countable neighbourhood basis)**: every `z ∈ |X|` has a countable basis of
open neighbourhoods `z ∈ V_k`, monotone (`V_{k+1} ⊆ V_k`): `V_k = π(B_{1/(k+1)}(x))` for a metric
on `X` and a representative `x` of `z`. -/
theorem proposition_7_2 (z : X.OrbitSpace) :
    ∃ V : ℕ → Set X.OrbitSpace, (∀ k, IsOpen (V k) ∧ z ∈ V k) ∧ (𝓝 z).HasAntitoneBasis V := by
  obtain ⟨x, rfl⟩ := X.surjective_π z
  have := X.PObj.metrizableSpace
  let _ := TopologicalSpace.metrizableSpaceMetric Obj
  have hB : (𝓝 x).HasAntitoneBasis fun k : ℕ => Metric.ball x (1 / ((k : ℝ) + 1)) :=
    ⟨Metric.nhds_basis_ball_inv_nat_succ, fun k l hkl =>
      Metric.ball_subset_ball (Nat.one_div_le_one_div hkl)⟩
  refine ⟨fun k => X.π '' Metric.ball x (1 / ((k : ℝ) + 1)), fun k =>
    ⟨X.proposition_7_1 _ Metric.isOpen_ball, mem_image_of_mem _ (Metric.mem_ball_self ?_)⟩,
    X.proposition_7_2_of_hasAntitoneBasis hB⟩
  positivity

/-- **Proposition 7.2**: the orbit space is first countable. -/
instance proposition_7_2_firstCountableTopology : FirstCountableTopology X.OrbitSpace :=
  ⟨fun z => by
    obtain ⟨V, -, hV⟩ := X.proposition_7_2 z
    exact hV.toHasBasis.isCountablyGenerated⟩

/-! ### Proposition 7.3 -/

/-- **Proposition 7.3, for a given `U`**: if `t : s⁻¹(cl U) → X` is proper, then
`π(cl A) = cl π(A)` for every `A ⊆ cl U`. -/
theorem proposition_7_3_of_isProperMap {U A : Set Obj}
    (hU : IsProperMap ((X.src ⁻¹' closure U).domRestrict X.tgt)) (hA : A ⊆ closure U) :
    X.π '' closure A = closure (X.π '' A) := by
  refine (image_closure_subset_closure_image X.continuous_π).antisymm fun z hz => ?_
  obtain ⟨y, rfl⟩ := X.surjective_π z
  have hy : y ∈ closure (X.tgt '' (X.src ⁻¹' A)) := by
    rw [← preimage_π_image_eq,
      ← X.proposition_7_1.preimage_closure_eq_closure_preimage X.continuous_π]
    exact hz
  have hcl : IsClosed (X.tgt '' (X.src ⁻¹' closure A)) :=
    isClosed_image_preimage_of_isProperMap_domRestrict hU (closure_minimal hA isClosed_closure)
      (isClosed_closure.preimage X.continuous_src)
  obtain ⟨φ, hφ, rfl⟩ :=
    (hcl.closure_subset_iff.2 (image_mono (preimage_mono subset_closure))) hy
  exact ⟨X.src φ, hφ, X.π_src_eq_π_tgt φ⟩

/-- **Proposition 7.3 (local closure relation)**: for every object `x` (a representative of
`z = π(x)`) there is an open `U ∋ x` such that `π(cl_X(A)) = cl_{|X|}(π(A))` for every `A ⊆ U`. -/
theorem proposition_7_3 (x : Obj) :
    ∃ U : Set Obj, IsOpen U ∧ x ∈ U ∧ ∀ A ⊆ U, X.π '' closure A = closure (X.π '' A) := by
  obtain ⟨U, hUo, hxU, hU⟩ := X.exists_isProperMap x
  exact ⟨U, hUo, hxU, fun A hA => X.proposition_7_3_of_isProperMap hU (hA.trans subset_closure)⟩

/-! ### Lemma 7.1 -/

/-- **Lemma 7.1, the form of its proof**: if `t : s⁻¹(cl U) → X` is proper, only finitely many
`ψ` have `t(ψ) = x` and `s(ψ) ∈ cl U`. -/
theorem lemma_7_1_swap_of_isProperMap {U : Set Obj}
    (hU : IsProperMap ((X.src ⁻¹' closure U).domRestrict X.tgt)) (x : Obj) :
    {ψ | X.tgt ψ = x ∧ X.src ψ ∈ closure U}.Finite :=
  (MPolyfold.finite_setOf_mem_of_isLocalScDiffeo X.isLocalScDiffeo_tgt hU x).subset
    fun _ hψ => ⟨hψ.2, hψ.1⟩

/-- **Lemma 7.1, the form of its statement**: if `t : s⁻¹(cl U) → X` is proper, only finitely
many `ψ` have `s(ψ) = x` and `t(ψ) ∈ cl U` (their inverses are the morphisms of
`lemma_7_1_swap_of_isProperMap`). -/
theorem lemma_7_1_of_isProperMap {U : Set Obj}
    (hU : IsProperMap ((X.src ⁻¹' closure U).domRestrict X.tgt)) (x : Obj) :
    {ψ | X.src ψ = x ∧ X.tgt ψ ∈ closure U}.Finite := by
  refine ((X.lemma_7_1_swap_of_isProperMap hU x).image X.inv).subset fun ψ hψ => ?_
  refine ⟨X.inv ψ, ⟨?_, ?_⟩, GroupoidStr.inv_inv ψ⟩
  · rw [X.tgt_inv]
    exact hψ.1
  · rw [X.src_inv]
    exact hψ.2

/-- **Lemma 7.1**: let `x, x₀ ∈ X` and `U(x₀)` an open neighbourhood of `x₀` such that
`t : s⁻¹(cl_X(U(x₀))) → X` is proper.  Then only finitely many morphisms `ψ` satisfy `s(ψ) = x`
and `t(ψ) ∈ U(x₀)`. -/
theorem lemma_7_1 {x x₀ : Obj} {U : Set Obj} (_hU : IsOpen U) (_hx₀ : x₀ ∈ U)
    (hp : IsProperMap ((X.src ⁻¹' closure U).domRestrict X.tgt)) :
    {ψ | X.src ψ = x ∧ X.tgt ψ ∈ U}.Finite :=
  (X.lemma_7_1_of_isProperMap hp x).subset fun _ hψ => ⟨hψ.1, subset_closure hψ.2⟩

/-- **Lemma 7.1 with source and target exchanged**, the form its proof treats (possible
misprint): under the hypotheses of Lemma 7.1, only finitely many `ψ` satisfy `t(ψ) = x` and
`s(ψ) ∈ U(x₀)`. -/
theorem lemma_7_1_swap {x x₀ : Obj} {U : Set Obj} (_hU : IsOpen U) (_hx₀ : x₀ ∈ U)
    (hp : IsProperMap ((X.src ⁻¹' closure U).domRestrict X.tgt)) :
    {ψ | X.tgt ψ = x ∧ X.src ψ ∈ U}.Finite :=
  (X.lemma_7_1_swap_of_isProperMap hp x).subset fun _ hψ => ⟨hψ.1, subset_closure hψ.2⟩

/-! ### Proposition 7.4 and the conjugation -/

/-- **Proposition 7.4 (finiteness of the isotropy group)**: `G_x` is finite.  As in the text, a
consequence of Lemma 7.1 (with `x₀ = x` and `U(x₀) = V(x)` of Definition 7.3 (3)). -/
instance proposition_7_4 (x : Obj) : Finite (X.Isotropy x) := by
  obtain ⟨V, hVo, hxV, hV⟩ := X.exists_isProperMap x
  have := (X.lemma_7_1 (x := x) hVo hxV hV).to_subtype
  refine Finite.of_injective (β := {ψ | X.src ψ = x ∧ X.tgt ψ ∈ V})
    (fun g => ⟨g.val, g.src_val, by rw [g.tgt_val]; exact hxV⟩) fun g h hgh => ?_
  exact GroupoidStr.Isotropy.ext (congrArg Subtype.val hgh)

/-- **The identification `G_x ≅ G_y` given by `φ : x → y`** (p. 230): `g ↦ φ ∘ g ∘ φ⁻¹`,
Groupoid.lean's `isotropyConj`. -/
def conjIsotropy (φ : Mor) : X.Isotropy (X.src φ) ≃* X.Isotropy (X.tgt φ) :=
  X.isotropyConj φ rfl rfl

@[simp]
theorem conjIsotropy_val (φ : Mor) (g : X.Isotropy (X.src φ)) :
    (X.conjIsotropy φ g).val = X.comp (X.comp φ g.val) (X.inv φ) :=
  rfl

/-- **Isomorphic objects have isomorphic isotropy groups** (p. 230). -/
theorem nonempty_isotropy_mulEquiv {x y : Obj} (h : X.Isomorphic x y) :
    Nonempty (X.Isotropy x ≃* X.Isotropy y) := by
  obtain ⟨φ, hx, hy⟩ := h
  exact ⟨X.isotropyConj φ hx hy⟩

theorem nat_card_isotropy_eq {x y : Obj} (h : X.Isomorphic x y) :
    Nat.card (X.Isotropy x) = Nat.card (X.Isotropy y) := by
  obtain ⟨e⟩ := X.nonempty_isotropy_mulEquiv h
  exact Nat.card_congr e.toEquiv

open CategoryTheory in
/-- **The identification depends on the choice of `φ`** (p. 230), up to an inner automorphism:
for `φ, φ' : x → y` and `h = φ⁻¹ ∘ φ' ∈ G_x`, `φ' ∘ g ∘ φ'⁻¹ = φ ∘ (h g h⁻¹) ∘ φ⁻¹`. -/
theorem isotropyConj_eq_isotropyConj_conj {x y : Obj} {φ φ' : Mor} (hx : X.src φ = x)
    (hy : X.tgt φ = y) (hx' : X.src φ' = x) (hy' : X.tgt φ' = y) :
    ∃ h : X.Isotropy x, h.val = X.comp (X.inv φ) φ' ∧
      ∀ g, X.isotropyConj φ' hx' hy' g = X.isotropyConj φ hx hy (h * g * h⁻¹) := by
  let f := X.homMk φ hx hy
  let f' := X.homMk φ' hx' hy'
  let k : X.toOb x ⟶ X.toOb x := f' ≫ Groupoid.inv f
  refine ⟨⟨k.1, k.2.1, k.2.2⟩, rfl, fun g => GroupoidStr.Isotropy.ext ?_⟩
  let γ := X.homMk g.val g.src_val g.tgt_val
  change (Groupoid.inv f' ≫ γ ≫ f').1 =
    (Groupoid.inv f ≫ (Groupoid.inv k ≫ γ ≫ k) ≫ f).1
  congr 1
  simp [k, Groupoid.inv_eq_inv]

end EpGroupoid

/-! ### The remark after Definition 7.7 -/

section Remark

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor]
  {Obj' Mor' : Type v} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor']
  {X : EpGroupoid Obj Mor} {Y : EpGroupoid Obj' Mor'}

namespace EpGroupoid

/-- **The formula of the remark after Definition 7.7**: if `s : U(ψ) → U(s ψ)` is an
sc-diffeomorphism of `Y` with inverse `σ = (s|U(ψ))⁻¹` and `f(γ) ∈ U(ψ)`, then
`f(γ) = σ(f(s γ))`. -/
theorem mor_eq_srcInv_obj_src (F : GroupoidFunctor X.toGroupoidStr Y.toGroupoidStr)
    {σ : Obj' → Mor'} {W : Set Mor'} {V : Set Obj'} (hd : Y.PMor.IsScDiffeoOn Y.PObj Y.src σ W V)
    {γ : Mor} (hγ : F.mor γ ∈ W) : F.mor γ = σ (F.obj (X.src γ)) := by
  rw [← F.src_mor, hd.left_inv _ hγ]

/-- **The remark after Definition 7.7, with continuity on morphisms**: a functor between
ep-groupoids which is sc-smooth on the object spaces and continuous on the morphism spaces is
sc-smooth on the morphism spaces.  Near `φ`, with a sheet `s : U(ψ) → U(s ψ)` at `ψ = f(φ)` and
`U(φ) = f⁻¹(U(ψ))`, `f = (s|U(ψ))⁻¹ ∘ f ∘ s` on `U(φ)`. -/
theorem isScSmoothMap_mor_of_continuous {F : GroupoidFunctor X.toGroupoidStr Y.toGroupoidStr}
    (hobj : X.PObj.IsScSmoothMap Y.PObj F.obj) (hmor : Continuous F.mor) :
    X.PMor.IsScSmoothMap Y.PMor F.mor := by
  refine MPolyfold.IsScSmoothOn.of_locally isOpen_univ fun φ _ => ?_
  obtain ⟨W, V, σ, hψ, hd⟩ := Y.isLocalScDiffeo_src (F.mor φ)
  have hO : IsOpen (F.mor ⁻¹' W) := hd.isScSmoothOn.isOpen.preimage hmor
  refine ⟨F.mor ⁻¹' W, hO, hψ, subset_univ _, ?_⟩
  have h₁ : X.PMor.IsScSmoothOn Y.PObj (F.obj ∘ X.src) (F.mor ⁻¹' W) :=
    (hobj.comp X.isScSmoothMap_src).mono hO (subset_univ _)
  have h₂ : MapsTo (F.obj ∘ X.src) (F.mor ⁻¹' W) V := fun γ hγ => by
    rw [comp_apply, ← F.src_mor]
    exact hd.mapsTo hγ
  exact (hd.isScSmoothOn_inv.comp h₁ h₂).congr fun γ hγ =>
    (mor_eq_srcInv_obj_src F hd hγ).symm

/-- **The remark after Definition 7.7, corrected**: for a functor sc-smooth on objects,
sc-smoothness on morphisms is equivalent to continuity on morphisms. -/
theorem isScSmoothMap_mor_iff_continuous {F : GroupoidFunctor X.toGroupoidStr Y.toGroupoidStr}
    (hobj : X.PObj.IsScSmoothMap Y.PObj F.obj) :
    X.PMor.IsScSmoothMap Y.PMor F.mor ↔ Continuous F.mor :=
  ⟨fun h => continuousOn_univ.1 h.continuousOn, isScSmoothMap_mor_of_continuous hobj⟩

end EpGroupoid

namespace EpFunctor

/-- A morphism of `EP` is continuous on morphisms. -/
theorem continuous_mor (F : EpFunctor X Y) : Continuous F.mor :=
  continuousOn_univ.1 F.isScSmoothMap_mor.continuousOn

/-- **A morphism of `EP` from a functor sc-smooth on objects and continuous on morphisms** (the
remark after Definition 7.7, with continuity on morphisms). -/
def ofContinuous (F : GroupoidFunctor X.toGroupoidStr Y.toGroupoidStr)
    (hobj : X.PObj.IsScSmoothMap Y.PObj F.obj) (hmor : Continuous F.mor) : EpFunctor X Y where
  toGroupoidFunctor := F
  isScSmoothMap_obj := hobj
  isScSmoothMap_mor := EpGroupoid.isScSmoothMap_mor_of_continuous hobj hmor

@[simp]
theorem ofContinuous_toGroupoidFunctor (F : GroupoidFunctor X.toGroupoidStr Y.toGroupoidStr)
    (hobj : X.PObj.IsScSmoothMap Y.PObj F.obj) (hmor : Continuous F.mor) :
    (ofContinuous F hobj hmor).toGroupoidFunctor = F :=
  rfl

end EpFunctor

end Remark

end Polyfold
