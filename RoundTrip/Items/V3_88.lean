import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V3_88

/-!
Round trip for V3_88 (Theorem 3.58, given the family of sc-isomorphisms).  `A` is the conjunction
of the types of `Polyfold.theorem_3_7_1_of_family`, `Polyfold.contrMap358_contraction`,
`Polyfold.norm_sub_sub_le_of_hasFDerivWithinAt_segment` (universes `0, 0, 0`),
`Polyfold.fiberIsoMap_isStrongBundleIso` and `Polyfold.famInv_isScSmooth_of`
(`Polyfold.DerivCondition` is vocabulary).

Glue for `A → B` (only the first conjunct of `A` is used):
* B's condition (3) `UniformD2Estimate` (stated in `E = Bf ⊕ X` with the subspaces
  `Bsub = Bf ⊕ 0`, `Xsub = 0 ⊕ X`) gives the project's `DerivCondition` (stated with points
  `(b, 0)`, `(b, x)`, `(0, h)`): apply it to `(b, 0)`, `(0, x)`, `(0, h)`; the norms agree since
  `‖(b, 0)‖ = ‖b‖`, `‖(0, x)‖ = ‖x‖`.
* B's `O = O' ∩ C̃` is the project's `Vo ∩ C̃` with `Vo = O'`; `U₀ = U ∩ (O' × X)`.
* B's `Φ`, `Φ'` are `fiberIsoMap X (L ·).symm`, `fiberIsoMap X L`, and B's `pushed L f` is
  `pushGerm358 L f`, all definitionally; the germ is `ScNbhdGerm.ofSet U₀`, whose level `0` is `U₀`.
B's other hypotheses (constant-index Fredholm, `ker Df(0) ⊆ B`, compactness, `Y = Df(0)X`) are not
needed: they serve to produce the family `L`, which `B` takes as given.
-/

namespace RoundTrip.V3_88
open Polyfold Set

/-- The project's statement: Theorem 3.58 from the family, the contraction estimate, the mean
value inequality along a segment, the strong bundle isomorphism and Lemma 3.61. -/
def A : Prop :=
  type_of% @Polyfold.theorem_3_7_1_of_family ∧ type_of% @Polyfold.contrMap358_contraction ∧
    type_of% @Polyfold.norm_sub_sub_le_of_hasFDerivWithinAt_segment.{0, 0, 0} ∧
    type_of% @Polyfold.fiberIsoMap_isStrongBundleIso ∧ type_of% @Polyfold.famInv_isScSmooth_of

theorem A_holds : A :=
  ⟨@Polyfold.theorem_3_7_1_of_family, @Polyfold.contrMap358_contraction,
    @Polyfold.norm_sub_sub_le_of_hasFDerivWithinAt_segment.{0, 0, 0},
    @Polyfold.fiberIsoMap_isStrongBundleIso, @Polyfold.famInv_isScSmooth_of⟩

/-- B's condition (3) gives the project's `DerivCondition`. -/
theorem derivCondition_of_uniform {Bf Af : Type} [NormedAddCommGroup Bf] [NormedSpace ℝ Bf]
    [FiniteDimensional ℝ Bf] [NormedAddCommGroup Af] [NormedSpace ℝ Af] [FiniteDimensional ℝ Af]
    {X Y : ScBanach} {Ct : Set Bf} {U : Set ((ScBanach.paramProd Bf X).lvl 0)}
    {f : (ScBanach.paramProd Bf X).lvl 0 → (ScBanach.paramProd Af Y).lvl 0}
    (h : UniformD2Estimate (ScBanach.paramProd Bf X) (ScBanach.paramProd Af Y) U f (Bsub Bf X)
      (Xsub Bf X)) : DerivCondition Ct U f := by
  intro m ε hε
  obtain ⟨r, hr, hD⟩ := h m ε hε
  refine ⟨r, hr, fun b _ hbr x hb0 hbx hxr k => ?_⟩
  have e0 : (ScBanach.paramProd Bf X).toBase (m + 1) ((b, 0) : Bf × X (m + 1)) =
      ((b, 0) : Bf × X 0) := by
    rw [ScBanach.paramProd_toBase, map_zero]
  have hbB : (ScBanach.paramProd Bf X).toBase (m + 1) ((b, 0) : Bf × X (m + 1)) ∈ Bsub Bf X := by
    rw [e0]; exact ⟨b, rfl⟩
  have hbn : ‖(ScBanach.paramProd Bf X).toBase (m + 1) ((b, 0) : Bf × X (m + 1))‖ < r := by
    rw [e0, Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _)]; exact hbr
  have hxX : (ScBanach.paramProd Bf X).toBase (m + 1) ((0, x) : Bf × X (m + 1)) ∈ Xsub Bf X := by
    rw [ScBanach.paramProd_toBase]; exact ⟨X.toBase (m + 1) x, rfl⟩
  have hxn : ‖(ScBanach.paramProd Bf X).incl m ((0, x) : Bf × X (m + 1))‖ < r := by
    rw [ScBanach.paramProd_incl, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
    exact hxr
  have hsum : ((b, 0) : Bf × X (m + 1)) + ((0, x) : Bf × X (m + 1)) = ((b, x) : Bf × X (m + 1)) := by
    rw [Prod.mk_add_mk, add_zero, zero_add]
  have hkX : (ScBanach.paramProd Bf X).toBase m ((0, k) : Bf × X m) ∈ Xsub Bf X := by
    rw [ScBanach.paramProd_toBase]; exact ⟨X.toBase m k, rfl⟩
  have := hD ((b, 0) : Bf × X (m + 1)) ((0, x) : Bf × X (m + 1)) hbB hb0 hbn hxX hxn
    (by rw [hsum]; exact hbx) ((0, k) : Bf × X m) hkX
  have hk : ‖((0, k) : (ScBanach.paramProd Bf X).lvl m)‖ = ‖k‖ := by
    rw [Prod.norm_def]; simp
  rw [hsum, hk] at this
  exact this

theorem A_to_B (hA : A) : B := by
  intro Bf Af _ _ _ _ _ _ X Y Ct U f hCt hU h0 hf _ _ _ hD3 _ O L hOrel h0O hOU hL hc
  obtain ⟨O', hO'o, rfl⟩ := hOrel
  have hOU' : ∀ b ∈ O' ∩ Ct, ((b, 0) : Bf × X.lvl 0) ∈ U := hOU
  obtain ⟨hbasic, hiso, -⟩ := hA.1 hCt hU h0 hf hO'o h0O.1 hOU' hL hc
    (derivCondition_of_uniform hD3)
  have hUC : U ⊆ Ct ×ˢ univ := by obtain ⟨O, -, rfl⟩ := hU.relOpen; exact inter_subset_right
  exact ⟨U ∩ O' ×ˢ univ, hU.inter_isOpen (hO'o.prod isOpen_univ), ⟨h0, h0O.1, mem_univ _⟩,
    inter_subset_left, fun u hu => ⟨hu.2.1, (hUC hu.1).1⟩, hiso, _, contrMap358 L f,
    fun u hu => hu, hbasic⟩

#rt_check RoundTrip.V3_88.A_to_B [Polyfold.theorem_3_7_1_of_family,
  Polyfold.contrMap358_contraction, Polyfold.norm_sub_sub_le_of_hasFDerivWithinAt_segment,
  Polyfold.fiberIsoMap_isStrongBundleIso, Polyfold.famInv_isScSmooth_of]
#rt_overlap RoundTrip.V3_88.A_to_B [Polyfold.theorem_3_7_1_of_family,
  Polyfold.contrMap358_contraction, Polyfold.norm_sub_sub_le_of_hasFDerivWithinAt_segment,
  Polyfold.fiberIsoMap_isStrongBundleIso, Polyfold.famInv_isScSmooth_of]

end RoundTrip.V3_88
