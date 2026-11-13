import Polyfold.Chapter4.LocalStrongBundle
import Polyfold.Chapter4.RetractionSectionSplitting
import Polyfold.Chapter4.ScPlusGraph
import Polyfold.Chapter3.GlobalIFTNearbyOntoXi

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Part I, §4.1,
**Lemma 4.1.11** (p. 179; preprint: Lemma 4.10; 2017: inside the proof of Proposition 4.2).

# Lemma 4.1.11: the section `f(u) = (1 − p)(u − t(u))` is sc-Fredholm

## The text

In the setting of Proposition 4.1.9: `t : U → U` an sc⁺-retraction of the relatively open
`U ⊆ C` onto `O ∋ 0`, `T₀O` in good position to `C` with a good (sc-)complement `Y`,
`E = T₀O ⊕ Y`, and `p : E → T₀O` the associated sc-projection.  On the local strong bundle
`π : U ◁ Y → U` the section `f(u) = (u, f(u))`, `f(u) = (1 − p)(u − t(u))`.

"**Lemma 4.1.11.** The section `f` is sc-Fredholm."

*Proof in the text*: regularizing because `t` is sc⁺ and `a = p(u)` is smooth; at a smooth point
`u`, no filling is needed (the retraction is the identity), the sc⁺-section
`s(v) = f(u) + (1 − p)[t(u) − t(u + v)]` gives `g − s = (1 − p)v`, and with `Y = B ⊕ W`, `W ⊆ C`,
`E = (T₀O ⊕ B) ⊕ W`, the germ `(a + b, w) ↦ b + w` is a basic germ.

## What is formalized

* `lemma_4_1_11`: for the data of Proposition 4.1.9, with `Y` an sc-complement
  (`E.IsScSplitting N Y`, the text's "good sc-complement") and `p` the projection onto
  `N = T₀O` along `Y`, the section `LocalBundle.sec f` of the local strong bundle
  `LocalBundle.bundle` (`U ◁ Y → U` over the M-polyfold `U`) is an **sc-Fredholm section in the
  sense of 2021 Definition 3.1.16** (`StrongBundle.IsScFredholmSection2021`): sc-smooth,
  regularizing, and an sc-Fredholm germ at every smooth point.  It holds on all of `U`, not
  only on a small neighbourhood of `0`.
* The germ at a smooth `e ∈ U` is taken in the chart centred at `e` (`LocalBundle.centred`):
  the filling is the principal part itself (`isFilling2021_of_R_eq_self`), the sc⁺-section is the
  text's `s`, lifted to `Y¹`, and `g − s = (1 − p)v` is conjugated to a basic germ by
  `isConjugateToBasicGerm_qOp`.

## Choices

* `hsplit : E.IsScSplitting N Y` is the text's "good **sc**-complement" (Definition 3.1.24 asks for
  an sc-complement; the project's `IsGoodComplement` records only the algebraic splitting and the
  `ε`-condition).  It makes `Y` an sc-Banach space, the fibre of `U ◁ Y`.

* `N ⊆ E_∞` and `dim N < ∞` are Lemma 4.1.7 (`GraphData.smooth`, `GraphData.finiteDimensional`).
* The regularity argument: `u = (1 − p)(u − t(u)) + t(u) + p(u − t(u))`, with `t(u) ∈ E_{m+1}` for
  `u ∈ U_m` (sc⁺) and `p(·) ∈ N ⊆ E_∞`.
-/

open Set Filter Topology Function

noncomputable section

namespace Polyfold

variable {E : ScBanach} {C : Set (E 0)}

/-- **2021 Lemma 4.1.11, p. 179** (preprint Lemma 4.10): in the setting of Proposition 4.1.9 — an
sc⁺-retraction `t : U → U` onto `O = t(U) ∋ 0` in the partial quadrant `C`, `N = T₀O` in good
position to `C` with the good sc-complement `Y` (`E = N ⊕ Y` an sc-splitting) and `p` the
projection onto `N` along `Y` — the section `f(u) = (u, (1 − p)(u − t(u)))` of the local strong
bundle `U ◁ Y → U` is **sc-Fredholm** (2021 Definition 3.1.16). -/
theorem lemma_4_1_11 (t : ScRetraction E C) (ht : t.IsScPlus) (h0 : (0 : E 0) ∈ t.retract)
    {N : Submodule ℝ (E 0)} (hN : (N : Set (E 0)) = tangentSpace E C t.retract 0)
    (hgood : IsInGoodPosition E C N) {Y : Submodule ℝ (E 0)} (hY : IsGoodComplement E C N Y)
    (hsplit : E.IsScSplitting N Y) (p : E 0 →L[ℝ] N) (hpN : ∀ n : N, p n = n)
    (hpY : ∀ y ∈ Y, p y = 0) :
    (LocalBundle.bundle (E.ofSubspace hsplit.2.1) t.relOpen
        ⟨0, t.retract_subset h0⟩).IsScFredholmSection2021 (LocalBundle.sec fun u : E 0 =>
        (⟨(u - t u) - p (u - t u), sub_p_mem hY.isCompl p hpN hpY _⟩ :
          (E.ofSubspace hsplit.2.1) 0)) := by
  classical
  let d : GraphData E C := ⟨t, ht, h0, N, hN, hgood, Y, hY, hsplit.2.1.1, p, hpN, hpY⟩
  have : FiniteDimensional ℝ N := d.finiteDimensional
  have hNs : N ≤ E.smooth := d.smooth
  have hYs := hsplit.2.1
  have hcompl := hY.isCompl
  set u₀ : t.U := ⟨0, t.retract_subset h0⟩
  set q := qOp hNs hYs hcompl p hpN hpY with hqdef
  set k : E 0 → (E.ofSubspace hYs) 0 := fun u =>
    (⟨(u - t u) - p (u - t u), sub_p_mem hcompl p hpN hpY _⟩ : (E.ofSubspace hYs) 0) with hkdef
  have hk : ∀ u, k u = q 0 (u - t u) := fun u =>
    Subtype.ext (qOp_zero_val hNs hYs hcompl p hpN hpY _).symm
  have hdom := t.relOpen.isScDomain
  have hksm : IsScSmooth t.U k := by
    refine (IsScSmooth.comp hdom (isScDomain_univ _) (q.isScSmooth (isScDomain_univ _))
      (IsScSmooth.sub hdom (isScSmooth_id hdom) t.isScSmooth) (mapsTo_univ _ _)).congr hdom
      fun u _ => (hk u).symm
  refine ⟨LocalBundle.isScSmoothSection_sec t.relOpen u₀ hksm, ?_, ?_⟩
  · -- regularizing
    intro m x hx hfx
    rw [LocalBundle.mem_levelSet_iff] at hx ⊢
    obtain ⟨-, ⟨z, hz⟩⟩ := (LocalBundle.mem_doubleLevel_iff t.relOpen u₀).1 hfx
    obtain ⟨xm, hxm⟩ := hx
    have htx : t x ∈ range (E.toBase (m + 1)) := by
      have := ht.mem_range_succ m (x := xm) (by rw [ScBanach.mem_lvlSet, hxm]; exact x.2)
      rwa [hxm] at this
    have hz' : E.toBase (m + 1) z.1 = ((x : E 0) - t x) - p ((x : E 0) - t x) :=
      (E.ofSubspaceScale_coe_toBase hYs.1 (m + 1) z).symm.trans (congrArg Subtype.val hz)
    obtain ⟨a, ha⟩ := htx
    obtain ⟨b, hb⟩ := (E.mem_smooth_iff.1 (hNs (p ((x : E 0) - t x)).2)) (m + 1)
    refine ⟨z.1 + a + b, ?_⟩
    rw [map_add, map_add, hz', ha, hb]
    abel
  · -- the germ at a smooth point
    intro x hx
    rw [LocalBundle.mem_smoothSet_iff] at hx
    set e : E 0 := (x : E 0) with hedef
    obtain ⟨n, W, T, hT⟩ := t.relOpen.isPartialQuadrant
    set c := LocalBundle.centred (F := E.ofSubspace hYs) t.relOpen u₀ hT hx with hcdef
    have heU : e ∈ t.U := x.2
    have h0c : (0 : E 0) ∈ c.U := LocalBundle.zero_mem_centred_U t.relOpen u₀ hT hx heU
    have hdomc := c.relOpen.isScDomain
    have hmaps : MapsTo (fun v : E 0 => v + e) c.U t.U := fun v hv =>
      LocalBundle.add_mem_of_mem_centred_U t.relOpen u₀ hT hx hv
    have hprinc : ∀ v : E 0, v ∈ c.U → (c.principal (LocalBundle.sec k) v : (E.ofSubspace hYs) 0) =
        k (v + e) := fun v hv =>
      LocalBundle.principal_centred t.relOpen u₀ hT hx k hv
    have hgsm : IsScSmooth c.U (c.principal (LocalBundle.sec k)) :=
      (IsScSmooth.comp hdomc hdom hksm (isScSmooth_add_const hx hdomc) hmaps).congr hdomc
        fun v hv => (hprinc v hv).symm
    -- the sc⁺-section `s(v) = (1 − p)(e − t(v + e))`, lifted to `Y¹`
    have hte : t e ∈ range (E.toBase 1) := ht.mem_range e heU
    have he1 : e ∈ range (E.toBase 1) := (E.mem_smooth_iff.1 hx) 1
    let s : E 0 → (E.ofSubspace hYs) 1 := fun v => q 1 (E.liftOne e - E.liftOne (t (v + e)))
    have hinner : IsScSmooth (E := E) (F := E.shift) c.U
        (fun v => E.liftOne e - E.liftOne (t (v + e))) := by
      have hc1 : IsScSmooth (E := E) (F := E.shift) c.U (fun _ => E.liftOne e) :=
        isScSmooth_const_of_smooth hdomc (by rw [E.toBase_liftOne he1]; exact hx)
      have hc2 : IsScSmooth (E := E) (F := E.shift) c.U
          ((E.liftOne ∘ t) ∘ (fun v : E 0 => v + e)) :=
        IsScSmooth.comp (G := E.shift) (g := E.liftOne ∘ t) (f := fun v : E 0 => v + e) hdomc hdom
          ht.isScSmooth_lift (isScSmooth_add_const hx hdomc) hmaps
      exact IsScSmooth.sub hdomc hc1 hc2
    have hs : IsScSmooth (E := E) (F := (E.ofSubspace hYs).shift) c.U s :=
      IsScSmooth.comp hdomc (isScDomain_univ _) (q.shiftOp.isScSmooth (isScDomain_univ _)) hinner
        (mapsTo_univ _ _)
    have hιs : ∀ v : E 0, v ∈ c.U → c.F.toBase 1 (s v) = q 0 (e - t (v + e)) := by
      intro v hv
      change (E.ofSubspace hYs).toBase 1 (q 1 _) = _
      rw [q.toBase_comm, map_sub, E.toBase_liftOne he1,
        E.toBase_liftOne (ht.mem_range _ (hmaps hv))]
    have hQc := c.relOpen.isPartialQuadrant.isQuadrantLike
    refine ⟨by rw [LocalBundle.mem_smoothSet_iff]; exact hx, c,
      LocalBundle.isChart_centred t.relOpen u₀ hT hx,
      LocalBundle.mem_centred_source t.relOpen u₀ hT hx rfl,
      LocalBundle.centred_apply_self t.relOpen u₀ hT hx rfl, h0c,
      c.principal (LocalBundle.sec k), s,
      isFilling2021_of_R_eq_self c.relOpen c.isRetraction
        (LocalBundle.centred_R_apply t.relOpen u₀ hT hx) h0c hgsm,
      ⟨ScNbhdGerm.ofSet c.relOpen.relOpen h0c, fun _ hv => hv,
        IsScSmooth.isScSmoothGerm hQc c.relOpen.relOpen h0c hs⟩, ?_, ?_⟩
    · refine ((hιs 0 h0c).trans ?_).trans (hprinc 0 h0c).symm
      rw [hk, zero_add]
    · refine (isConjugateToBasicGerm_qOp hNs hYs hcompl p hpN hpY c.relOpen h0c).congr
        fun v hv => ?_
      rw [hιs v hv, hprinc v hv, hk]
      exact (by rw [← map_sub]; congr 1; abel :
        q 0 v = q 0 (v + e - t (v + e)) - q 0 (e - t (v + e)))

end Polyfold
