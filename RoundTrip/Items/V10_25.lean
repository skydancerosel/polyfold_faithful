import Polyfold
import RoundTrip.Check
import RoundTrip.Blind.V10_25

/-! Round trip for V10_25 (2021 Proposition 10.4.3 = 2017 Proposition 10.8: if `|Φ| = |Ψ|`, then
`Φ_* f = Ψ_* f` for every sc-smooth section functor `f`).

`A` (universes at `0`) is the conjunction of the types of `EpStrongBundle.proposition_10_4_3`
(for `f ∈ Γ(P, μ)`) and `IsStrongBundleEquivalence.pushforward_eq_of_orbitMap_eq` (the same for
every functorial section `f`, sc-smooth or not).

`B` uses its own push-forward `pushB` (a `Classical.choose` of some `(x, σ : ϕ(x) → x')`), where
the project's `pushforward` uses the fixed choice `preObj`/`preMor`.  The bridge `pushB_eq`: for a
functorial section `f`, `pushB E' ϕ Φ.obj f = hΦ.pushforward f`, by the project's (10.22)
`pushforward_eq` (independence of the choice; not an item theorem).

* `A_to_B`: `pushB_eq` twice and `proposition_10_4_3`.
* `B_to_A`: `proposition_10_4_3` from `B` and `pushB_eq`.  The second conjunct (all functorial
  sections, no sc-smoothness) is not a consequence of `B` (which speaks of `Γ(P, μ)` only); it is
  re-proved outright below (`pushforward_eq_of_orbitMap_eq'`, the project's proof, from non-item
  lemmas). -/

namespace RoundTrip.V10_25
open Polyfold Set Function

/-- The project's statement (universes at `0`). -/
def A1 : Prop := type_of% @Polyfold.EpStrongBundle.proposition_10_4_3.{0}
def A2 : Prop :=
  type_of% @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_eq_of_orbitMap_eq.{0}

def A : Prop := A1 ∧ A2

theorem A_holds : A :=
  ⟨@Polyfold.EpStrongBundle.proposition_10_4_3.{0},
    @Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_eq_of_orbitMap_eq.{0}⟩

section Bridge

variable {Obj Mor : Type} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'}

/-- `B`'s push-forward is the project's on functorial sections (by (10.22), `pushforward_eq`). -/
theorem pushB_eq {ϕ : EpFunctor X X'} {Φ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (h : E.IsStrongBundleEquivalence E' ϕ Φ) {f : Obj → W} (hf : IsSection P f)
    (hfun : E.IsFunctorialSection hf) : pushB E' ϕ Φ.obj f = h.pushforward f := by
  funext x'
  have hex : ∃ p : Obj × Mor', X'.src p.2 = ϕ.obj p.1 ∧ X'.tgt p.2 = x' ∧
      P' (Φ.obj (f p.1)) = X'.src p.2 :=
    ⟨(h.preObj x', h.preMor x'), h.src_preMor x', h.tgt_preMor x',
      by rw [h.covers, hf, h.src_preMor]⟩
  unfold pushB
  rw [dif_pos hex, h.pushforward_eq hf hfun hex.choose_spec.1 hex.choose_spec.2.1]

/-- `pushforward_eq_of_orbitMap_eq`, re-proved outright (the project's proof, non-item lemmas). -/
theorem pushforward_eq_of_orbitMap_eq' {ϕ ψ : EpFunctor X X'}
    {Φ Ψ : EpFunctor E.toEpGroupoid E'.toEpGroupoid}
    (hΦ : E.IsStrongBundleEquivalence E' ϕ Φ)
    (hΨ : E.IsStrongBundleEquivalence E' ψ Ψ) (hΦΨ : Φ.orbitMap = Ψ.orbitMap) {f : Obj → W}
    (hf : IsSection P f) (hfun : E.IsFunctorialSection hf) :
    hΦ.pushforward f = hΨ.pushforward f := by
  funext x'
  obtain ⟨⟨⟨τ, w'⟩, hq⟩, hq2, hqμ⟩ :=
    EpStrongBundle.exists_μ_eq_of_orbitMap_eq hΦΨ (f (hΦ.preObj x'))
  change w' = _ at hq2
  subst hq2
  have hq' : P' (Φ.obj (f (hΦ.preObj x'))) = X'.src τ := hq
  have hsτ : X'.src τ = ϕ.obj (hΦ.preObj x') := by rw [← hq', hΦ.covers, hf]
  have htτ : X'.tgt τ = ψ.obj (hΦ.preObj x') :=
    (E'.P_μ ⟨(τ, Φ.obj (f (hΦ.preObj x'))), hq⟩).symm.trans (by rw [hqμ, hΨ.covers, hf])
  have hc : X'.src (hΦ.preMor x') = X'.tgt (X'.inv τ) := by
    rw [X'.tgt_inv, hsτ, hΦ.src_preMor]
  have hc' : X'.src (X'.comp (hΦ.preMor x') (X'.inv τ)) = X'.tgt τ := by
    rw [X'.src_comp _ _ hc, X'.src_inv]
  have hs : X'.src (X'.comp (hΦ.preMor x') (X'.inv τ)) = ψ.obj (hΦ.preObj x') := hc'.trans htτ
  have ht : X'.tgt (X'.comp (hΦ.preMor x') (X'.inv τ)) = x' := by
    rw [X'.tgt_comp _ _ hc, hΦ.tgt_preMor]
  have hρ : X'.comp (X'.comp (hΦ.preMor x') (X'.inv τ)) τ = hΦ.preMor x' := by
    have := GroupoidStr.comp_inv_cancel_right (G := X'.toGroupoidStr) (φ := X'.inv τ)
      (ψ := hΦ.preMor x') hc
    rwa [GroupoidStr.inv_inv] at this
  rw [hΨ.pushforward_eq hf hfun hs ht, hΦ.pushforward_def hf]
  symm
  have e : Ψ.obj (f (hΦ.preObj x')) = E'.μ ⟨(τ, Φ.obj (f (hΦ.preObj x'))), hq⟩ := hqμ.symm
  exact (E'.μ_mk_congr rfl e _ _).trans
    ((E'.μ_comp _ _ _ hq hc').symm.trans (E'.μ_mk_congr hρ rfl _ _))

end Bridge

theorem A_to_B : A → B := by
  rintro ⟨h103, -⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
    E E' ϕ ψ Φ Ψ hΦ hΨ hΦΨ f hf
  obtain ⟨hs, hfun⟩ := hf
  rw [pushB_eq hΦ hs.1 hfun, pushB_eq hΨ hs.1 hfun]
  exact h103 hΦ hΨ hΦΨ ⟨hs, hfun⟩

theorem B_to_A : B → A := by
  intro hB
  refine ⟨?_, @pushforward_eq_of_orbitMap_eq'⟩
  intro Obj Mor _ _ _ _ _ _ X W _ _ _ P _ _ B _ Obj' Mor' _ _ _ _ _ _ X' W' _ _ _ P' _ _ B' _
    E E' ϕ ψ Φ Ψ hΦ hΨ hΦΨ f hf
  have key := hB Obj Mor X W P B Obj' Mor' X' W' P' B' E E' ϕ ψ Φ Ψ hΦ hΨ hΦΨ f hf
  obtain ⟨hs, hfun⟩ := hf
  rwa [pushB_eq hΦ hs.1 hfun, pushB_eq hΨ hs.1 hfun] at key

#rt_check RoundTrip.V10_25.A_to_B [Polyfold.EpStrongBundle.proposition_10_4_3,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_eq_of_orbitMap_eq]
#rt_check RoundTrip.V10_25.B_to_A [Polyfold.EpStrongBundle.proposition_10_4_3,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_eq_of_orbitMap_eq]
#rt_overlap RoundTrip.V10_25.B_to_A [Polyfold.EpStrongBundle.proposition_10_4_3,
  Polyfold.EpStrongBundle.IsStrongBundleEquivalence.pushforward_eq_of_orbitMap_eq]

end RoundTrip.V10_25
