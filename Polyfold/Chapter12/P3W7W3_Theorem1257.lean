import Polyfold.Chapter12.P3W7W3_OrbitHomeo

/-!
Hofer–Wysocki–Zehnder, *Polyfold and Fredholm Theory* (Springer 2021), Chapter 12, §12.5,
pp. 595–597: **Theorem 12.5.7** (2017: Theorem 12.12) for a representative `W ←Φ₁– V –Φ₂→ W'`,
with the topology.

* `theorem_12_5_7_one_homeo_hyp`: **(1)**: homeomorphisms `|O_f| ≃ₜ |O_{f'}|` and
  `|X_∞| ≃ₜ |X'_∞|` commuting with `|σ|`, `|σ'|`, the maps of the diagram (Part I's topology on
  `O_f`, the topology of Theorem 2.3.10 on `X_∞`, quotient topologies).
* `theorem_12_5_7_two_book_hyp`: **(2)** as printed: an orientation `o` of `f` in the sense of
  Definition 12.5.4 (continuous section of `σ` for Part I's topology, invariant under morphisms)
  has exactly one push-forward `o'` corresponding to `o` over `V`, and `o'` is an orientation of
  `f'` in the sense of Definition 12.5.4.
* `theorem_12_5_7_one_homeo`, `theorem_12_5_7_two_book`: the same without instance arguments.

Hypotheses: Part I's (tame object M-polyfolds with bump functions, tame germ data, as in
`theorem_12_5_3_hyp`) for `X`, `X'` and `V`, and the standing `sc⁺`-sections through points.
-/

set_option maxSynthPendingDepth 3

open Set Function Topology Filter

noncomputable section

namespace Polyfold

open StrongRetr

universe u

section Diagram

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type u} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]
  {Obj'' Mor'' : Type u} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor''] {X'' : EpGroupoid Obj'' Mor''}
  {W'' : Type u} [TopologicalSpace W''] [T2Space W''] [ParacompactSpace W''] {P'' : W'' → Obj''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]
  {B'' : StrongBundle X''.PObj P''} [ParacompactSpace (pullbackSpace P'' X''.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {E'' : EpStrongBundle X'' B''}
  {ϕ₁ : EpFunctor X'' X} {Φ₁ : EpFunctor E''.toEpGroupoid E.toEpGroupoid}
  {ϕ₂ : EpFunctor X'' X'} {Φ₂ : EpFunctor E''.toEpGroupoid E'.toEpGroupoid}
  (h₁ : E''.IsStrongBundleEquivalence E ϕ₁ Φ₁) (h₂ : E''.IsStrongBundleEquivalence E' ϕ₂ Φ₂)
  {f : Obj → W} {f' : Obj' → W'} {f'' : Obj'' → W''} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hF'' : E''.IsScFredholmSectionFunctor f'')
  (hpb₁ : f'' = h₁.pullback f) (hpb₂ : f'' = h₂.pullback f')
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)
  (hsec'' : B''.HasScPlusSectionsThrough)
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj)]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P (Prod.snd : (Fin n → ℝ) × Obj → Obj))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P (Prod.snd : (Fin n → ℝ) × Obj → Obj))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj) → (Fin n → ℝ) × Obj))]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj')]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P' (Prod.snd : (Fin n → ℝ) × Obj' → Obj'))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj'))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P' (Prod.snd : (Fin n → ℝ) × Obj' → Obj'))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj') → (Fin n → ℝ) × Obj'))]
  [∀ n : ℕ, ParacompactSpace ((Fin n → ℝ) × Obj'')]
  [∀ n : ℕ, ParacompactSpace (pullbackSpace P'' (Prod.snd : (Fin n → ℝ) × Obj'' → Obj''))]
  [∀ k n : ℕ, ParacompactSpace ((Fin k → ℝ) × ((Fin n → ℝ) × Obj''))]
  [∀ k n : ℕ, ParacompactSpace (pullbackSpace
    (pullbackProj P'' (Prod.snd : (Fin n → ℝ) × Obj'' → Obj''))
    (Prod.snd : (Fin k → ℝ) × ((Fin n → ℝ) × Obj'') → (Fin n → ℝ) × Obj''))]
  (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions) (hfT : B.IsScFredholmSectionTame f)
  (hX' : X'.PObj.IsTame) (hbump' : X'.PObj.AdmitsBumpFunctions)
  (hfT' : B'.IsScFredholmSectionTame f') (hX'' : X''.PObj.IsTame)
  (hbump'' : X''.PObj.AdmitsBumpFunctions) (hfT'' : B''.IsScFredholmSectionTame f'')

include hX'' hbump'' hfT'' in
/-- **Theorem 12.5.7 (1)**, p. 595 (2017: Theorem 12.12 (1)), with the topology and Part I's
hypotheses, for a representative `W ←Φ₁– V –Φ₂→ W'`: there are homeomorphisms
`|O_f| ≃ₜ |O_{f'}|` and `|X_∞| ≃ₜ |X'_∞|` with `|σ'| ∘ F = G ∘ |σ|`; they are the maps of the
diagram, `F ∘ |Φ₁|_* = |Φ₂|_*` and `G ∘ |ϕ₁| = |ϕ₂|`.  The topology of `O_f` is Part I's
(Theorem 12.5.3), those of `|O_f|`, `|X_∞|` the quotient topologies. -/
theorem theorem_12_5_7_one_homeo_hyp :
    letI : TopologicalSpace (OrSpace f hF.2) := orTopology (orLocalTransport hX hbump hfT hsec)
    letI : TopologicalSpace (OrSpace f' hF'.2) :=
      orTopology (orLocalTransport hX' hbump' hfT' hsec')
    ∃ (F : Quot (E.OrRel hF hsec) ≃ₜ Quot (E'.OrRel hF' hsec'))
      (G : Quot X.SmoothRel ≃ₜ Quot X'.SmoothRel),
      (∀ c, E'.orbitProj hF' hsec' (F c) = G (E.orbitProj hF hsec c)) ∧
      (∀ c, F (h₁.orbitOrMap hF'' hF hpb₁ hsec'' hsec c) =
        h₂.orbitOrMap hF'' hF' hpb₂ hsec'' hsec' c) ∧
      ∀ v, G (h₁.smoothOrbitMap v) = h₂.smoothOrbitMap v := by
  let := orTopology (orLocalTransport hX hbump hfT hsec)
  let := orTopology (orLocalTransport hX' hbump' hfT' hsec')
  let := orTopology (orLocalTransport hX'' hbump'' hfT'' hsec'')
  set F₁ := h₁.orbitOrHomeo hF'' hF hpb₁ hsec'' hsec hX'' hbump'' hfT'' hX hbump hfT
  set F₂ := h₂.orbitOrHomeo hF'' hF' hpb₂ hsec'' hsec' hX'' hbump'' hfT'' hX' hbump' hfT'
  set G₁ := h₁.smoothOrbitHomeo
  set G₂ := h₂.smoothOrbitHomeo
  refine ⟨F₁.symm.trans F₂, G₁.symm.trans G₂, fun c => ?_, fun c => ?_, fun v => ?_⟩
  · obtain ⟨d, rfl⟩ := F₁.surjective c
    rw [Homeomorph.trans_apply, Homeomorph.symm_apply_apply, Homeomorph.trans_apply]
    change E'.orbitProj hF' hsec' (h₂.orbitOrMap hF'' hF' hpb₂ hsec'' hsec' d) =
      G₂ (G₁.symm (E.orbitProj hF hsec (h₁.orbitOrMap hF'' hF hpb₁ hsec'' hsec d)))
    rw [h₂.orbitProj_orbitOrMap, h₁.orbitProj_orbitOrMap]
    change _ = G₂ (G₁.symm (G₁ _))
    rw [Homeomorph.symm_apply_apply]
    rfl
  · change F₂ (F₁.symm (F₁ c)) = _
    rw [Homeomorph.symm_apply_apply]
    rfl
  · change G₂ (G₁.symm (G₁ v)) = _
    rw [Homeomorph.symm_apply_apply]
    rfl

include hX'' hbump'' hfT'' in
/-- **Theorem 12.5.7 (2)**, p. 595 (2017: Theorem 12.12 (2)), as printed, with Part I's
hypotheses, for a representative `W ←Φ₁– V –Φ₂→ W'`: if `o` is an orientation of `f`
(Definition 12.5.4: `x ↦ (x, o_x)` continuous for Part I's topology of `O_f`, and invariant under
morphisms), there is exactly one invariant `o'` corresponding to `o` over `V`
(`orEqv₂ o'_{ϕ₂ v} = orEqv₁ o_{ϕ₁ v}`), and `o'` is an orientation of `f'` (Definition 12.5.4).
The continuity is moved between Definition 12.5.4 and `IsContOrOn` over all of `X` by Part I's
`continuous_orSec_iff`. -/
theorem theorem_12_5_7_two_book_hyp {o : ∀ a (hs : a ∈ X.PObj.smoothSet), Orx f hF.2 a hs}
    (ho : E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hfT hsec)) o) :
    ∃! o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), Orx f' hF'.2 x hs,
      E'.definition_12_5_4 hF' hsec' (orTopology (orLocalTransport hX' hbump' hfT' hsec')) o' ∧
        ∀ v (hv : v ∈ X''.PObj.smoothSet),
          h₂.orEqv hF'' hF' hpb₂ hsec'' hsec' v hv (o' (ϕ₂.obj v) (h₂.smooth_obj hv)) =
            h₁.orEqv hF'' hF hpb₁ hsec'' hsec v hv (o (ϕ₁.obj v) (h₁.smooth_obj hv)) := by
  have h2 := isTwoPointed_of_hasScPlusSectionsThrough hfT hsec
  have h2' := isTwoPointed_of_hasScPlusSectionsThrough hfT' hsec'
  have hoc : IsContOrOn (orLocalTransport hX hbump hfT hsec) univ o :=
    (continuous_orSec_iff (orLocalTransport hX hbump hfT hsec) h2 o).1 ho.1
  obtain ⟨o', ⟨hinv, hcorr, hc'⟩, huniq⟩ := theorem_12_5_7_two_hyp h₁ h₂ hF hF' hF'' hpb₁ hpb₂
    hsec hsec' hsec'' hX hbump hfT hX' hbump' hfT' hX'' hbump'' hfT'' ho.2 hoc
  refine ⟨o', ⟨⟨(continuous_orSec_iff (orLocalTransport hX' hbump' hfT' hsec') h2' o').2 hc',
    hinv⟩, hcorr⟩, fun o'' ⟨⟨hc'', hinv''⟩, hcorr''⟩ => huniq o'' ⟨hinv'', hcorr'', ?_⟩⟩
  exact (continuous_orSec_iff (orLocalTransport hX' hbump' hfT' hsec') h2' o'').1 hc''

end Diagram

section DiagramWitness

variable {Obj Mor : Type u} [TopologicalSpace Obj] [T2Space Obj] [ParacompactSpace Obj]
  [TopologicalSpace Mor] [T2Space Mor] [ParacompactSpace Mor] {X : EpGroupoid Obj Mor}
  {W : Type u} [TopologicalSpace W] [T2Space W] [ParacompactSpace W] {P : W → Obj}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})] {B : StrongBundle X.PObj P}
  [ParacompactSpace (pullbackSpace P X.src)]
  {Obj' Mor' : Type u} [TopologicalSpace Obj'] [T2Space Obj'] [ParacompactSpace Obj']
  [TopologicalSpace Mor'] [T2Space Mor'] [ParacompactSpace Mor'] {X' : EpGroupoid Obj' Mor'}
  {W' : Type u} [TopologicalSpace W'] [T2Space W'] [ParacompactSpace W'] {P' : W' → Obj'}
  [∀ x, AddCommGroup (P' ⁻¹' {x})] [∀ x, Module ℝ (P' ⁻¹' {x})] {B' : StrongBundle X'.PObj P'}
  [ParacompactSpace (pullbackSpace P' X'.src)]
  {Obj'' Mor'' : Type u} [TopologicalSpace Obj''] [T2Space Obj''] [ParacompactSpace Obj'']
  [TopologicalSpace Mor''] [T2Space Mor''] [ParacompactSpace Mor''] {X'' : EpGroupoid Obj'' Mor''}
  {W'' : Type u} [TopologicalSpace W''] [T2Space W''] [ParacompactSpace W''] {P'' : W'' → Obj''}
  [∀ x, AddCommGroup (P'' ⁻¹' {x})] [∀ x, Module ℝ (P'' ⁻¹' {x})]
  {B'' : StrongBundle X''.PObj P''} [ParacompactSpace (pullbackSpace P'' X''.src)]
  {E : EpStrongBundle X B} {E' : EpStrongBundle X' B'} {E'' : EpStrongBundle X'' B''}
  {ϕ₁ : EpFunctor X'' X} {Φ₁ : EpFunctor E''.toEpGroupoid E.toEpGroupoid}
  {ϕ₂ : EpFunctor X'' X'} {Φ₂ : EpFunctor E''.toEpGroupoid E'.toEpGroupoid}
  (h₁ : E''.IsStrongBundleEquivalence E ϕ₁ Φ₁) (h₂ : E''.IsStrongBundleEquivalence E' ϕ₂ Φ₂)
  {f : Obj → W} {f' : Obj' → W'} {f'' : Obj'' → W''} (hF : E.IsScFredholmSectionFunctor f)
  (hF' : E'.IsScFredholmSectionFunctor f') (hF'' : E''.IsScFredholmSectionFunctor f'')
  (hpb₁ : f'' = h₁.pullback f) (hpb₂ : f'' = h₂.pullback f')
  (hsec : B.HasScPlusSectionsThrough) (hsec' : B'.HasScPlusSectionsThrough)
  (hsec'' : B''.HasScPlusSectionsThrough)
  (hX : X.PObj.IsTame) (hbump : X.PObj.AdmitsBumpFunctions) (hfT : B.IsScFredholmSectionTame f)
  (hX' : X'.PObj.IsTame) (hbump' : X'.PObj.AdmitsBumpFunctions)
  (hfT' : B'.IsScFredholmSectionTame f') (hX'' : X''.PObj.IsTame)
  (hbump'' : X''.PObj.AdmitsBumpFunctions) (hfT'' : B''.IsScFredholmSectionTame f'')

include hX'' hbump'' hfT'' in
/-- **Theorem 12.5.7 (1)**, p. 595 (2017: Theorem 12.12 (1)), with the topology, Part I's
hypotheses and no instance arguments (they hold for the metrizable spaces of the text); as
`theorem_12_5_7_one_homeo_hyp`. -/
theorem theorem_12_5_7_one_homeo :
    haveI := paracompactSpace_rn_prod X.PObj
    haveI := paracompactSpace_rn_pullback B
    haveI := paracompactSpace_rn_rn_prod X.PObj
    haveI := paracompactSpace_rn_rn_pullback B
    haveI := paracompactSpace_rn_prod X'.PObj
    haveI := paracompactSpace_rn_pullback B'
    haveI := paracompactSpace_rn_rn_prod X'.PObj
    haveI := paracompactSpace_rn_rn_pullback B'
    letI : TopologicalSpace (OrSpace f hF.2) := orTopology (orLocalTransport hX hbump hfT hsec)
    letI : TopologicalSpace (OrSpace f' hF'.2) :=
      orTopology (orLocalTransport hX' hbump' hfT' hsec')
    ∃ (F : Quot (E.OrRel hF hsec) ≃ₜ Quot (E'.OrRel hF' hsec'))
      (G : Quot X.SmoothRel ≃ₜ Quot X'.SmoothRel),
      (∀ c, E'.orbitProj hF' hsec' (F c) = G (E.orbitProj hF hsec c)) ∧
      (∀ c, F (h₁.orbitOrMap hF'' hF hpb₁ hsec'' hsec c) =
        h₂.orbitOrMap hF'' hF' hpb₂ hsec'' hsec' c) ∧
      ∀ v, G (h₁.smoothOrbitMap v) = h₂.smoothOrbitMap v := by
  have := paracompactSpace_rn_prod X.PObj
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_rn_prod X.PObj
  have := paracompactSpace_rn_rn_pullback B
  have := paracompactSpace_rn_prod X'.PObj
  have := paracompactSpace_rn_pullback B'
  have := paracompactSpace_rn_rn_prod X'.PObj
  have := paracompactSpace_rn_rn_pullback B'
  have := paracompactSpace_rn_prod X''.PObj
  have := paracompactSpace_rn_pullback B''
  have := paracompactSpace_rn_rn_prod X''.PObj
  have := paracompactSpace_rn_rn_pullback B''
  exact theorem_12_5_7_one_homeo_hyp h₁ h₂ hF hF' hF'' hpb₁ hpb₂ hsec hsec' hsec'' hX hbump hfT
    hX' hbump' hfT' hX'' hbump'' hfT''

include hX'' hbump'' hfT'' in
/-- **Theorem 12.5.7 (2)**, p. 595 (2017: Theorem 12.12 (2)), as printed, with Part I's
hypotheses and no instance arguments; as `theorem_12_5_7_two_book_hyp`. -/
theorem theorem_12_5_7_two_book {o : ∀ a (hs : a ∈ X.PObj.smoothSet), Orx f hF.2 a hs} :
    haveI := paracompactSpace_rn_prod X.PObj
    haveI := paracompactSpace_rn_pullback B
    haveI := paracompactSpace_rn_rn_prod X.PObj
    haveI := paracompactSpace_rn_rn_pullback B
    haveI := paracompactSpace_rn_prod X'.PObj
    haveI := paracompactSpace_rn_pullback B'
    haveI := paracompactSpace_rn_rn_prod X'.PObj
    haveI := paracompactSpace_rn_rn_pullback B'
    E.definition_12_5_4 hF hsec (orTopology (orLocalTransport hX hbump hfT hsec)) o →
    ∃! o' : ∀ x (hs : x ∈ X'.PObj.smoothSet), Orx f' hF'.2 x hs,
      E'.definition_12_5_4 hF' hsec' (orTopology (orLocalTransport hX' hbump' hfT' hsec')) o' ∧
        ∀ v (hv : v ∈ X''.PObj.smoothSet),
          h₂.orEqv hF'' hF' hpb₂ hsec'' hsec' v hv (o' (ϕ₂.obj v) (h₂.smooth_obj hv)) =
            h₁.orEqv hF'' hF hpb₁ hsec'' hsec v hv (o (ϕ₁.obj v) (h₁.smooth_obj hv)) := by
  have := paracompactSpace_rn_prod X.PObj
  have := paracompactSpace_rn_pullback B
  have := paracompactSpace_rn_rn_prod X.PObj
  have := paracompactSpace_rn_rn_pullback B
  have := paracompactSpace_rn_prod X'.PObj
  have := paracompactSpace_rn_pullback B'
  have := paracompactSpace_rn_rn_prod X'.PObj
  have := paracompactSpace_rn_rn_pullback B'
  have := paracompactSpace_rn_prod X''.PObj
  have := paracompactSpace_rn_pullback B''
  have := paracompactSpace_rn_rn_prod X''.PObj
  have := paracompactSpace_rn_rn_pullback B''
  exact theorem_12_5_7_two_book_hyp h₁ h₂ hF hF' hF'' hpb₁ hpb₂ hsec hsec' hsec'' hX hbump hfT
    hX' hbump' hfT' hX'' hbump'' hfT''

end DiagramWitness

end Polyfold
