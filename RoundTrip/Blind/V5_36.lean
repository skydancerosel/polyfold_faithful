import Polyfold
/-! Blind formalization of V5_36 (the text's §5.3, proof of Theorem 5.18, p. 178).

Text: for `F(λ, y) = f(y) + Σᵢ λᵢ tᵢ(y)` on `ℝᵐ ⊕ X` and `x ∈ S_f`: (i) `F'(0, x)` is surjective;
(ii) `ker F'(0, x)` is transversal to `ℝᵐ ⊕ T^R_xX`.  "Adding more sections, the properties
(i)–(ii) will still hold"; "we take a linear subspace `L` complementing `T^R_xX` in `T_xX` and add
sections, which at `x` span the image `f'(x)L`."

Choices:
- This item is a definition (properties (i)–(ii)) plus three claims of the proof.  B is the
  conjunction of:
  (1) the project's `StrongBundleChart.IsParamGP` (properties (i)–(ii) in a strong bundle chart
      centred at the point, checked with `#print`) is my `ParamGPB` below, at a zero `y` of `g`, in
      a chart centred at `y`, for every presentation `T` of the partial quadrant;
  (2) monotonicity: if (i)–(ii) hold for `t₁, …, t_m`, they hold for `t₁, …, t_m, s₁, …, s_k`
      (`Fin.append`);
  (3) a finite-dimensional linear subspace `L` complementing `T^R_xX` in `T_xX` exists;
  (4) if (i) holds for `t₁, …, t_m` and the added sections `s₁, …, s_k` at `x` span the image
      `f'(x)L` of a complement `L` of `T^R_xX` in `T_xX`, then (i)–(ii) hold for the enlarged
      family (this is what "we take `L` … and add sections" achieves; (i) is achieved first, by
      sections spanning a complement of the range, in the preceding sentences of the proof).
- Setting: `X Y : Type` (universe 0, as asked); `PX : MPolyfold X`, `P : Y → X` with the
  fibrewise linear structure as instances on the fibres, `Bd : StrongBundle PX P`, as in
  `RoundTrip/Blind/V5_38.lean` (Theorem 5.18).  The claims are pointwise linear algebra, so I put
  no hypothesis on the bundle or on the sections (no tameness, no sc⁺-condition on the `tᵢ`, no
  sc-Fredholm condition on `f`); the point `x` is a zero of `f` (`IsZeroAt`) where the text has it
  so (in (1) and (4)).  Writing `g` for the section `f` of the text.
- Everything is read in a strong bundle chart `Φ` of `P` around `x` (`Bd.IsChart c`, compatible
  with the atlas), as in `RoundTrip/Blind/V5_23.lean`, `V5_31.lean`: `φ(x)` lifts to `z ∈ E_1`;
  `T_xX ≅ T_zO = Dr(z)E` (`TO`, `r = StrongRetr.r R`); `Y_x ≅ K_{φ(x)} = {k | (φ(x), k) ∈ K}`;
  `f'(x) ≅ D(f̂ ∘ r)(z)|_{T_zO}` (`Dg`); the value `tᵢ(x)` is the principal part `t̂ᵢ(φ(x)) ∈ F`;
  `T^R_xX ≅ T_zO ∩ E_{φ(x)}`, `E_p = minimalSubspaceWith T p` for a presentation
  `T : E ≅ ℝⁿ ⊕ W`, `C = T⁻¹([0, ∞)ⁿ ⊕ W)` (B quantifies over all presentations).
- `F'(0, x) : ℝᵐ ⊕ T_xX → Y_x` is `(a, u) ↦ f'(x)u + Σᵢ aᵢ tᵢ(x)` (the derivative of
  `F(λ, y) = f(y) + Σ λᵢ tᵢ(y)` at `(0, x)`, `f(x) = 0`).  (i): every `k ∈ K_{φ(x)}` is
  `F'(0, x)(a, u)` for some `a ∈ ℝᵐ`, `u ∈ T_zO`.  (ii) "transversal": the subspaces
  `ker F'(0, x)` and `ℝᵐ ⊕ T^R_xX` of `ℝᵐ ⊕ T_xX` add up to the whole space: every `(b, w)` is
  `(a, u) + (b', r)` with `F'(0, x)(a, u) = 0` and `r ∈ T^R`.
- "a linear subspace `L` complementing `T^R_xX` in `T_xX`": `L ⊆ T_zO`, `L ∩ T^R = 0`,
  `L + T^R = T_zO` (algebraic complement); in (3) also finite-dimensional (so that finitely many
  sections suffice; `T^R_xX` has finite codimension).  "sections which at `x` span the image
  `f'(x)L`": `span{ŝⱼ(φ(x))} = Dg(L)`.
- Nothing looks false to me.
-/
namespace RoundTrip.V5_36
open Polyfold

section
variable {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] {PX : MPolyfold X}
  {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] {P : Y → X}
  [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]

/-- The tangent space `T_zO = Dr(z)E` of the retract `O = r(U)` at `z ∈ O_1`. -/
noncomputable def TO (c : StrongBundleChart PX P) (z : c.φ.model.E.lvl 1) :
    Submodule ℝ (c.φ.model.E.lvl 0) :=
  LinearMap.range (scDeriv c.U (StrongRetr.r c.R) z).toLinearMap

/-- `D(f̂ ∘ r)(z) : E → F`; on `T_zO` it is the linearization at a zero. -/
noncomputable def Dg (c : StrongBundleChart PX P) (g : X → Y) (z : c.φ.model.E.lvl 1) :
    c.φ.model.E.lvl 0 →L[ℝ] c.F.lvl 0 :=
  scDeriv c.U (c.principal g ∘ StrongRetr.r c.R) z

/-- The reduced tangent space `T^R = T_zO ∩ E_{φ(x)}` for the presentation `T`. -/
noncomputable def TR (c : StrongBundleChart PX P) (z : c.φ.model.E.lvl 1) (x : X) {n : ℕ}
    {W : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)) :
    Submodule ℝ (c.φ.model.E.lvl 0) :=
  TO c z ⊓ minimalSubspaceWith T (c.φ.toPartialEquiv x)

/-- `F'(0, x)(a, u) = f'(x)u + Σᵢ aᵢ tᵢ(x)`, in the chart. -/
noncomputable def DF (c : StrongBundleChart PX P) (g : X → Y) {m : ℕ} (t : Fin m → X → Y) (x : X)
    (z : c.φ.model.E.lvl 1) (a : Fin m → ℝ) (u : c.φ.model.E.lvl 0) : c.F.lvl 0 :=
  Dg c g z u + ∑ i, a i • c.principal (t i) (c.φ.toPartialEquiv x)

/-- Property (i): `F'(0, x) : ℝᵐ ⊕ T_xX → Y_x` is surjective. -/
def PropI (c : StrongBundleChart PX P) (g : X → Y) {m : ℕ} (t : Fin m → X → Y) (x : X)
    (z : c.φ.model.E.lvl 1) : Prop :=
  ∀ k : c.F.lvl 0, (c.φ.toPartialEquiv x, k) ∈ c.K →
    ∃ a : Fin m → ℝ, ∃ u ∈ TO c z, DF c g t x z a u = k

/-- Property (ii): `ker F'(0, x) + (ℝᵐ ⊕ T^R_xX) = ℝᵐ ⊕ T_xX`. -/
def PropII (c : StrongBundleChart PX P) (g : X → Y) {m : ℕ} (t : Fin m → X → Y) (x : X)
    (z : c.φ.model.E.lvl 1) {n : ℕ} {W : ScBanach}
    (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)) : Prop :=
  ∀ b : Fin m → ℝ, ∀ w ∈ TO c z,
    ∃ a : Fin m → ℝ, ∃ u ∈ TO c z, DF c g t x z a u = 0 ∧
      ∃ b' : Fin m → ℝ, ∃ r ∈ TR c z x T, b = a + b' ∧ w = u + r

/-- Properties (i)–(ii) at `(0, x)` for the family `t`, in the chart `c` with presentation `T`. -/
def ParamGPB (c : StrongBundleChart PX P) (g : X → Y) {m : ℕ} (t : Fin m → X → Y) {n : ℕ}
    {W : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)) (x : X) : Prop :=
  ∃ z : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z = c.φ.toPartialEquiv x ∧
    PropI c g t x z ∧ PropII c g t x z T

/-- `L` complements `T^R` in `T_zO`. -/
def IsComplementTR (c : StrongBundleChart PX P) (z : c.φ.model.E.lvl 1) (x : X) {n : ℕ}
    {W : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W))
    (L : Submodule ℝ (c.φ.model.E.lvl 0)) : Prop :=
  L ≤ TO c z ∧ Disjoint L (TR c z x T) ∧ L ⊔ TR c z x T = TO c z

end

/-- Properties (i)–(ii) of the proof of Theorem 5.18: the project's `IsParamGP` is the text's
notion; adding sections preserves (i)–(ii); a finite-dimensional complement `L` of `T^R_xX` in
`T_xX` exists; and adding to a family with (i) sections spanning `f'(x)L` gives (i)–(ii). -/
def B : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [T2Space X] [ParacompactSpace X] (PX : MPolyfold X)
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [ParacompactSpace Y] (P : Y → X)
    [∀ x, AddCommGroup (P ⁻¹' {x})] [∀ x, Module ℝ (P ⁻¹' {x})]
    (Bd : StrongBundle PX P),
    -- (1) the definition, in a chart centred at the zero `y`
    (∀ (g : X → Y) (y : X) (c : StrongBundleChart PX P), Bd.IsChart c → y ∈ c.φ.source →
      c.φ.toPartialEquiv y = 0 → IsZeroAt P g y →
      ∀ {m : ℕ} (t : Fin m → X → Y) {n : ℕ} {W : ScBanach}
        (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
        c.φ.model.C = T.lvl 0 ⁻¹' quadrant n W 0 →
          (c.IsParamGP g t T ↔ ParamGPB c g t T y)) ∧
    -- (2) adding more sections, (i)–(ii) still hold
    (∀ (g : X → Y) (x : X) (c : StrongBundleChart PX P), Bd.IsChart c → x ∈ c.φ.source →
      ∀ {m k : ℕ} (t : Fin m → X → Y) (s : Fin k → X → Y) {n : ℕ} {W : ScBanach}
        (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
        c.φ.model.C = T.lvl 0 ⁻¹' quadrant n W 0 →
          ParamGPB c g t T x → ParamGPB c g (Fin.append t s) T x) ∧
    -- (3) a finite-dimensional complement `L` of `T^R_xX` in `T_xX`
    (∀ (x : X) (c : StrongBundleChart PX P), Bd.IsChart c → x ∈ c.φ.source →
      ∀ z : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z = c.φ.toPartialEquiv x →
      ∀ {n : ℕ} {W : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
        c.φ.model.C = T.lvl 0 ⁻¹' quadrant n W 0 →
          ∃ L : Submodule ℝ (c.φ.model.E.lvl 0), IsComplementTR c z x T L ∧
            FiniteDimensional ℝ L) ∧
    -- (4) adding sections which at `x` span `f'(x)L` achieves (ii)
    (∀ (g : X → Y) (x : X) (c : StrongBundleChart PX P), Bd.IsChart c → x ∈ c.φ.source →
      IsZeroAt P g x →
      ∀ z : c.φ.model.E.lvl 1, c.φ.model.E.toBase 1 z = c.φ.toPartialEquiv x →
      ∀ {n : ℕ} {W : ScBanach} (T : ScIso c.φ.model.E ((ScBanach.const (Fin n → ℝ)).prod W)),
        c.φ.model.C = T.lvl 0 ⁻¹' quadrant n W 0 →
      ∀ {m k : ℕ} (t : Fin m → X → Y) (s : Fin k → X → Y)
        (L : Submodule ℝ (c.φ.model.E.lvl 0)),
        PropI c g t x z → IsComplementTR c z x T L →
        Submodule.span ℝ (Set.range fun j => c.principal (s j) (c.φ.toPartialEquiv x)) =
          L.map (Dg c g z).toLinearMap →
          ParamGPB c g (Fin.append t s) T x)

end RoundTrip.V5_36
