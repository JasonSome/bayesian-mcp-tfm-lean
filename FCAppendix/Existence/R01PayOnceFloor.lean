import FCAppendix.Existence.R01PayOnceKernel
import FCAppendix.Existence.R01CompactProduct
import FCAppendix.Existence.R01SumBorel

noncomputable section
namespace FCAppendix.Existence.PayOnceBounded
open MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators
open FCAppendix.Existence.Distributional

abbrev Value (W : ℝ) := Icc (0 : ℝ) W
abbrev FloorLaw (ε W : ℝ) (μ : Measure (Value W)) :=
  Law (A := FloorAction ε W) μ

def insertFocal {ε W : ℝ} (N : ℕ) (a : FloorAction ε W)
    (r : Fin N → Value W × FloorAction ε W) : Fin (N + 1) → FloorAction ε W :=
  Fin.cons a (fun i => (r i).2)

theorem continuous_insertFocal {ε W : ℝ} (N : ℕ) :
    Continuous (fun p : FloorAction ε W × (Fin N → Value W × FloorAction ε W) =>
      insertFocal N p.1 p.2) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [insertFocal] using
      (continuous_fst : Continuous (Prod.fst : FloorAction ε W ×
        (Fin N → Value W × FloorAction ε W) → _))
  · have hj : Continuous (fun p : FloorAction ε W × (Fin N → Value W × FloorAction ε W) => p.2 j) :=
      (continuous_apply j).comp continuous_snd
    change Continuous (fun p : FloorAction ε W × (Fin N → Value W × FloorAction ε W) => (p.2 j).2)
    exact hj.snd

def Qfloor {ε W : ℝ} (N n c : ℕ) {μ : Measure (Value W)}
    (π : FloorLaw ε W μ) (a : FloorAction ε W) : ℝ :=
  ∫ r, success n c (insertFocal N a r) 0
    ∂(rowLaw N π.1 : Measure (Fin N → Value W × FloorAction ε W))

def floorPayoff {ε W : ℝ} (N n c : ℕ) {μ : Measure (Value W)}
    (p : FloorLaw ε W μ × (Value W × FloorAction ε W)) : ℝ :=
  (p.2.1.1 - bid p.2.2) * Qfloor N n c p.1 p.2.2

theorem continuous_Qfloor {ε W : ℝ} (N n c : ℕ) (hn : 2 ≤ n) (hε : 0 < ε)
    (μ : Measure (Value W)) [IsProbabilityMeasure μ] :
    Continuous (fun p : FloorLaw ε W μ × FloorAction ε W => Qfloor N n c p.1 p.2) := by
  letI : OpensMeasurableSpace (Fin N → Value W × FloorAction ε W) := inferInstance
  let f : FloorAction ε W × (Fin N → Value W × FloorAction ε W) → ℝ :=
    fun p => success n c (insertFocal N p.1 p.2) 0
  have hf : Continuous f := (PayOnce.continuous_success n).comp
    ((continuous_apply (0 : Fin (N + 1))).comp
      ((continuous_marginal n c hn hε).comp (continuous_insertFocal N)))
  have hrow : Continuous (fun p : FloorLaw ε W μ × FloorAction ε W => rowLaw N p.1.1) :=
    (continuous_rowLaw (X := Value W × FloorAction ε W) N).comp
      (continuous_subtype_val.comp continuous_fst)
  exact (continuous_law_integral f hf).comp (continuous_snd.prodMk hrow)

theorem continuous_floorPayoff {ε W : ℝ} (N n c : ℕ) (hn : 2 ≤ n) (hε : 0 < ε)
    (μ : Measure (Value W)) [IsProbabilityMeasure μ] :
    Continuous (floorPayoff (μ := μ) (ε := ε) N n c) := by
  have hq : Continuous (fun p : FloorLaw ε W μ × (Value W × FloorAction ε W) =>
      Qfloor N n c p.1 p.2.2) := (continuous_Qfloor N n c hn hε μ).comp
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  exact ((continuous_subtype_val.comp (continuous_fst.comp continuous_snd)).sub
    (continuous_bid.comp (continuous_snd.comp continuous_snd))).mul hq

theorem Qfloor_bounds {ε W : ℝ} (N n c : ℕ) (hn : 2 ≤ n) (hε : 0 < ε)
    {μ : Measure (Value W)} (π : FloorLaw ε W μ) (a : FloorAction ε W) :
    0 ≤ Qfloor N n c π a ∧ Qfloor N n c π a ≤ 1 := by
  have hb : ∀ r : Fin N → Value W × FloorAction ε W,
      0 ≤ success n c (insertFocal N a r) 0 ∧ success n c (insertFocal N a r) 0 ≤ 1 :=
    fun r => success_bounds n c hn hε _ _
  refine ⟨integral_nonneg (fun r => (hb r).1), ?_⟩
  have hf : Continuous (fun r : Fin N → Value W × FloorAction ε W =>
      success n c (insertFocal N a r) 0) :=
    (PayOnce.continuous_success n).comp
      ((continuous_apply 0).comp ((continuous_marginal n c hn hε).comp
        ((continuous_insertFocal N).comp (continuous_const.prodMk continuous_id))))
  have hi := (ContinuousMap.equivBoundedOfCompact _ _ ⟨_, hf⟩).integrable
    (rowLaw N π.1 : Measure (Fin N → Value W × FloorAction ε W))
  calc
    Qfloor N n c π a ≤ ∫ _r : Fin N → Value W × FloorAction ε W, (1 : ℝ)
        ∂(rowLaw N π.1 : Measure (Fin N → Value W × FloorAction ε W)) :=
      integral_mono hi (integrable_const _) (fun r => (hb r).2)
    _ = 1 := by simp

@[simp] theorem Qfloor_abstain {ε W : ℝ} (N n c : ℕ)
    {μ : Measure (Value W)} (π : FloorLaw ε W μ) :
    Qfloor N n c π (.inl ()) = 0 := by
  unfold Qfloor
  have he : ∀ r : Fin N → Value W × FloorAction ε W,
      success n c (insertFocal N (.inl ()) r) 0 = 0 := by
    intro r
    have ha : (0 : Fin (N + 1)) ∉ activeSet (insertFocal N (.inl ()) r) := by
      simp [activeSet, insertFocal, present]
    simp [success, marginal, onSupport, ha, PayOnce.success]
  simp_rw [he]
  simp

@[simp] theorem floorPayoff_abstain {ε W : ℝ} (N n c : ℕ)
    {μ : Measure (Value W)} (π : FloorLaw ε W μ) (w : Value W) :
    floorPayoff N n c (π, (w, .inl ())) = 0 := by
  simp [floorPayoff]

theorem epsilon_floor_exists (W ε : ℝ) (hε : 0 < ε) (_hεW : ε ≤ W)
    (N n c : ℕ) (hn : 2 ≤ n)
    (μ : Measure (Value W)) [IsProbabilityMeasure μ] :
    ∃ (π : FloorLaw ε W μ) (σ : Kernel (Value W) (FloorAction ε W)),
      IsMarkovKernel σ ∧ μ ⊗ₘ σ = (π.1 : Measure (Value W × FloorAction ε W)) ∧
      AllActionOptimal π (fun z => floorPayoff N n c (π, z)) ∧
      (∀ᵐ w ∂μ, ∀ᵐ a ∂σ w, ∀ a' : FloorAction ε W,
        floorPayoff N n c (π, (w, a')) ≤ floorPayoff N n c (π, (w, a))) := by
  exact exists_symmetric_law μ (floorPayoff N n c)
    (continuous_floorPayoff N n c hn hε μ)

theorem Qfloor_mono {ε W : ℝ} (N n c : ℕ) (hn : 2 ≤ n) (hε : 0 < ε)
    {μ : Measure (Value W)} (π : FloorLaw ε W μ) (b b' : Icc ε W)
    (hbb' : b.1 ≤ b'.1) : Qfloor N n c π (.inr b) ≤ Qfloor N n c π (.inr b') := by
  have hf (a : FloorAction ε W) : Continuous
      (fun r : Fin N → Value W × FloorAction ε W => success n c (insertFocal N a r) 0) :=
    (PayOnce.continuous_success n).comp
      ((continuous_apply 0).comp ((continuous_marginal n c hn hε).comp
        ((continuous_insertFocal N).comp (continuous_const.prodMk continuous_id))))
  apply integral_mono
  · exact (ContinuousMap.equivBoundedOfCompact _ _ ⟨_, hf (.inr b)⟩).integrable _
  · exact (ContinuousMap.equivBoundedOfCompact _ _ ⟨_, hf (.inr b')⟩).integrable _
  · intro r
    have hp := marginal_spec n c hn hε (insertFocal N (.inr b) r)
    have hp' := marginal_spec n c hn hε (insertFocal N (.inr b') r)
    apply success_mono_scalar n (hp.1 0) _ (hp'.2.1 0)
    have hm := marginal_mono_own n c hn hε (insertFocal N (.inr b) r) 0 b b' hbb'
    simpa [insertFocal, Function.update, Fin.cons] using hm
end FCAppendix.Existence.PayOnceBounded
