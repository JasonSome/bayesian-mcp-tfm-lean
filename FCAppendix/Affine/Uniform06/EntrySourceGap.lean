import FCAppendix.Affine.Uniform06.EntrySourceRatios

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntrySourceGap
open MeasureTheory ProbabilityTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07
open EntrySequence EntrySequence.Source EntrySourceRatios EntryGoodVelocity
open EntryLiteralCanonicalTransfer EntryLiteralResponseGeometry EntryMomentAlgebra

lemma eventually_of_every_subsequence (P : ℕ → Prop)
    (h : ∀ ψ : ℕ → ℕ,Tendsto ψ atTop atTop →
      ∃ φ : ℕ → ℕ,StrictMono φ ∧ ∀ᶠ m in atTop,P (ψ (φ m))) :
    ∀ᶠ m in atTop,P m := by
  classical
  by_contra hn
  have hf : ∃ᶠ m in atTop,¬P m := by simpa only [not_eventually] using hn
  obtain ⟨ψ,hψ,hbad⟩ := extraction_of_frequently_atTop hf
  obtain ⟨φ,hφ,he⟩ := h ψ hψ.tendsto_atTop
  obtain ⟨m,hm⟩ := he.exists
  exact hbad (φ m) hm

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {i : Row} (s : Source μ i)

theorem eventually_conditional_moments {τ : ℝ} (hτ : 0<τ) :
    ∀ᶠ m in atTop,0< s.success m ∧ 0< s.first m ∧ 0< s.second m ∧
      (1/2:ℝ)-τ≤ s.ratio m ∧ s.conditionalMean m≤τ := by
  apply eventually_of_every_subsequence
  intro ψ hψ
  obtain ⟨φ,hφ,hpos,r,hr,hlim,hmean⟩ := every_subsequence s ψ hψ
  refine ⟨φ,hφ,?_⟩
  filter_upwards [hpos,hlim.eventually (Ioi_mem_nhds (sub_lt_self r hτ)),
    hmean.eventually (Iio_mem_nhds hτ)] with m hm hR hM
  exact ⟨hm.1,hm.2.1,hm.2.2,by linarith,hM.le⟩

def margin (i : Row) : ℝ := ((1/2:ℝ)-eta i/xi i)/4

lemma margin_pos (i : Row) : 0< margin i := by
  cases i <;> norm_num [margin,eta,etaQ,xi,xiQ]

lemma margin_value (i : Row) :
    margin i=(match i with | .first => (5/72:ℝ) | .second => (5/328:ℝ)) := by
  cases i <;> norm_num [margin,eta,etaQ,xi,xiQ]

theorem actual_entry_moment_gap
    (hnull : ∀ m,∀ a : ℝ,((s.jointLaw m).map Prod.snd) {a}=0)
    (hnon : ∀ m,∀ᵐ p ∂s.jointLaw m,0≤ p.2)
    (hinterior : ∀ᶠ m in atTop,s.focal m<(s.guards m).multiplier+(s.guards m).radius) :
    ∀ᶠ m in atTop,
      let dq := ∫ x,FixedPriceEntryIntegral.velocity (s.raw m) i (capacity (s.population m))
        (s.guards m) (s.focal m) (s.stripBid m) (ReceiptGap.cap i) s.epsilon x ∂s.law m
      HasDerivAt (fun a => canonicalGoodMarginal i (s.jointLaw m)
        (capacity (s.population m)) (s.rivals m) (s.guards m) a (s.stripBid m)
          (ReceiptGap.cap i) s.epsilon) dq (s.focal m) ∧
      0< s.success m ∧ 0< s.first m ∧ 0< s.second m ∧
      margin i*(s.first m)^2≤ routeGap (eta i) (s.focal m) (s.first m) dq (s.second m) := by
  have hδ := margin_pos i
  filter_upwards [eventually_conditional_moments s hδ,hinterior] with m hm hint
  have hd := original_derivative_and_success_bound i (s.jointLaw m) (hnull m) (hnon m)
    (s.guards m) (s.cap m) (s.finite m) hint
  refine ⟨hd.1,hm.1,hm.2.1,hm.2.2.1,?_⟩
  apply actual_gap_from_conditional_moments (xi_pos i) (eta_pos i).le hm.1 hm.2.2.1
    hδ.le hd.2.2 (s.cauchy m hm.1)
  change eta i/xi i+s.conditionalMean m+margin i≤ s.ratio m
  have hrow : eta i/xi i+3*margin i≤(1/2:ℝ) := by
    have hh := hδ
    unfold margin at hh ⊢
    linarith only [hh]
  linarith [hm.2.2.2.1,hm.2.2.2.2]

end FCAppendix.Affine.Uniform06.EntrySourceGap
