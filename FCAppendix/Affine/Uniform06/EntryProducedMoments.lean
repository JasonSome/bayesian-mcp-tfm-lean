import FCAppendix.Affine.Uniform06.EntryConstructedSource

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryProducedMoments

open MeasureTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07
open EntryConstructedSource EntryConstructedSource.EarlyArray EntryFiniteConstructor
open EntryLiteralCanonicalTransfer EntrySourceGap EntrySourceLower EntryMomentAlgebra

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {i : Row} (s : EarlyArray μ i)

def first (m : ℕ) (b : ℝ) : ℝ :=
  canonicalGoodMarginal i (s.jointLaw m) (capacity (s.population m)) (s.population m-1)
    (s.guards m) b ((s.guards m).multiplier+2*(s.guards m).radius) (ReceiptGap.cap i) (epsilon i)

def second (m : ℕ) (b : ℝ) : ℝ :=
  canonicalGoodDuplicate i (s.jointLaw m) (capacity (s.population m)) (s.population m-1)
    (s.guards m) b ((s.guards m).multiplier+2*(s.guards m).radius) (ReceiptGap.cap i) (epsilon i)

lemma eventually_unshift (M : ℕ) {P : ℕ→ Prop} (h : ∀ᶠ m in atTop,P (m+M)) :
    ∀ᶠ m in atTop,P m := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp h
  refine eventually_atTop.mpr ⟨K+M,?_⟩
  intro m hm
  have hh := hK (m-M) (by omega)
  simpa only [Nat.sub_add_cancel (by omega : M≤ m)] using hh

theorem original_first_subexponential (b : ℕ→ℝ)
    (hb : Tendsto b atTop (𝓝 (entry i))) :
    SubexponentialLower (fun m => s.population m-1) (fun m => first s m (b m)) := by
  obtain ⟨M,t,hV,hB,hN,hb',hg,he,hA⟩ := s.source_on_tail b hb
  have hfirst (m : ℕ) : t.first m=first s (m+M) (b (m+M)) := by
    simp only [EntrySequence.Source.first,EntrySequence.Source.jointLaw,EntrySequence.Source.rivals,
      first,hV,hB,hN,hb',hg,he,hA,canonicalGoodMarginal_normalize,jointLaw]
  intro e hepos
  apply eventually_unshift M
  have hh := first_subexponential t e hepos
  simpa only [EntrySequence.Source.rivals,hN,hfirst] using hh

theorem original_entry_gap (b : ℕ→ℝ) (hb : Tendsto b atTop (𝓝 (entry i)))
    (hnull : ∀ m,∀ z : ℝ,((s.jointLaw m).map Prod.snd) {z}=0) :
    ∀ᶠ m in atTop,∃ dq : ℝ,
      HasDerivAt (first s m) dq (b m) ∧ 0< first s m (b m) ∧ 0< second s m (b m) ∧
      margin i*(first s m (b m))^2≤ routeGap (eta i) (b m)
        (first s m (b m)) dq (second s m (b m)) := by
  obtain ⟨M,t,hV,hB,hN,hb',hg,he,hA⟩ := s.source_on_tail b hb
  have hG (m : ℕ) : t.jointLaw m=s.jointLaw (m+M) := by
    simp only [EntrySequence.Source.jointLaw,jointLaw,hV,hB]
  have hfirst (m : ℕ) : t.first m=first s (m+M) (b (m+M)) := by
    simp only [EntrySequence.Source.first,EntrySequence.Source.rivals,first,hG,hN,hb',hg,he,hA,
      canonicalGoodMarginal_normalize]
  have hsecond (m : ℕ) : t.second m=second s (m+M) (b (m+M)) := by
    simp only [EntrySequence.Source.second,EntrySequence.Source.rivals,second,hG,hN,hb',hg,he,hA,
      canonicalGoodDuplicate_normalize]
  have hrad (m : ℕ) : (t.guards m).radius=SourcePrefixConstructor.radius i := by
    rw [hg]
    exact (s.literal (m+M)).radius_eq
  have ha : 0< SourcePrefixConstructor.radius i := by
    have ht := cutoff_pos i
    unfold SourcePrefixConstructor.radius
    positivity
  have hint : ∀ᶠ m in atTop,t.focal m<(t.guards m).multiplier+(t.guards m).radius := by
    have hh : Tendsto (fun m => t.focal m-(t.guards m).multiplier) atTop (𝓝 (0:ℝ)) := by
      simpa only [sub_self] using t.focal_tendsto.sub t.multiplier_tendsto
    filter_upwards [hh.eventually_lt_const ha] with m hm
    rw [hrad]
    linarith
  have hgap := actual_entry_moment_gap t
    (fun m z => by rw [hG]; exact hnull (m+M) z)
    (fun m => by rw [hG]; exact s.joint_nonnegative (m+M)) hint
  apply eventually_unshift M
  filter_upwards [hgap] with m hm
  dsimp only at hm
  generalize hdq : (∫ x : EntryIIDCentral.Row (t.rivals m),
    FixedPriceEntryIntegral.velocity (t.raw m) i (capacity (t.population m))
      (t.guards m) (t.focal m) (t.stripBid m) (ReceiptGap.cap i) t.epsilon x ∂t.law m)=dq at hm
  refine ⟨dq,?_,?_,?_,?_⟩
  · change HasDerivAt (fun a => first s (m+M) a) dq (b (m+M))
    simpa only [first,EntrySequence.Source.rivals,hG,hN,hb',hg,he,hA,
      canonicalGoodMarginal_normalize] using hm.1
  · simpa only [hfirst] using hm.2.2.1
  · simpa only [hsecond] using hm.2.2.2.1
  · simpa only [hfirst,hsecond,hb'] using hm.2.2.2.2

end FCAppendix.Affine.Uniform06.EntryProducedMoments
