import FCAppendix.Affine.Tail04.OriginalPrivateEntry
import FCAppendix.Affine.LowBody.NoisyAtomlessLimit

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalLowConditional
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Hybrid NativeFlag OriginalPopulation OriginalPrivateEntry

variable (E : Observable.Regions)

def lowRowEvent (B : Set ℝ) : Set LowBody.RowRival := {r | r.1=0 ∧ r.2∈B}

lemma measurableSet_lowRowEvent (B : Set ℝ) (hB : MeasurableSet B) :
    MeasurableSet (lowRowEvent B) :=
  (measurableSet_eq_fun measurable_fst measurable_const).inter (hB.preimage measurable_snd)

lemma rivalLaw_low_event (s a h : ℝ) (G : Measure ℝ) (B : Set ℝ) (hB : MeasurableSet B) :
    LowBody.rivalLaw s a h G (lowRowEvent B)=ENNReal.ofReal s*G B := by
  have hE := measurableSet_lowRowEvent B hB
  have h0 : (fun b : ℝ => ((0:Fin 4),b)) ⁻¹' lowRowEvent B=B := by
    ext b;simp [lowRowEvent]
  simp only [LowBody.rivalLaw,Measure.add_apply,Measure.smul_apply,smul_eq_mul]
  rw [Measure.map_apply (show Measurable (fun b : ℝ => ((0:Fin 4),b)) from measurable_const.prodMk measurable_id) hE,h0]
  rw [Measure.dirac_apply' (1,0) hE,Measure.dirac_apply' (2,0) hE,Measure.dirac_apply' (3,0) hE]
  simp [lowRowEvent,Set.indicator]

lemma native_low_event_preimage {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (B : Set ℝ) :
    (E.coarseTag ⁻¹' {0})∩(nativeBid ⁻¹' B)=(E.nativeRow Γ) ⁻¹' lowRowEvent B := by
  ext x
  by_cases hl : x.1.2.bid≤ E.d
  · simp [Observable.Regions.coarseTag,Observable.Regions.nativeRow,
      Observable.Regions.collapse,nativeBid,lowRowEvent,hl]
  · have ht : E.coarseTag x≠0 := by
      simpa [ObservedScenario.coarseTag_low_iff E x] using hl
    have ht' : (E.nativeRow Γ x).1≠0 := ht
    simp [ht,lowRowEvent,ht',nativeBid]

theorem native_lowBidLaw_eq {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (s a h : ℝ) (hs : 0< s)
    (G : Measure ℝ) [IsProbabilityMeasure G]
    (hrow : (userLaw Γ).map (E.nativeRow Γ)=LowBody.rivalLaw s a h G) :
    nativeLowBidLaw Γ E=G := by
  let P : Set (UserDraw 2) := E.coarseTag ⁻¹' {0}
  have hP : MeasurableSet P := E.measurable_coarseTag (measurableSet_singleton _)
  have hnum (B : Set ℝ) (hB : MeasurableSet B) :
      (userLaw Γ) (P∩nativeBid ⁻¹' B)=ENNReal.ofReal s*G B := by
    rw [native_low_event_preimage E Γ B,← Measure.map_apply (E.measurable_nativeRow Γ)
      (measurableSet_lowRowEvent B hB),hrow,rivalLaw_low_event s a h G B hB]
  have hpmeasure : (userLaw Γ) P=ENNReal.ofReal s := by
    simpa using hnum univ MeasurableSet.univ
  have hpmass : (userLaw Γ).real P=s := by
    rw [measureReal_def,hpmeasure,ENNReal.toReal_ofReal hs.le]
  have hp : 0<(userLaw Γ).real P := by rw [hpmass];exact hs
  letI : IsProbabilityMeasure (cond (userLaw Γ) P) :=
    cond_isProbabilityMeasure (measure_ne_zero_of_real_pos _ _ hp)
  apply Measure.ext
  intro B hB
  rw [nativeLowBidLaw,Measure.map_apply measurable_nativeBid hB]
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change (cond (userLaw Γ) P).real (nativeBid ⁻¹' B)=G.real B
  rw [cond_real_eq _ P hP hp,hpmass]
  have hn : (userLaw Γ).real (P∩nativeBid ⁻¹' B)=s*G.real B := by
    rw [measureReal_def,hnum B hB,ENNReal.toReal_mul,ENNReal.toReal_ofReal hs.le]
    rfl
  rw [hn]
  field_simp [hs.ne']

theorem native_low_atomless_of_C2 {m N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    {d ξ : ℝ} (Γ : FiniteGame m 2 c Seed) (s a h : ℝ) (hs : 0< s)
    (categories : FiniteLaw (Fin 4)) (μ : Measure (LowBody.LowValue d)) [IsProbabilityMeasure μ]
    (L : LowBody.ActualAtomlessLowLimit N d ξ c categories μ)
    (hrow : (userLaw Γ).map (E.nativeRow Γ)=
      LowBody.rivalLaw s a h (LowBody.realLowBidLaw L.joint.1 : Measure ℝ)) :
    ∀ b,nativeLowBidLaw Γ E {b}=0 := by
  letI := L.real_atomless
  rw [native_lowBidLaw_eq E Γ s a h hs _ hrow]
  exact fun b => measure_singleton b

end FCAppendix.Affine.Tail04.OriginalLowConditional
