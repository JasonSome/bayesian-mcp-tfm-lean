import FCAppendix.Affine.Uniform07Finishing.Native.Concrete05CanonicalRelabel

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.Concrete05
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Crossover Crossover.Physical Crossover.Received06
open Uniform06.LiteralKernelDecomposition
open Uniform06.LiteralExperiment
open FCAppendix.Affine
variable {m c N : ℕ} {row : Uniform07.Row}

theorem canonical_fair_test_eq_marginal {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (i : Fin m) (B : Physical.CanonicalEvent Γ) (b : ℝ) :
    (∫ω in B.event b,fairTest (focalCount Γ i (Physical.two b) ω) ∂sampleLaw Γ)=
      Physical.canonicalMarginal Γ i B b := by
  let μ := (sampleLaw Γ).restrict (B.event b)
  let K := focalCount Γ i (Physical.two b)
  have hK : Measurable K:=measurable_focalCount Γ i (Physical.two b)
  have hS : Integrable (fun ω=>successIndicator (K ω).val) μ :=
    CountLaw.integrable_comp μ K hK (fun k=>successIndicator k.val)
  have hD : Integrable (fun ω=>(K ω:ℝ)-successIndicator (K ω).val) μ :=
    CountLaw.integrable_comp μ K hK (fun k=>(k:ℝ)-successIndicator k.val)
  change (∫ω,(K ω:ℝ)/2 ∂μ)=
    ((∫ω,successIndicator (K ω).val ∂μ)+
      ∫ω,(K ω:ℝ)-successIndicator (K ω).val ∂μ)/2
  rw [integral_div,←integral_add hS hD]
  congr 1
  exact integral_congr_ae (ae_of_all _ (fun ω=>by ring))

theorem canonical_duplicate_test_eq {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (i : Fin m) (B : Physical.CanonicalEvent Γ) (b : ℝ) :
    (∫ω in B.event b,duplicateTest (focalCount Γ i (Physical.two b) ω) ∂sampleLaw Γ)=
      Physical.canonicalDuplicate Γ i B b := by
  apply integral_congr_ae
  apply ae_of_all
  intro ω
  change duplicateTest (focalCount Γ i (Physical.two b) ω)=
    ((focalCount Γ i (Physical.two b) ω).val:ℝ)-
      successIndicator (focalCount Γ i (Physical.two b) ω).val
  generalize focalCount Γ i (Physical.two b) ω=k
  fin_cases k <;> norm_num [duplicateTest,successIndicator] <;> decide

theorem native_canonical_kernels_eq_source06_succ
    (E : UniformFinite.ExactRestrictedLaw row (N+1))
    (hc : 1≤ Uniform07.capacity (N+1)) {R : ℝ} (hR : 0< R)
    (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (hguard : Uniform07.kappa row*R< E.law.multiplier-Early.nativeRadius row)
    (i : Fin (N+1)) (own : Uniform05.Bid row) (hown : 0<(own:ℝ)) :
    Physical.canonicalMarginal (nativeGame E hc R) i (nativeCanonicalEvent E hc R i) own=
      sourceCanonicalMarginal row (N+1) (realJoint E)
        (received06GuardData row (N+1) E.law.multiplier E.law.rejectionRoot)
        (received06CountMargin row (N+1)) own ∧
    Physical.canonicalDuplicate (nativeGame E hc R) i (nativeCanonicalEvent E hc R i) own=
      sourceCanonicalDuplicate row (N+1) (realJoint E)
        (received06GuardData row (N+1) E.law.multiplier E.law.rejectionRoot)
        (received06CountMargin row (N+1)) own := by
  have ha : Hybrid.lowBroadcast own=Physical.two (own:ℝ) :=
    Physical.raw_two_eq (Hybrid.lowBroadcast own) rfl
  have hC:=native_canonical_count_eq_numerical E hc hR hUR hRt hguard i own hown
    fairTest (by norm_num [fairTest])
  have hD:=native_canonical_count_eq_numerical E hc hR hUR hRt hguard i own hown
    duplicateTest (by simp only [duplicateTest,if_neg (by decide : (0:Fin 3)≠2)])
  rw [ha,nativeCanonicalMoment_eq_event,canonical_fair_test_eq_marginal] at hC
  rw [ha,nativeCanonicalMoment_eq_event,canonical_duplicate_test_eq] at hD
  have hsource:=received_canonical_integrals E N own
  exact ⟨hC.trans hsource.1,hD.trans hsource.2⟩

theorem native_canonical_kernels_eq_source06 [Nonempty (Fin m)]
    (E : UniformFinite.ExactRestrictedLaw row m)
    (hc : 1≤ Uniform07.capacity m) {R : ℝ} (hR : 0< R)
    (hUR : Early.bidCap row< R) (hRt : R< Uniform07.cutoff row)
    (hguard : Uniform07.kappa row*R< E.law.multiplier-Early.nativeRadius row)
    (i : Fin m) (own : Uniform05.Bid row) (hown : 0<(own:ℝ)) :
    Physical.canonicalMarginal (nativeGame E hc R) i (nativeCanonicalEvent E hc R i) own=
      sourceCanonicalMarginal row m (realJoint E)
        (received06GuardData row m E.law.multiplier E.law.rejectionRoot)
        (received06CountMargin row m) own ∧
    Physical.canonicalDuplicate (nativeGame E hc R) i (nativeCanonicalEvent E hc R i) own=
      sourceCanonicalDuplicate row m (realJoint E)
        (received06GuardData row m E.law.multiplier E.law.rejectionRoot)
        (received06CountMargin row m) own := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ N =>
    exact native_canonical_kernels_eq_source06_succ E hc hR hUR hRt hguard i own hown

end FCAppendix.Affine.Uniform07Finishing.Concrete05
