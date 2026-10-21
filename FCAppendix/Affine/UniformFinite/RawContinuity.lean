import FCAppendix.Affine.UniformFinite.ZeroNoiseTests
import FCAppendix.Affine.UniformFinite.FocalSeedContinuity

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

namespace RawContinuous

abbrev Parameter (i : Row) := Value i×Bid i

def input (i : Row) {N : ℕ} (G : Uniform05.RestrictedLaw i)
    (kind : Fin N→ Fin 3) (p : Parameter i) (b : Fin N→ Bid i) :
    ℝ×SourceContinuity.State i (N+1) :=
  (p.1,G,Noisy.cappedFocalBids i kind p.2 b)

lemma continuous_input (i : Row) {N : ℕ} (G : Uniform05.RestrictedLaw i)
    (kind : Fin N→ Fin 3) :
    Continuous (fun p : Parameter i×(Fin N→ Bid i)=> input i G kind p.1 p.2) := by
  have hb : Continuous (fun p : Parameter i×(Fin N→Bid i) =>
      Noisy.cappedFocalBids i kind p.1.2 p.2) :=
    (Noisy.continuous_cappedFocalBids i kind).comp
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hs := (SourceContinuity.continuous_fixedLawState i G).comp hb
  exact (continuous_subtype_val.comp (continuous_fst.comp continuous_fst)).prodMk hs

def integrand (i : Row) {N : ℕ} (G : Uniform05.RestrictedLaw i)
    (kind : Fin N→ Fin 3) (p : Parameter i) (b : Fin N→ Bid i) : ℝ :=
  rowPayoff i G (focalRow kind) p.1 (focalBids i kind p.2 b) 0

lemma integrand_input (i : Row) {N : ℕ} (G : Uniform05.RestrictedLaw i)
    (kind : Fin N→ Fin 3) (p : Parameter i) (b : Fin N→ Bid i) :
    integrand i G kind p b=rowPayoff i (input i G kind p b).2.1 (focalRow kind)
      (input i G kind p b).1 (SourceContinuity.bids i (input i G kind p b).2) 0 := by
  have he : SourceContinuity.bids i
      (show SourceContinuity.State i (N+1) from (G,Noisy.cappedFocalBids i kind p.2 b)) =
      focalBids i kind p.2 b := Noisy.cappedFocalBids_real i kind p.2 b
  simpa only [integrand,input] using congrArg
    (fun bs => rowPayoff i G (focalRow kind) p.1 bs 0) he.symm

lemma measurable_integrand (i : Row) {N : ℕ} (G : Uniform05.RestrictedLaw i)
    (kind : Fin N→ Fin 3) : Measurable (Function.uncurry (integrand i G kind)) := by
  change Measurable (fun x : Parameter i×(Fin N→Bid i)=>integrand i G kind x.1 x.2)
  simp_rw [integrand_input]
  exact (SourceContinuity.measurable_rowPayoff i (focalRow kind) 0 (Noisy.focal_mem_lower kind)).comp
    (continuous_input i G kind).measurable

lemma integrand_bound (i : Row) {N : ℕ} (G : Uniform05.RestrictedLaw i)
    (kind : Fin N→ Fin 3) (p : Parameter i) (b : Fin N→ Bid i) :
    |integrand i G kind p b|≤ Uniform05.t i+(1+|Uniform05.eta i|)*Uniform05.cap i := by
  have h:=rowPayoff_bound i G (focalRow kind) p.1 (focalBids i kind p.2 b) 0
  simp only [focalBids_zero,abs_of_nonneg p.1.property.1,abs_of_nonneg p.2.property.1] at h
  exact h.trans (add_le_add p.1.property.2
    (mul_le_mul_of_nonneg_left p.2.property.2 (by positivity)))

theorem ae_continuousAt_integrand (i : Row) {N : ℕ} (G : Uniform05.RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (kind : Fin N→ Fin 3) (p : Parameter i) (hp : 0<(p.2:ℝ)) :
    ∀ᵐb∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i)),
      ContinuousAt (fun q : Parameter i=> integrand i G kind q b) p := by
  filter_upwards [ExactTests.ae_rival_ties i G kind p.2 hp.ne',
    ExactTests.ae_rival_cut (N:=N) i G] with b hties hcut
  have hc : Continuous (fun q : Parameter i=> input i G kind q b) :=
    (continuous_input i G kind).comp (continuous_id.prodMk continuous_const)
  have hbi : SourceContinuity.bids i (input i G kind p b).2 =
      focalBids i kind p.2 b := Noisy.cappedFocalBids_real i kind p.2 b
  simp_rw [integrand_input]
  apply (SourceContinuity.continuousAt_rowPayoff_rival_cut i (focalRow kind) 0
    (Noisy.focal_mem_lower kind) (input i G kind p b) ?_ ?_ ?_).comp
      (f := fun q : Parameter i=>input i G kind q b) hc.continuousAt
  · simpa only [hbi,focalBids_zero] using hp
  · intro a
    refine Fin.cases ?_ (fun j=>?_) a
    · intro _ hne
      exact False.elim (hne rfl)
    · intro ha _
      have hk : kind j=0 := by simpa [focalRow,Source.countRowOfKind] using ha
      simpa only [hbi,focalBids_succ,
        if_pos hk] using hcut j
  · intro P Q h
    apply hties P.val Q.val
    simpa only [hbi,
      Noisy.lowerBids_focalBids] using h

theorem continuousAt_rowIntegral (i : Row) {N : ℕ} (G : Uniform05.RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (kind : Fin N→ Fin 3) (p : Parameter i) (hp : 0<(p.2:ℝ)) :
    ContinuousAt (fun q : Parameter i=>∫b : Fin N→ Bid i,integrand i G kind q b
      ∂(rowLaw N G.bidLaw : Measure (Fin N→ Bid i))) p := by
  apply MeasureTheory.continuousAt_of_dominated
    (bound:=fun _=> Uniform05.t i+(1+|Uniform05.eta i|)*Uniform05.cap i)
  · exact Eventually.of_forall (fun q=>(
      (measurable_integrand i G kind).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun q=> ae_of_all _ (fun b=> by
      simpa only [Real.norm_eq_abs] using integrand_bound i G kind q b))
  · exact integrable_const _
  · exact ae_continuousAt_integrand i G kind p hp

end RawContinuous

theorem continuousAt_rawUtility (i : Row) (N : ℕ) (G : Uniform05.RestrictedLaw i)
    [NullSingletonClass (G.bidLaw : Measure (Bid i))]
    (p : Value i×Bid i) (hp : 0<(p.2:ℝ)) :
    ContinuousAt (fun q : Value i×Bid i=> rawUtility i N G q.1 q.2) p := by
  unfold rawUtility FiniteLaw.expect
  apply tendsto_finsetSum
  intro kind _
  exact continuousAt_const.mul (RawContinuous.continuousAt_rowIntegral i G kind p hp)

end FCAppendix.Affine.UniformFinite
