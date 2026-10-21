import FCAppendix.Affine.Tail04.EqualPrivateCountPayoff
import FCAppendix.Affine.Tail04.CompactSourceBidLaws
import FCAppendix.Affine.Tail04.SortedAllNoise
import FCAppendix.Affine.Tail04.PrivatePayoffContinuity

noncomputable section
namespace FCAppendix.Affine.Tail04.EqualNoisyUtilities
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional EqualPrivateSignal SortedAllNoise AllNoiseFiniteSelector
open scoped BigOperators

abbrev Input (N H : ℕ) (R V U : ℝ) :=
  (Fin N → Icc (1:ℝ) U)×ProbabilityMeasure (Signal H R V)

def physical {N : ℕ} {U eps : ℝ} (heps : 0≤ eps)
    (b : Fin N → Icc (1:ℝ) U) (z : Fin N → unitInterval) : Fin N → Icc (1:ℝ) (U*(1+eps)) :=
  fun i => CompactSourceBidLaws.noisyBid (by norm_num) heps (b i,z i)

lemma continuous_physical {N : ℕ} {U eps : ℝ} (heps : 0≤ eps) :
    Continuous (fun p : (Fin N → Icc (1:ℝ) U)×(Fin N → unitInterval) => physical heps p.1 p.2) := by
  apply continuous_pi
  intro i
  exact (CompactSourceBidLaws.continuous_noisyBid (by norm_num) heps).comp
    (((continuous_apply i).comp continuous_fst).prodMk ((continuous_apply i).comp continuous_snd))

def parameter {N H : ℕ} {R V U eps : ℝ} (heps : 0≤ eps)
    (p : Input N H R V U) (z : Fin N → unitInterval) :
    PolicyParameters N H R V 1 (U*(1+eps)) :=
  (sortedBox (physical heps p.1 z),WeakProbability.mk p.2)

lemma continuous_parameter {N H : ℕ} {R V U eps : ℝ} (heps : 0≤ eps) :
    Continuous (fun p : Input N H R V U×(Fin N → unitInterval) => parameter heps p.1 p.2) :=
  (continuous_sortedBox.comp ((continuous_physical heps).comp
    ((continuous_fst.comp continuous_fst).prodMk continuous_snd))).prodMk
      (WeakProbability.continuous_mk.comp (continuous_snd.comp continuous_fst))

def physicalReal {N : ℕ} {U eps : ℝ} (heps : 0≤ eps)
    (b : Fin N → Icc (1:ℝ) U) (z : Fin N → unitInterval) : Fin N → ℝ :=
  fun i => (physical heps b z i:ℝ)

lemma continuous_physicalReal {N : ℕ} {U eps : ℝ} (heps : 0≤ eps) :
    Continuous (fun p : (Fin N → Icc (1:ℝ) U)×(Fin N → unitInterval) => physicalReal heps p.1 p.2) :=
  continuous_pi (fun i => continuous_subtype_val.comp ((continuous_apply i).comp (continuous_physical heps)))

def rawCount {N H c : ℕ} {R V U eps : ℝ} (heps : 0≤ eps) (ξ : ℝ)
    (p : Input N H R V U) (z : Fin N → unitInterval) (i : Fin N) : CountLaw 2 :=
  EqualPrivateCountPayoff.countLaw N H c R V ξ 1 (U*(1+eps)) (parameter heps p z)
    (focalRank (physicalReal heps p.1 z) i)

lemma measurable_rawCount_mass {N H c : ℕ} {R V U eps ξ : ℝ}
    (heps : 0≤ eps) (hξ : 0< ξ) (p : Input N H R V U) (i : Fin N) (r : Fin 3) :
    Measurable (fun z : Fin N → unitInterval => (rawCount (c:=c) heps ξ p z i).mass r) := by
  have hphys : Continuous (fun z : Fin N → unitInterval => physicalReal heps p.1 z) :=
    (continuous_physicalReal heps).comp
      (show Continuous (fun z : Fin N → unitInterval => (p.1,z)) from
        continuous_const.prodMk continuous_id)
  have hparam : Continuous (fun z : Fin N → unitInterval => parameter heps p z) :=
    (continuous_parameter heps).comp
      (show Continuous (fun z : Fin N → unitInterval => (p,z)) from
        continuous_const.prodMk continuous_id)
  exact LocalCoordinates.measurable_finite_eval
    (fun z : Fin N → unitInterval => focalRank (physicalReal heps p.1 z) i)
    (fun z j => (EqualPrivateCountPayoff.countLaw N H c R V ξ 1 (U*(1+eps))
      (parameter heps p z) j).mass r)
    ((measurable_focalRank i).comp hphys.measurable)
    (fun j => ((EqualPrivateCountPayoff.continuous_countLaw_mass N H c R V ξ 1 (U*(1+eps))
      hξ (by norm_num) j r).comp hparam).measurable)

lemma ae_continuousAt_rawCount_mass {N H c : ℕ} {R V U eps ξ : ℝ}
    (heps : 0< eps) (hξ : 0< ξ) (p : Input N H R V U) (i : Fin N) (r : Fin 3) :
    ∀ᵐ z ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)),
      ContinuousAt (fun q : Input N H R V U => (rawCount (c:=c) heps.le ξ q z i).mass r) p := by
  let b : Fin N → ℝ := fun j => (p.1 j:ℝ)
  have hb (j : Fin N) : 0< b j := lt_of_lt_of_le (by norm_num) (p.1 j).2.1
  filter_upwards [AtypicalActiveNoisy.ae_noisyBids_distinct heps.ne' b (fun j => (hb j).ne')] with z hz
  have hn : ∀ j k,j≠k → physicalReal heps.le p.1 z j≠physicalReal heps.le p.1 z k := hz
  have hc : Continuous (fun q : Input N H R V U => physicalReal heps.le q.1 z) :=
    (continuous_physicalReal heps.le).comp (continuous_fst.prodMk continuous_const)
  have hp := hc.continuousAt.tendsto.eventually
    (permutation_eventually_eq (physicalReal heps.le p.1 z) hn)
  have hparam : Continuous (fun q : Input N H R V U => parameter heps.le q z) :=
    (continuous_parameter heps.le).comp
      (show Continuous (fun q : Input N H R V U => (q,z)) from continuous_id.prodMk continuous_const)
  have hfixed := (EqualPrivateCountPayoff.continuous_countLaw_mass N H c R V ξ 1 (U*(1+eps))
    hξ (by norm_num) (focalRank (physicalReal heps.le p.1 z) i) r).comp hparam
  apply hfixed.continuousAt.congr_of_eventuallyEq
  exact hp.mono (fun q hq => by simp only [Function.comp_def,rawCount,focalRank,hq])

def mass {N H c : ℕ} {R V U eps : ℝ} (heps : 0≤ eps) (ξ : ℝ) (i : Fin N) (r : Fin 3)
    (p : Input N H R V U) : ℝ :=
  ∫ z : Fin N → unitInterval,(rawCount (c:=c) heps ξ p z i).mass r
    ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))

def paymentMass {N H c : ℕ} {R V U eps : ℝ} (heps : 0≤ eps) (ξ : ℝ) (i : Fin N) (r : Fin 3)
    (p : Input N H R V U) : ℝ :=
  ∫ z : Fin N → unitInterval,(1+eps*(z i:ℝ))*(rawCount (c:=c) heps ξ p z i).mass r
    ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))

theorem continuous_mass {N H c : ℕ} {R V U eps ξ : ℝ}
    (heps : 0< eps) (hξ : 0< ξ) (i : Fin N) (r : Fin 3) :
    Continuous (mass (H:=H) (c:=c) (R:=R) (V:=V) (U:=U) heps.le ξ i r) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply MeasureTheory.continuousAt_of_dominated
    (F:=fun p z => (rawCount (c:=c) heps.le ξ p z i).mass r) (bound:=fun _ => (1:ℝ))
  · exact Eventually.of_forall (fun p => (measurable_rawCount_mass heps.le hξ p i r).aestronglyMeasurable)
  · exact Eventually.of_forall (fun p => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs,abs_of_nonneg (AtypicalActiveNoisy.mass_bounds _ r).1]
      exact (AtypicalActiveNoisy.mass_bounds _ r).2))
  · exact integrable_const 1
  · exact ae_continuousAt_rawCount_mass heps hξ p i r

theorem continuous_paymentMass {N H c : ℕ} {R V U eps ξ : ℝ}
    (heps : 0< eps) (hξ : 0< ξ) (i : Fin N) (r : Fin 3) :
    Continuous (paymentMass (H:=H) (c:=c) (R:=R) (V:=V) (U:=U) heps.le ξ i r) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply MeasureTheory.continuousAt_of_dominated
    (F:=fun p z => (1+eps*(z i:ℝ))*(rawCount (c:=c) heps.le ξ p z i).mass r)
    (bound:=fun _ => 1+eps)
  · exact Eventually.of_forall (fun p =>
      (((by fun_prop : Measurable (fun z : Fin N → unitInterval => 1+eps*(z i:ℝ))).mul
        (measurable_rawCount_mass heps.le hξ p i r)).aestronglyMeasurable))
  · exact Eventually.of_forall (fun p => ae_of_all _ (fun z => by
      have h0 : 0≤1+eps*(z i:ℝ) := by nlinarith [mul_nonneg heps.le (z i).2.1]
      have h1 : 1+eps*(z i:ℝ)≤1+eps := by nlinarith [(z i).2.2]
      have hm := AtypicalActiveNoisy.mass_bounds (rawCount (c:=c) heps.le ξ p z i) r
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg h0 hm.1)]
      exact (mul_le_of_le_one_right h0 hm.2).trans h1))
  · exact integrable_const _
  · filter_upwards [ae_continuousAt_rawCount_mass heps hξ p i r] with z hz
    exact continuousAt_const.mul hz

def activeUtility {N H c : ℕ} {R V U eps : ℝ} (heps : 0≤ eps) (ξ eta : ℝ)
    (heta0 : 0≤ eta) (heta1 : eta≤1) (i : Fin N) (p : ℝ×Input N H R V U) : ℝ :=
  ∑ r : Fin 3, (p.1*successIndicator r.val*mass (c:=c) heps ξ i r p.2-
    (p.2.1 i:ℝ)*(Schedule.affine 2 eta heta0 heta1).charge r.val*paymentMass (c:=c) heps ξ i r p.2)

theorem continuous_activeUtility {N H c : ℕ} {R V U eps ξ : ℝ}
    (heps : 0< eps) (hξ : 0< ξ) (eta : ℝ) (heta0 : 0≤ eta) (heta1 : eta≤1) (i : Fin N) :
    Continuous (activeUtility (H:=H) (c:=c) (R:=R) (V:=V) (U:=U) heps.le ξ eta heta0 heta1 i) := by
  unfold activeUtility
  apply continuous_finsetSum
  intro r _
  exact (((continuous_fst.mul continuous_const).mul
    ((continuous_mass heps hξ i r).comp continuous_snd)).sub
    (((continuous_subtype_val.comp ((continuous_apply i).comp (continuous_fst.comp continuous_snd))).mul
      continuous_const).mul ((continuous_paymentMass heps hξ i r).comp continuous_snd)))

abbrev PrivateInput (N H : ℕ) (R Up eps U : ℝ) :=
  Input N H R (Up*(1+eps)) U×Icc R Up×ProbabilityMeasure (Signal H R (Up*(1+eps)))

instance (N H : ℕ) (R Up eps U : ℝ) : TopologicalSpace (PrivateInput N H R Up eps U) := by
  letI : TopologicalSpace (Input N H R (Up*(1+eps)) U) := inferInstance
  letI : TopologicalSpace (ProbabilityMeasure (Signal H R (Up*(1+eps)))) := inferInstance
  infer_instance

def privateEndogenous {N H : ℕ} {R Up eps U : ℝ} (heps : 0≤ eps)
    (p : PrivateInput N H R Up eps U) (z : Fin N → unitInterval) :
    PrivatePayoffContinuity.EndogenousInput N H R Up eps 1 (U*(1+eps)) :=
  (parameter heps p.1 z,p.2)

lemma continuous_privateEndogenous {N H : ℕ} {R Up eps U : ℝ} (heps : 0≤ eps) :
    Continuous (fun p : PrivateInput N H R Up eps U×(Fin N → unitInterval) =>
      privateEndogenous heps p.1 p.2) :=
  ((continuous_parameter heps).comp
    ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).prodMk
      (continuous_snd.comp continuous_fst)

def privateUtility {N H c : ℕ} {R Up eps U : ℝ} (hR : 0< R) (heps : 0≤ eps)
    (ξ : ℝ) (j : Fin H) (p : ℝ×PrivateInput N H R Up eps U) : ℝ :=
  ∫ z : Fin N → unitInterval,
    p.1*PrivatePayoffContinuity.averagedInclusion (c:=c) hR heps ξ j
      (PrivatePayoffContinuity.averagingInput (c:=c) (ξ:=ξ) (privateEndogenous heps p.2 z))-
    PrivatePayoffContinuity.averagedPayment (c:=c) hR heps ξ j
      (PrivatePayoffContinuity.averagingInput (c:=c) (ξ:=ξ) (privateEndogenous heps p.2 z))
      ∂Measure.pi (fun _ : Fin N => (volume : Measure unitInterval))

theorem continuous_privateUtility {N H c : ℕ} {R Up eps U ξ : ℝ}
    (hR : 0< R) (heps : 0< eps) (hξ : 0< ξ) (j : Fin H) :
    Continuous (privateUtility (N:=N) (c:=c) (Up:=Up) (U:=U) hR heps.le ξ j) := by
  letI : TopologicalSpace (ProbabilityMeasure (Fin N → unitInterval)) := inferInstance
  letI : TopologicalSpace (ℝ×PrivateInput N H R Up eps U) := inferInstance
  have hf := (PrivatePayoffContinuity.continuous_endogenousFocalUtility
    (N:=N) (c:=c) (U:=Up) (lo:=(1:ℝ)) (hi:=U*(1+eps)) hR heps hξ (by norm_num) j).comp
      ((continuous_fst.comp continuous_fst).prodMk
        ((continuous_privateEndogenous heps.le).comp
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd)))
  let μ : ProbabilityMeasure (Fin N → unitInterval) :=
    ⟨Measure.pi (fun _ : Fin N => (volume : Measure unitInterval)),inferInstance⟩
  have hμ : Continuous (fun _ : ℝ×PrivateInput N H R Up eps U => μ) := continuous_const
  have h := (continuous_law_integral (P:=ℝ×PrivateInput N H R Up eps U)
    (X:=Fin N → unitInterval) _ hf).comp (continuous_id.prodMk hμ)
  exact h

end FCAppendix.Affine.Tail04.EqualNoisyUtilities
