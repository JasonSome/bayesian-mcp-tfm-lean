import FCAppendix.Affine.Tail04.OrderedAtomSupport

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomProfileCarrier
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedNativeNoisySource LatentNoisyPopulation
open LatentSpeciesCalculus OrderedNativeBandCarrierIC OrderedAtomBandCarrier
open OrderedAtomSupport OriginalFiniteFibers NativeDeletedCounts
open scoped BigOperators

abbrev ProfileSample (N : ℕ) := (Fin (N+1) → Draw)×(Fin 2 → NativeLocalPolicy.Seed)

def profileToCarrier {N : ℕ} (i : Fin (N+1)) (z : ProfileSample N) : Draw×OrderedNativeBandCarrierIC.Background N :=
  (z.1 i,((fun j => z.1 (i.succAbove j)),z.2))

lemma measurable_profileToCarrier {N : ℕ} (i : Fin (N+1)) : Measurable (profileToCarrier i) :=
  ((measurable_pi_apply i).comp measurable_fst).prodMk
    ((measurable_pi_lambda _ (fun j => (measurable_pi_apply (i.succAbove j)).comp measurable_fst)).prodMk
      measurable_snd)

theorem profileToCarrier_preserves {N : ℕ} (μ : Measure Draw) [IsProbabilityMeasure μ]
    (ν : Measure (Fin 2 → NativeLocalPolicy.Seed)) [IsProbabilityMeasure ν]
    (i : Fin (N+1)) : MeasurePreserving (profileToCarrier i)
      ((Measure.pi (fun _ : Fin (N+1) => μ)).prod ν)
      (μ.prod ((Measure.pi (fun _ : Fin N => μ)).prod ν)) := by
  exact (measurePreserving_prodAssoc μ (Measure.pi (fun _ : Fin N => μ)) ν).comp
    ((measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ) i).prod (MeasurePreserving.id ν))

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (hfloor : ∀ v,t< v → H≤ upperBid v)
  (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)

local notation "Γ" => OrderedNativeNoisySource.game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "μ" => drawLaw D P t ht πL π upperBid hupperBid

include hrare in
private lemma expanded_rare :
    (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
      ((activeMass P.theta*P.zeta*powerTail P.M 10 t)/
        (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)))≤D.R := by
  simpa only [tailMass] using hrare

local notation "ν" => OrderedNativeBandCarrierIC.background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N
  (expanded_rare D P t N hrare)
local notation "σ" => Measure.pi (fun _ : Fin 2 => FiniteGame.seedLaw Γ)

def profileLaw : Measure (ProfileSample N) := (Measure.pi (fun _ : Fin (N+1) => μ)).prod σ

def profileGain (i : Fin (N+1)) (k : Fin 3) (y : Icc (bidLo D k) (bidHi D k))
    (J : Set ℝ) (z : ProfileSample N) : ℝ :=
  if z.1 i∈bandCluster k J then
    rawGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y
      ((bidLo_pos D k).le.trans y.2.1) (profileToCarrier i z) else 0

lemma measurable_profileGain (i : Fin (N+1)) (k : Fin 3)
    (y : Icc (bidLo D k) (bidHi D k)) (J : Set ℝ) (hJ : MeasurableSet J) :
    Measurable (profileGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y J) :=
  Measurable.ite ((measurableSet_bandCluster k J hJ).preimage
    ((measurable_pi_apply i).comp measurable_fst))
    ((measurable_rawGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y
      ((bidLo_pos D k).le.trans y.2.1)).comp (measurable_profileToCarrier i)) measurable_const

theorem profileGain_integral (i : Fin (N+1)) (k : Fin 3)
    (y : Icc (bidLo D k) (bidHi D k)) (J : Set ℝ) (hJ : MeasurableSet J) :
    (∫ z,profileGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y J z
      ∂profileLaw D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare)=
      ∫ z,rawGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y
        ((bidLo_pos D k).le.trans y.2.1) z ∂((μ).restrict (bandCluster k J)).prod ν := by
  let f : Draw×OrderedNativeBandCarrierIC.Background N → ℝ :=
    (bandCluster k J×ˢ univ).indicator
      (rawGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y
        ((bidLo_pos D k).le.trans y.2.1))
  have hf : Measurable f :=
    (measurable_rawGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y
      ((bidLo_pos D k).le.trans y.2.1)).indicator
        ((measurableSet_bandCluster k J hJ).prod MeasurableSet.univ)
  have hp : MeasurePreserving (profileToCarrier i)
      (profileLaw D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare) ((μ).prod ν) :=
    profileToCarrier_preserves μ σ i
  have hprofile (z : ProfileSample N) :
      profileGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y J z=
        f (profileToCarrier i z) := by
    simp only [profileGain,f,Set.indicator,Set.mem_prod,Set.mem_univ,and_true,profileToCarrier]
  trans ∫ z,f (profileToCarrier i z)
    ∂profileLaw D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
  · exact integral_congr_ae (ae_of_all _ hprofile)
  rw [←integral_map hp.measurable.aemeasurable hf.aestronglyMeasurable,hp.map_eq,
    integral_indicator ((measurableSet_bandCluster k J hJ).prod MeasurableSet.univ),
    ←Measure.restrict_prod_eq_prod_univ]

theorem profile_noisy_carrier_IC (i : Fin (N+1)) (k : Fin 3)
    (y : Icc (bidLo D k) (bidHi D k)) (J : Set ℝ) (hJ : MeasurableSet J)
    (hidentity : ∀ x,
      (∫ u,(problem Γ i).payoff (x.1:ℝ) (physicalBandAction D P t k x u)
        ∂(volume : Measure unitInterval))=SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π,x))
    (hC1 : AllActionOptimal (π k) (fun x => SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π,x))) :
    (∫ z,profileGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y J z
      ∂profileLaw D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare)≤0 := by
  rw [profileGain_integral D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y J hJ]
  exact original_noisy_carrier_IC D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
    i k y J hJ hidentity hC1

def fullSample (i : Fin (N+1)) (z : ProfileSample N) : Sample (N+1) 2 NativeLocalPolicy.Seed :=
  ((fun l => realize D (z.1 l),z.2),(z.1 i).2)

lemma measurable_fullSample (i : Fin (N+1)) : Measurable (fullSample D (N:=N) i) :=
  ((measurable_pi_lambda _ (fun l => (measurable_realize D).comp
    ((measurable_pi_apply l).comp measurable_fst))).prodMk measurable_snd).prodMk
      (measurable_snd.comp ((measurable_pi_apply i).comp measurable_fst))

lemma nativeDeleted_profileToCarrier (i : Fin (N+1)) (z : ProfileSample N) :
    nativeDeleted D (N:=N) ((profileToCarrier i z).2,(profileToCarrier i z).1.2)=
      deleteSample i (fullSample D (N:=N) i z) := rfl

def profileCount (i : Fin (N+1)) (action : Draw → JointAction 2)
    (z : ProfileSample N) : ℝ :=
  (focalCount Γ i (action (z.1 i)) (fullSample D (N:=N) i z)).val

lemma measurable_profileCount (i : Fin (N+1)) (action : Draw → JointAction 2)
    (ha : Measurable action) :
    Measurable (profileCount D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i action) := by
  have hc : Measurable (fun z : ProfileSample N =>
      focalCount Γ i (action (z.1 i)) (fullSample D (N:=N) i z)) := by
    change Measurable ((fun p : JointAction 2×Sample (N+1) 2 NativeLocalPolicy.Seed =>
      focalCount Γ i p.1 p.2) ∘ (fun z : ProfileSample N =>
        (action (z.1 i),fullSample D (N:=N) i z)))
    exact (measurable_focalCount_joint Γ i).comp
      ((ha.comp ((measurable_pi_apply i).comp measurable_fst)).prodMk (measurable_fullSample D (N:=N) i))
  exact (measurable_of_countable (fun r : Fin 3 => (r.val:ℝ))).comp hc

theorem realizedPay_profileToCarrier (i : Fin (N+1)) (action : Draw → JointAction 2)
    (z : ProfileSample N) :
    realizedPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i action (profileToCarrier i z)=
      userPayoff (value (z.1 i)) (action (z.1 i)).bid (Γ).g (Γ).A.charge (Γ).G.charge
        (focalCount Γ i (action (z.1 i)) (fullSample D (N:=N) i z)).val := by
  change userPayoff _ _ _ _ _ (deletedCount Γ i _ _).val=_
  rw [nativeDeleted_profileToCarrier]
  unfold deletedCount
  rw [focalCount_restore_delete]
  rfl

end FCAppendix.Affine.Tail04.OrderedAtomProfileCarrier
