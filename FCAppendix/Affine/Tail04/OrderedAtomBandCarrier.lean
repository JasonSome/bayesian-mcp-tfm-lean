import FCAppendix.Affine.Tail04.OrderedNativeBandCarrierIC

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomBandCarrier
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedNativeNoisySource LatentNoisyPopulation
open LatentSpeciesCalculus OriginalFiniteFibers NativeDeletedCounts OrderedNativeBandCarrierIC
open scoped BigOperators

private lemma measurable_sample_userPayoff {N c : ℕ} {Seed Ω : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Ω]
    (Γ : FiniteGame (N+1) 2 c Seed) (i : Fin (N+1))
    (v : Ω→ℝ) (a : Ω→JointAction 2) (s : Ω→Sample (N+1) 2 Seed)
    (hv : Measurable v) (ha : Measurable a) (hs : Measurable s) :
    Measurable (fun z => userPayoff (v z) (a z).bid Γ.g Γ.A.charge Γ.G.charge
      (focalCount Γ i (a z) (s z)).val) := by
  have hb : Measurable (fun z => (a z).bid) := (measurable_bid 2).comp ha
  have hc : Measurable (fun z => focalCount Γ i (a z) (s z)) := by
    change Measurable ((fun p : JointAction 2×Sample (N+1) 2 Seed => focalCount Γ i p.1 p.2) ∘
      (fun z => (a z,s z)))
    exact (measurable_focalCount_joint Γ i).comp (ha.prodMk hs)
  exact measurable_userPayoff v (fun z => (a z).bid) Γ.g Γ.A.charge Γ.G.charge
    (fun z => focalCount Γ i (a z) (s z)) hv hb hc

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (hfloor : ∀ v,t< v → H≤ upperBid v)
  (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)

local notation "Γ" => OrderedNativeNoisySource.game D P t ht hdR H hBH πL π upperBid hupperBid hfloor (N+1) hrare
local notation "μ" => drawLaw D P t ht πL π upperBid hupperBid
local notation "ν" => background D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare

def realizedPay (i : Fin (N+1)) (action : Draw → JointAction 2) (z : Draw×Background N) : ℝ :=
  userPayoff (value z.1) (action z.1).bid (Γ).g (Γ).A.charge (Γ).G.charge
    (deletedCount Γ i (action z.1) (nativeDeleted D (N:=N) (z.2,z.1.2))).val

lemma measurable_realizedPay (i : Fin (N+1)) (action : Draw → JointAction 2)
    (ha : Measurable action) :
    Measurable (realizedPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i action) := by
  have hs : Measurable (fun z : Draw×Background N =>
      restoreSample i (nativeDeleted D (N:=N) (z.2,z.1.2))) :=
    (measurable_restoreSample i).comp ((measurable_nativeDeleted D (N:=N)).comp
      (measurable_snd.prodMk measurable_fst.snd))
  change Measurable (fun z : Draw×Background N =>
    userPayoff (value z.1) (action z.1).bid (Γ).g (Γ).A.charge (Γ).G.charge
      (focalCount Γ i (action z.1) (restoreSample i
        (nativeDeleted D (N:=N) (z.2,z.1.2)))).val)
  exact measurable_sample_userPayoff Γ i (fun z : Draw×Background N => value z.1)
    (fun z => action z.1)
    (fun z => restoreSample i (nativeDeleted D (N:=N) (z.2,z.1.2)))
    (measurable_value.comp measurable_fst) (ha.comp measurable_fst) hs

def oldAction (z : Draw) : JointAction 2 := (realize D z).1.2

lemma measurable_oldAction : Measurable (oldAction D) :=
  measurable_snd.comp (measurable_fst.comp (measurable_realize D))

def raisedAction (k : Fin 3) (y : ℝ) (hy : 0≤ y) (z : Draw) : JointAction 2 :=
  noisyAction D.eps D.heps.le ⟨y,hy,bandRoutes k,bandRoutes_le k⟩ z.1.2

lemma measurable_raisedAction (k : Fin 3) (y : ℝ) (hy : 0≤ y) :
    Measurable (raisedAction D k y hy) :=
  (measurable_noisyAction D.eps D.heps.le).comp
    (measurable_const.prodMk measurable_fst.snd)

def rawGain (i : Fin (N+1)) (k : Fin 3) (y : ℝ) (hy : 0≤ y) (z : Draw×Background N) : ℝ :=
  realizedPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i (raisedAction D k y hy) z-
  realizedPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i (oldAction D) z

lemma measurable_rawGain (i : Fin (N+1)) (k : Fin 3) (y : ℝ) (hy : 0≤ y) :
    Measurable (rawGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y hy) :=
  (measurable_realizedPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i _
    (measurable_raisedAction D k y hy)).sub
      (measurable_realizedPay D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i _
        (measurable_oldAction D))

theorem rawGain_bandDraw (i : Fin (N+1)) (k : Fin 3)
    (y : Icc (bidLo D k) (bidHi D k)) (z : BandDraw D P t k×Background N) :
    rawGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y
      ((bidLo_pos D k).le.trans y.2.1) (bandDraw D P t k z.1,z.2)=
      bandGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k (fun _ => y) z := by
  fin_cases k <;>
    simp [rawGain,realizedPay,raisedAction,oldAction,bandGain,bandPay,
      physicalBandAction,bandDraw,mark,realize,implementJoint,bandSpecies,bandRoutes,
      bandBase,bandAction,noisyAction,noisyJoint,value]

theorem original_gain_integral (i : Fin (N+1)) (k : Fin 3)
    (y : Icc (bidLo D k) (bidHi D k)) (J : Set ℝ) (hJ : MeasurableSet J) :
    (∫ z,rawGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y
      ((bidLo_pos D k).le.trans y.2.1) z ∂((μ).restrict (bandCluster k J)).prod ν)=
      (species P t ht).mass (bandSpecies k)*
        ∫ z,bandGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k (fun _ => y) z
          ∂((((((π k).1 : Measure _).restrict (typedCluster D P t k J)).prod
            (volume : Measure unitInterval)).prod (permLaw 2)).prod ν) := by
  rw [drawLaw_restrict_bandCluster D P t ht πL π upperBid hupperBid k J hJ,
    Measure.prod_smul_left,integral_smul_measure,
    ENNReal.toReal_ofReal ((species P t ht).nonneg (bandSpecies k))]
  congr 1
  rw [show
      (((((((π k).1 : Measure _).restrict (typedCluster D P t k J)).prod
        (volume : Measure unitInterval)).prod (permLaw 2)).map (bandDraw D P t k)).prod ν)=
      ((((((π k).1 : Measure _).restrict (typedCluster D P t k J)).prod
        (volume : Measure unitInterval)).prod (permLaw 2)).prod ν).map
          (Prod.map (bandDraw D P t k) id) by
        simpa only [Measure.map_id] using Measure.map_prod_map _ _
          (measurable_bandDraw D P t k) measurable_id]
  rw [integral_map ((measurable_bandDraw D P t k).prodMap measurable_id).aemeasurable
    (measurable_rawGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y
      ((bidLo_pos D k).le.trans y.2.1)).aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ fun z => rawGain_bandDraw D P t ht πL π upperBid hupperBid
    hdR H hBH hfloor N hrare i k y z)

theorem original_noisy_carrier_IC (i : Fin (N+1)) (k : Fin 3)
    (y : Icc (bidLo D k) (bidHi D k)) (J : Set ℝ) (hJ : MeasurableSet J)
    (hidentity : ∀ x,
      (∫ u,(problem Γ i).payoff (x.1:ℝ) (physicalBandAction D P t k x u)
        ∂(volume : Measure unitInterval))=SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π,x))
    (hC1 : AllActionOptimal (π k) (fun x => SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π,x))) :
    (∫ z,rawGain D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y
      ((bidLo_pos D k).le.trans y.2.1) z ∂((μ).restrict (bandCluster k J)).prod ν)≤0 := by
  rw [original_gain_integral D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare i k y J hJ]
  exact mul_nonpos_of_nonneg_of_nonpos ((species P t ht).nonneg (bandSpecies k))
    (integrated_band_IC_of_native_identity D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare
      i k (fun _ => y) measurable_const J hidentity hC1)

end FCAppendix.Affine.Tail04.OrderedAtomBandCarrier
