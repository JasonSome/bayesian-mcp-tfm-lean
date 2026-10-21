import FCAppendix.Affine.Tail04.OrderedAtomCountExceptions

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomClusterBound
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues CompactSourceBidLaws
open FiniteTailNoisyGame SourceTailNoisyFixedPoint LatentNoisyPopulation LatentSpeciesCalculus
open OrderedAtomActiveLaw OrderedAtomActiveIC OrderedAtomActiveCompression
open OriginalActiveCrossingCarrier OrderedAtomActiveGeometry OrderedAtomCountExceptions
open OrderedAtomFiniteGain ActiveGainUniformModulus AllCountActiveFiniteGain
open IntegratedActiveFiniteGain ActualActiveFiniteGain

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (N : ℕ)
local notation "Ds" => installOriginal D P t ht
local notation "tag" => latentTag D P hdR H hBH
local notation "bid" => latentBid D P hdR H hBH

def carrierRegimeBeta (reg : Bool) (y : Icc (1:ℝ) D.U)
    (z : Draw×(Fin N→ Draw)) : ℝ :=
  beta D P t ht N (tags tag z.2) reg
    (focalRow Ds (tags tag z.2) bid (bid z.1) z.2) (raisedBid D y z.1)

def carrierBeta (y : Icc (1:ℝ) D.U) (z : Draw×(Fin N→ Draw)) : ℝ :=
  meanBeta D P t ht N (tags tag z.2)
    (focalRow Ds (tags tag z.2) bid (bid z.1) z.2) (raisedBid D y z.1)

lemma measurable_carrierRegimeBeta (reg : Bool) (y : Icc (1:ℝ) D.U) :
    Measurable (carrierRegimeBeta D P t ht hdR H hBH N reg y) := by
  apply LocalCoordinates.measurable_finite_eval
    (fun z : Draw×(Fin N→Draw) => tags tag z.2)
    (fun z kind => beta D P t ht N kind reg
      (focalRow Ds kind bid (bid z.1) z.2) (raisedBid D y z.1))
    ((measurable_tags tag (measurable_latentTag D P hdR H hBH)).comp measurable_snd)
  intro kind
  have hb : Measurable (fun z : Draw×(Fin N→ Draw) =>
      fun j => (focalRow Ds kind bid (bid z.1) z.2 j:ℝ)) :=
    measurable_pi_lambda _ fun j => measurable_subtype_coe.comp
      ((measurable_pi_apply j).comp ((measurable_focalRow Ds kind bid
        (measurable_latentBid D P hdR H hBH)).comp
          (((measurable_latentBid D P hdR H hBH).comp measurable_fst).prodMk measurable_snd)))
  have hy : Measurable (fun z : Draw×(Fin N→Draw) => (raisedBid D y z.1:ℝ)) :=
    ((measurable_raisedBid D y).subtype_val).comp measurable_fst
  have hw := measurable_weightFailure (A:=(Ds).count kind 1+1) (min ((Ds).count kind 2) ((Ds).count kind 3)) (max ((Ds).count kind 2) ((Ds).count kind 3)) D.c
    D.ξ D.B D.R D.V D.width (D.e0 reg) D.F reg (decide (0< (Ds).count kind 0))
      ((Ds).marksLaw _) ((Ds).marksLaw _)
  exact (hw.comp (measurable_freeze _ hb 0 _ hy)).add
    (hw.comp (Resample.measurable_update_pair 0 |>.comp (hy.prodMk hb)))

lemma measurable_carrierBeta (y : Icc (1:ℝ) D.U) :
    Measurable (carrierBeta D P t ht hdR H hBH N y) :=
  ((measurable_carrierRegimeBeta D P t ht hdR H hBH N false y).const_mul _).add
    ((measurable_carrierRegimeBeta D P t ht hdR H hBH N true y).const_mul _)

lemma carrierBeta_bounds (y : Icc (1:ℝ) D.U) (z : Draw×(Fin N→ Draw)) :
    carrierBeta D P t ht hdR H hBH N y z∈Icc (0:ℝ) 2 :=
  meanBeta_bounds D P t ht N _ _ _

lemma focalRow_update (kind : Fin N→ Fin 4) (b y : Icc (1:ℝ) D.B) (row : Fin N→ Draw) :
    Function.update (focalRow Ds kind bid b row) 0 y=focalRow Ds kind bid y row := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [focalRow]
  · simp [focalRow]

include ht in
lemma physical_below_value (hFtwo : D.F≤2) (x : Draw) (hx : activeRecord D P t x) :
    (bid x:ℝ)≤ value x := by
  have hv := record_value_bounds D P t ht x hx
  have h2 : 2< P.vA-P.w := by linarith [P.partial_active_gap,P.w_pos]
  exact ((bid x).2.2.trans (D.hUF.trans hFtwo)).trans (h2.le.trans hv.1)

section Original
variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v→ H≤ upperBid v)
local notation "μsrc" => drawLaw D P t ht πL π upperBid hupperBid

include πL upperBid hupperBid hfloor in
theorem original_cluster_bound_from_radius (hN : 0< N) {C e : ℝ}
    (hξh : D.ξ<1/2) (_hη : D.eta=1-2*D.ξ) (heps : D.eps≤1)
    (hC : 1≤ C) (_hBC : D.B≤ C) (_hCF : C< D.F) (hFtwo : D.F≤2) (_he : 0< e)
    (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+2:ℕ)*
      (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
    (hC1 : ∀ k : Fin 3,AllActionOptimal (π k) (fun x => SourceOrderedNoisyFixedPoint.payoff D P t ht (N+1) k (π,x)))
    (δ : ℝ)
    (hδgain : ∀ kind : Fin (N+1)→ Fin 4,∀ μP : ProbabilityMeasure (Icc D.R D.Up),
      ∀ v∈Icc (0:ℝ) t,∀ b : Fin ((Ds).count kind 1+1)→ Icc (1:ℝ) D.B,
      (∀ i j,i≠j→(b i:ℝ)≠(b j:ℝ)) → (b 0:ℝ)≤ v →
      ∀ y : Icc (1:ℝ) D.B,(b 0:ℝ)< y → (y:ℝ)-(b 0:ℝ)< δ →
        populationCoefficient (N+2) D.ξ D.width (minFlag D) D.F C*
          (if (Ds).count kind 2=(Ds).count kind 3 then 0 else
            AtypicalFittingFiniteLoss.crossingCount (fun j => (b j:ℝ)) 0 y)-
          (t+2*C+1)*meanBeta D P t ht (N+1) kind b y*
            AtypicalFittingFiniteLoss.crossingCount (fun j => (b j:ℝ)) 0 y-
          2*e-smoothCoefficient D.ξ C t*((y:ℝ)-(b 0:ℝ))≤
        ActivePhysicalPayoff.regimeValue Ds ((Ds).count kind 1) (min ((Ds).count kind 2) ((Ds).count kind 3)) (max ((Ds).count kind 2) ((Ds).count kind 3)) μP v
          (decide (0< (Ds).count kind 0)) (Function.update b 0 y)-
        ActivePhysicalPayoff.regimeValue Ds ((Ds).count kind 1) (min ((Ds).count kind 2) ((Ds).count kind 3)) (max ((Ds).count kind 2) ((Ds).count kind 3)) μP v
          (decide (0< (Ds).count kind 0)) b) :
    ∀ b r : ℝ,0< r → 6*r< δ → D.eps*D.U≤ r →
      ∀ y : Icc (1:ℝ) D.U,(y:ℝ)=b+2*r →
      ((y:ℝ)≤1+D.u ∨ (∀ x∈Ioo (b-r) (b+r),1+D.u< x) ∨
        ((π 0).1 : Measure _) (LatentSpeciesCalculus.typedCluster D P t 0 (Ioo (b-r) (b+r)))=0) → ∀ εbad : ℝ,
      (∀ j : Fin (N+1),∀ x∈cluster D P t (Ioo (b-r) (b+r)),
        ∀ w∈physicalCarrier D P hdR H hBH b r,
          (∫ row,carrierBeta D P t ht hdR H hBH (N+1)
            y (x,restore j w row)
              ∂Measure.pi (fun _ : Fin N => μsrc))≤ εbad) →
      populationCoefficient (N+2) D.ξ D.width (minFlag D) D.F C*(N+1:ℕ)*
          (1/2-(75/4:ℝ)/Real.sqrt N)*((μsrc).real (cluster D P t (Ioo (b-r) (b+r))))^2≤
        (t+2*C+1)*(N+1:ℕ)*εbad*(μsrc).real (cluster D P t (Ioo (b-r) (b+r)))*
          (μsrc).real (physicalCarrier D P hdR H hBH b r)+
        (2*e+6*smoothCoefficient D.ξ C t*r)*(μsrc).real (cluster D P t (Ioo (b-r) (b+r))) := by
  have ht0 : 0< t := P.M_pos.trans ht
  intro b r hr hsmall hnoise y hy hlegal εbad hbad
  let yT : Icc (1:ℝ) D.U := y
  let E0 := cluster D P t (Ioo (b-r) (b+r))
  let F0 := physicalCarrier D P hdR H hBH b r
  let active : Set Draw := {z | tag z=1}
  let bb : Draw→ℝ := fun z => (bid z:ℝ)
  let rr : Draw→ℝ := fun z => (raisedBid D yT z:ℝ)
  let A := populationCoefficient (N+2) D.ξ D.width (minFlag D) D.F C
  let K := t+2*C+1
  let err := 2*e+6*smoothCoefficient D.ξ C t*r
  let ν := ((μsrc).restrict E0).prod (Measure.pi (fun _ : Fin (N+1) => μsrc))
  have hE : MeasurableSet E0 := measurableSet_cluster D P t _ measurableSet_Ioo
  have hF : MeasurableSet F0 := measurableSet_physicalCarrier D P hdR H hBH b r
  have ha : MeasurableSet active := measurableSet_eq_fun
    (measurable_latentTag D P hdR H hBH) measurable_const
  have hb : Measurable bb := (measurable_latentBid D P hdR H hBH).subtype_val
  have hrm : Measurable rr := (measurable_raisedBid D yT).subtype_val
  have hEa : E0⊆active := fun x hx => record_tag D P t hdR H hBH x hx.1
  have hord : ∀ x∈E0,∀ w∈E0,bb w≤ rr x := fun x hx w hw =>
    (cluster_ordered D P t hdR H hBH b r hr hnoise yT hy x w hx hw).le
  have hloc : ∀ x∈E0,∀ w,crossing active bb rr x w→ w∈F0 :=
    fun x hx w hw => crossing_in_physicalCarrier D P t hdR H hBH heps b r hr hnoise yT hy x w hx hw
  have hA : 0≤ A := by
    dsimp [A,populationCoefficient]
    have hη0 : 0≤1-2*D.ξ := by linarith
    positivity
  have hK : 0≤ K := by dsimp [K];linarith
  have hL : 0≤ smoothCoefficient D.ξ C t :=
    (by norm_num : (0:ℝ)≤2).trans (smoothCoefficient_ge_two D.hξ (by linarith) ht0.le)
  have hx : ∀ᵐ z ∂ν,z.1∈E0 :=
    (measurePreserving_fst (μ:=(μsrc).restrict E0)
      (ν:=Measure.pi (fun _ : Fin (N+1) => μsrc))).quasiMeasurePreserving.ae (ae_restrict_mem hE)
  have hgBound : ∀ᵐ z ∂ν,
      ‖gain D P t ht π hdR H hBH (N+1) yT z‖≤2*(|P.vA-P.w|+|t|+2*D.B) :=
    hx.mono fun z hz => gain_bound_on_cluster D P t hdR H hBH ht π
      (N+1) yT _ z hz
  have hpoint : ∀ᵐ z ∂ν,
      A*(if equalCounts Ds tag z then 0 else crossingCount active bb rr z)-
        K*carrierBeta D P t ht hdR H hBH (N+1) yT z*crossingCount active bb rr z-err≤
        gain D P t ht π hdR H hBH (N+1) yT z := by
    filter_upwards [hx,ae_original_carrier_distinct D P t ht πL π upperBid hupperBid
      hdR H hBH hfloor (N+1) hrare E0] with z hz hdistinct
    let kind := tags tag z.2
    let old := focalRow Ds kind bid (bid z.1) z.2
    let new := raisedBid D yT z.1
    have hv := record_value_bounds D P t ht z.1 hz.1
    have hv0 : 0≤ value z.1 := by linarith [hv.1,P.partial_active_gap,P.w_pos]
    have hgeom := cluster_geometry D P t hdR H hBH heps b r hr hnoise yT hy z.1 hz
    have hh := hδgain kind (bidMarginal (π 2).1) (value z.1) ⟨hv0,hv.2⟩ old hdistinct
      (physical_below_value D P t ht hdR H hBH hFtwo z.1 hz.1) new hgeom.2.1
        (hgeom.2.2.2.2.trans hsmall)
    have hcross := crossing_compression Ds tag bid z.1 z.2 (new:ℝ)
    have hupdate := focalRow_update D P t ht hdR H hBH (N+1) kind (bid z.1) new z.2
    have hprice := mul_le_mul_of_nonneg_left hgeom.2.2.2.2.le hL
    rw [hupdate] at hh
    rw [hcross] at hh
    have hh' : A*(if equalCounts Ds tag z then 0 else crossingCount active bb rr z)-
      K*carrierBeta D P t ht hdR H hBH (N+1) yT z*crossingCount active bb rr z-
      2*e-smoothCoefficient D.ξ C t*(rr z.1-bb z.1)≤
        gain D P t ht π hdR H hBH (N+1) yT z := by
      simpa only [A,K,carrierBeta,equalCounts,kind,crossingCount,crossing,active,bb,rr,
        gain,physicalValue,rivalValue,caseValue,old,new,focalRow,Fin.cons_zero] using! hh
    dsimp only [err]
    nlinarith only [hh',hprice]
  have heq : ∀ j : Fin (N+1),∀ x∈E0,∀ w∈E0,
      (Measure.pi (fun _ : Fin N => μsrc)).real {row | equalCounts Ds tag (x,restore j w row)}≤
        (75/4:ℝ)/Real.sqrt N := by
    intro j x hx w hw
    exact original_equalCounts_conditional D P t ht πL π upperBid hupperBid hdR H hBH hfloor
      N hrare hN j x w (hEa hw)
  have hic := original_active_cluster_IC_with_bulk_null D P t hdR H hBH ht πL π upperBid hupperBid
    hfloor (N+1) hrare y _ measurableSet_Ioo hlegal hC1
  exact integrate_cluster_gain μsrc E0 F0 active hE hF ha bb rr hb hrm hEa hord hloc
    (equalCounts Ds tag) (measurableSet_equalCounts Ds tag (measurable_latentTag D P hdR H hBH))
    (carrierBeta D P t ht hdR H hBH (N+1) yT)
    (gain D P t ht π hdR H hBH (N+1) yT)
    (measurable_carrierBeta D P t ht hdR H hBH (N+1) yT)
    (measurable_gain D P t ht π hdR H hBH (N+1) yT)
    (carrierBeta_bounds D P t ht hdR H hBH (N+1) yT)
    (2*(|P.vA-P.w|+|t|+2*D.B)) hgBound hA hK hpoint heq hbad hic

include πL upperBid hupperBid hfloor in
theorem exists_original_cluster_radius (hN : 0< N) {C e : ℝ}
    (hξh : D.ξ<1/2) (hη : D.eta=1-2*D.ξ) (heps : D.eps≤1)
    (hC : 1≤ C) (hBC : D.B≤ C) (hCF : C< D.F) (hFtwo : D.F≤2) (he : 0< e)
    (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+2:ℕ)*
      (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
    (hC1 : ∀ k : Fin 3,AllActionOptimal (π k) (fun x => SourceOrderedNoisyFixedPoint.payoff D P t ht (N+1) k (π,x))) :
    ∃ δ : ℝ,0< δ ∧ ∀ b r : ℝ,0< r → 6*r< δ → D.eps*D.U≤ r →
      ∀ y : Icc (1:ℝ) D.U,(y:ℝ)=b+2*r →
      ((y:ℝ)≤1+D.u ∨ (∀ x∈Ioo (b-r) (b+r),1+D.u< x) ∨
        ((π 0).1 : Measure _) (LatentSpeciesCalculus.typedCluster D P t 0 (Ioo (b-r) (b+r)))=0) → ∀ εbad : ℝ,
      (∀ j : Fin (N+1),∀ x∈cluster D P t (Ioo (b-r) (b+r)),
        ∀ w∈physicalCarrier D P hdR H hBH b r,
          (∫ row,carrierBeta D P t ht hdR H hBH (N+1)
            y (x,restore j w row)
              ∂Measure.pi (fun _ : Fin N => μsrc))≤ εbad) →
      populationCoefficient (N+2) D.ξ D.width (minFlag D) D.F C*(N+1:ℕ)*
          (1/2-(75/4:ℝ)/Real.sqrt N)*((μsrc).real (cluster D P t (Ioo (b-r) (b+r))))^2≤
        (t+2*C+1)*(N+1:ℕ)*εbad*(μsrc).real (cluster D P t (Ioo (b-r) (b+r)))*
          (μsrc).real (physicalCarrier D P hdR H hBH b r)+
        (2*e+6*smoothCoefficient D.ξ C t*r)*(μsrc).real (cluster D P t (Ioo (b-r) (b+r))) := by
  have ht0 : 0< t := P.M_pos.trans ht
  obtain ⟨δ,hδ,hδgain⟩ := exists_ordered_physical_gain_radius D P t ht (N+1)
    hξh.le hη hC hBC hCF.le ht0.le he
  exact ⟨δ,hδ,original_cluster_bound_from_radius D P t ht hdR H hBH N
    πL π upperBid hupperBid hfloor hN hξh hη heps hC hBC hCF hFtwo he
      hrare hC1 δ hδgain⟩

end Original
end FCAppendix.Affine.Tail04.OrderedAtomClusterBound
