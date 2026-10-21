import FCAppendix.Affine.Tail04.OrderedAtomContraction
import FCAppendix.Affine.Tail04.SourceActiveErrorRates
import FCAppendix.Affine.Tail04.OrderedAtomRestoredGuard

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomBetaControl
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues FiniteTailNoisyGame SourceTailNoisyFixedPoint
open OrderedOriginalNoisySequence NativeNoisySource LatentNoisyPopulation
open OrderedAtomActiveGeometry OrderedAtomClusterBound OrderedAtomUniformCluster
open OrderedAtomContraction OrderedAtomRestoredBeta OrderedAtomActiveLaw OrderedAtomActiveIC
open OrderedAtomFiniteGain SourceActiveErrorRates OrderedAtomFlagVariation OriginalActiveCrossingCarrier
open SourceMomentRectangle SourceMenuPopulation MenuError

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (N : ℕ)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v→ H≤ upperBid v)
  (S : Sequence D P t ht (N+1))

lemma bulkWidth_le (j : ℕ) : bulkPhysicalWidth (S.data j)≤ bulkPhysicalWidth D := by
  change (1+D.u)*(1+(S.eps j:ℝ))-1≤(1+D.u)*(1+D.eps)-1
  exact sub_le_sub_right (mul_le_mul_of_nonneg_left
    (by linarith [S.noise_small j]) (by linarith [D.hu])) 1

include hfloor in
theorem original_conditional_beta_control
    (hcap : D.c=twoCapacity (99/200) N) (hN : 0< N)
    (hξh : D.ξ<1/2) (hF : D.F=Central.B D.ξ) (hR : D.R=Central.R D.ξ)
    (hflags : ∀ reg,D.e0 reg=baseFlag P reg) (heps : D.eps≤1)
    (huB : 1+bulkPhysicalWidth D< Central.B D.ξ)
    (hRp : D.V≤ Central.R D.ξ+D.ξ/1000)
    (hsmall : relativeError P.zeta (bulkPhysicalWidth D) (Central.B D.ξ)≤ D.ξ/1000)
    (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
    (hwγ : D.width≤ γ D.ξ)
    (hroom : ∀ reg,32/(N:ℝ)≤ radius D.ξ (centerMoment P reg))
    (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+2:ℕ)*
      (tailMass P t/(partialMass+tailMass P t)))≤ D.R) :
    ConditionalBetaControl D P t ht hdR H hBH N πL upperBid hupperBid S
      (sourceError P D.ξ N) := by
  intro e he
  obtain ⟨rf,hrf,hmod⟩ := exists_source_pair_modulus D P t ht (N+1) D.B he
  have hrad (reg : Bool) : 0< radius D.ξ (centerMoment P reg) :=
    SourcePartialPublicGuard.guard_radius_positive P D.hξ reg
  let δ := min rf (min (radius D.ξ (centerMoment P false)/2)
    (radius D.ξ (centerMoment P true)/2))
  have hδ : 0< δ := lt_min hrf (lt_min (half_pos (hrad false)) (half_pos (hrad true)))
  refine ⟨δ,hδ,?_⟩
  intro j b r hr hsmallr hnoise y hy i x hx w hw
  let Dj := S.data j
  let HBj : Dj.B< H := (S.physical_cap_le j).trans_lt hBH
  let μ := originalLaw D P t ht N πL upperBid hupperBid S j
  let bb := latentBid Dj P hdR H HBj x
  let yy := raisedBid Dj y x
  have geom := cluster_geometry Dj P t hdR H HBj
    ((S.noise_small j).le.trans heps) b r hr hnoise y hy x hx
  have hxy : (bb:ℝ)≤ yy := geom.2.1.le
  have hdist : (yy:ℝ)-(bb:ℝ)<6*r := geom.2.2.2.2
  have hnew : (yy:ℝ)-(bb:ℝ)< rf :=
    hdist.trans (hsmallr.trans_le (min_le_left _ _))
  have hnear (reg : Bool) : (yy:ℝ)-(bb:ℝ)≤ radius D.ξ (centerMoment P reg)/2 := by
    cases reg
    · exact (hdist.trans (hsmallr.trans_le ((min_le_right _ _).trans (min_le_left _ _)))).le
    · exact (hdist.trans (hsmallr.trans_le ((min_le_right _ _).trans (min_le_right _ _)))).le
  have hbulkj := bulkWidth_le D P t ht N S j
  have huBj : 1+bulkPhysicalWidth Dj< Central.B D.ξ :=
    (add_le_add (le_refl (1:ℝ)) hbulkj).trans_lt huB
  have hcoef : 0≤1+2/(Central.B D.ξ-1) := by
    have hh : 0< Central.B D.ξ-1 := by unfold Central.B;linarith [D.hξ]
    positivity
  have hmj : relativeError P.zeta (bulkPhysicalWidth Dj) (Central.B D.ξ)≤ D.ξ/1000 :=
    (add_le_add (le_refl P.zeta) (mul_le_mul_of_nonneg_right hbulkj hcoef)).trans hsmall
  have hreg (reg : Bool) :
      (∫ row,carrierRegimeBeta Dj P t ht hdR H HBj (N+1) reg y (x,restore i w row)
        ∂Measure.pi (fun _ : Fin N => μ))≤2*sourceError P D.ξ N+e := by
    have htransport := original_carrierBeta_integral Dj P t ht hdR H HBj N πL (S.law j)
      upperBid hupperBid hfloor (S.rare_guard hrare j) reg i x w y
    have hh := OrderedAtomRestoredGuard.native_restored_beta_bound Dj P t ht hdR H HBj
      πL (S.law j) upperBid hupperBid hfloor N (S.rare_guard hrare j)
      hcap hN hξh hF hR hflags huBj ((S.partial_cap_le j).trans hRp)
      hmj hmSmall hwγ hroom reg i (realize Dj w) hw.1 bb yy hxy (hnear reg)
      e rf D.B (S.physical_cap_le j) hrf hnew
        (fun kind b' d' hbd => hmod kind reg b' d' hbd)
    change _ ≤ 2*(10*Real.exp (-(N:ℝ)*(radius D.ξ (centerMoment P reg))^2/200)+
      Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2))+e at hh
    exact htransport.le.trans (hh.trans (by linarith [regime_error_le P D.ξ N reg]))
  have hi (reg : Bool) : Integrable
      (fun row => carrierRegimeBeta Dj P t ht hdR H HBj (N+1) reg y (x,restore i w row))
      (Measure.pi (fun _ : Fin N => μ)) := by
    have hm := measurable_restoredBeta Dj P t ht
      (latentTag Dj P hdR H HBj) (latentBid Dj P hdR H HBj)
      (measurable_latentTag Dj P hdR H HBj) (measurable_latentBid Dj P hdR H HBj)
      reg i w bb yy
    apply Integrable.of_bound hm.aestronglyMeasurable 2
    exact ae_of_all _ fun row => by
      have hh := restoredBeta_bounds Dj P t ht
        (latentTag Dj P hdR H HBj) (latentBid Dj P hdR H HBj) reg i w bb yy row
      rw [Real.norm_eq_abs,abs_of_nonneg hh.1]
      exact hh.2
  change (∫ row,(1-(D.regimeShare:ℝ))*
      carrierRegimeBeta Dj P t ht hdR H HBj (N+1) false y (x,restore i w row)+
      (D.regimeShare:ℝ)*carrierRegimeBeta Dj P t ht hdR H HBj (N+1) true y (x,restore i w row)
        ∂Measure.pi (fun _ : Fin N => μ))≤_
  rw [integral_add ((hi false).const_mul _) ((hi true).const_mul _),integral_const_mul,integral_const_mul]
  have h0 := mul_le_mul_of_nonneg_left (hreg false) (sub_nonneg.mpr D.regimeShare.2.2)
  have h1 := mul_le_mul_of_nonneg_left (hreg true) D.regimeShare.2.1
  nlinarith only [h0,h1]

end FCAppendix.Affine.Tail04.OrderedAtomBetaControl
