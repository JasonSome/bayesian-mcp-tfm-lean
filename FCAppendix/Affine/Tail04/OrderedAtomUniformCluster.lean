import FCAppendix.Affine.Tail04.OrderedAtomClusterLaws
import FCAppendix.Affine.Tail04.OrderedAtomNoiseRadius

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomUniformCluster
open MeasureTheory ProbabilityTheory Set Classical
open Existence.Distributional OriginalValues CompactSourceBidLaws
open FiniteTailNoisyGame SourceTailNoisyFixedPoint OrderedOriginalNoisySequence
open LatentNoisyPopulation OrderedAtomActiveGeometry OrderedAtomClusterBound
open OriginalActiveCrossingCarrier OrderedAtomFiniteGain ActiveGainUniformModulus
open ActualActiveFiniteGain AllCountActiveFiniteGain

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (N : ℕ)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v→ H≤ upperBid v)
  (S : Sequence D P t ht (N+1))

def originalLaw (j : ℕ) : Measure Draw :=
  drawLaw (S.data j) P t ht πL (S.law j) upperBid hupperBid

instance originalLaw_probability (j : ℕ) :
    IsProbabilityMeasure (originalLaw D P t ht N πL upperBid hupperBid S j) :=
  inferInstanceAs (IsProbabilityMeasure
    (drawLaw (S.data j) P t ht πL (S.law j) upperBid hupperBid))

include hfloor in
theorem exists_sequence_cluster_radius {C e : ℝ}
    (hN : 0< N) (hξh : D.ξ<1/2) (hη : D.eta=1-2*D.ξ)
    (heps : D.eps≤1) (hC : 1≤ C) (hBC : D.B≤ C) (hCF : C< D.F)
    (hFtwo : D.F≤2) (he : 0< e)
    (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+2:ℕ)*
      (tailMass P t/(partialMass+tailMass P t)))≤ D.R) :
    ∃ δ : ℝ,0< δ ∧ ∀ j : ℕ,∀ b r : ℝ,0< r → 6*r< δ →
      (S.eps j:ℝ)*D.U≤ r → ∀ y : Icc (1:ℝ) D.U,(y:ℝ)=b+2*r →
      ((y:ℝ)≤1+D.u ∨ (∀ x∈Ioo (b-r) (b+r),1+D.u< x) ∨
        ((S.law j 0).1 : Measure _)
          (LatentSpeciesCalculus.typedCluster D P t 0 (Ioo (b-r) (b+r)))=0) → ∀ εbad : ℝ,
      (∀ i : Fin (N+1),∀ x∈cluster D P t (Ioo (b-r) (b+r)),
        ∀ w∈physicalCarrier (S.data j) P hdR H
          ((S.physical_cap_le j).trans_lt hBH) b r,
          (∫ row,carrierBeta (S.data j) P t ht hdR H
            ((S.physical_cap_le j).trans_lt hBH) (N+1) y (x,restore i w row)
              ∂Measure.pi (fun _ : Fin N =>
                originalLaw D P t ht N πL upperBid hupperBid S j))≤ εbad) →
      populationCoefficient (N+2) D.ξ D.width (minFlag D) D.F C*(N+1:ℕ)*
          (1/2-(75/4:ℝ)/Real.sqrt N)*
            ((originalLaw D P t ht N πL upperBid hupperBid S j).real
              (cluster D P t (Ioo (b-r) (b+r))))^2≤
        (t+2*C+1)*(N+1:ℕ)*εbad*
          (originalLaw D P t ht N πL upperBid hupperBid S j).real
            (cluster D P t (Ioo (b-r) (b+r)))*
          (originalLaw D P t ht N πL upperBid hupperBid S j).real
            (physicalCarrier (S.data j) P hdR H
              ((S.physical_cap_le j).trans_lt hBH) b r)+
        (2*e+6*smoothCoefficient D.ξ C t*r)*
          (originalLaw D P t ht N πL upperBid hupperBid S j).real
            (cluster D P t (Ioo (b-r) (b+r))) := by
  obtain ⟨δ,hδ,hgain⟩ := OrderedAtomNoiseRadius.exists_uniform_noise_gain_radius
    D P t ht (N+1) hξh.le hη hC hBC hCF.le (P.M_pos.trans ht).le he
  refine ⟨δ,hδ,?_⟩
  intro j
  have hepsj : (S.data j).eps≤1 := (S.noise_small j).le.trans heps
  have hh := original_cluster_bound_from_radius (S.data j) P t ht hdR H
    ((S.physical_cap_le j).trans_lt hBH) N πL (S.law j) upperBid hupperBid hfloor
      hN hξh hη hepsj hC ((S.physical_cap_le j).trans hBC) hCF hFtwo he
        (S.rare_guard hrare j) (S.optimal j) δ
          (hgain (S.eps j) (S.noise_positive j) (S.noise_small j))
  exact hh

end FCAppendix.Affine.Tail04.OrderedAtomUniformCluster
