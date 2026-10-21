import FCAppendix.Affine.Tail04.PartialRegimeLimit
import FCAppendix.Affine.Tail04.OrderedPartialEventRelabel
import FCAppendix.Affine.Tail04.SourcePartialPublicGuard
import FCAppendix.Affine.Tail04.OrderedZeroNativeBindings
import FCAppendix.Affine.Tail04.OrderedZeroNativeCategories

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedZeroSourcePartialCount
open MeasureTheory ProbabilityTheory Set Classical Game Bayes Filter Topology
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedNativeZeroNoiseSource OrderedZeroNativeBindings
open MenuError SourceMenuPopulation SourceMomentRectangle SourceMenuError
open OrderedNativePartialDeviation SourcePartialPublicGuard

variable (P : ValueParameters) (ξ u Up U width : ℝ) (N : ℕ)
  (hξ : 0< ξ) (hξh : ξ<1/2) (hu : 0≤ u) (huU : 1+u≤ U)
  (hRUp : Central.R ξ≤ Up) (hUp : Up<1) (hUB : U< Central.B ξ) (hw : 0< width)
local notation "cN" => iidCapacity (99/200) N
local notation "D" => SourceNoisyData.data P ξ u Up U width cN
  hξ hξh hu huU hRUp hUp hUB hw
variable (t : ℝ) (ht : P.M< t) (hdR : P.d0< (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).R) (H : ℝ) (hUH : (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).U< H)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw) P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀v,t< v→ H≤ upperBid v)
  (hrare : (1-(SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).ξ)*(SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).U+(SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).ξ*(SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).U*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ (SourceNoisyData.data P ξ u Up U width (iidCapacity (99/200) N) hξ hξh hu huU hRUp hUp hUB hw).R)
local notation "E" => regions D P hdR H hUH
local notation "K" => localData D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
local notation "Q" => publicData D P t ht hdR H hUH πL π upperBid hupperBid hfloor
local notation "Γ₀" => coreGame D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare
local notation "Γ" => game D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare

include N hdR H hUH hfloor hrare in
lemma core_joint : (Γ₀).F⊗ₘ(Γ₀).σ=ProbabilityMeasure.toMeasure (originalJoint P t ht.le (E).R (E).Rp (E).U
    ((E).d_nonneg.trans (E).d_lt_R.le) πL (partialLaw D P t ht π)
    (active D P t ht π) upperBid hupperBid) :=
  game_original_joint D P t ht hdR H hUH πL π upperBid hupperBid hfloor (N+1) hrare

variable (hN : 0< N) (huB : 1+u< Central.B ξ)
  (hRp : Up≤ Central.R ξ+ξ/1000)
  (hsmall : relativeError P.zeta u (Central.B ξ)≤ ξ/1000)
  (hmSmall : upperMass P t≤ Central.mixedR (P.theta^2)/1000)
  (hwγ : width≤ γ ξ) (hroom : ∀reg,8/(N:ℝ)≤ radius ξ (centerMoment P reg))
  (cats : FiniteLaw (Fin 4))
  (L : LowBody.ActualAtomlessLowLimit N P.d0 ξ (iidCapacity (99/200) N) cats P.originalLowLaw)
  (hL : πL=L.joint)

include u Up U width hξ hξh hu huU hRUp hUp hUB hw t ht hdR H hUH πL π upperBid hupperBid hfloor hrare hN huB hRp hsmall hmSmall hwγ hroom cats L hL in
lemma badMass_bound (i : Fin (N+1)) : badMass K Γ₀ i≤ 2*badBound P ξ N := by
  have hb := SourcePartialPublicGuard.source_badMass P E rfl t ht u hu huU πL
    (partialLaw D P t ht π) (π 0) (π 1) upperBid hupperBid hfloor ξ width hξ hξh hw
    hrare (base_duplicate_gap D) Γ₀
    (core_joint P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw t ht hdR H hUH
      πL π upperBid hupperBid hfloor hrare)
    hN huB hUB.le rfl hRp hsmall hmSmall hwγ hroom cats L hL i
  have ho := OrderedPartialEventRelabel.badMass_le_twice K Q
    (LowBody.realLowBidLaw πL.1 : Measure ℝ) (fun _ _ => rfl) Γ₀ i
  exact ho.trans (mul_le_mul_of_nonneg_left hb (by norm_num))

include ξ u Up U width hξ hξh hu huU hRUp hUp hUB hw t ht hdR H hUH πL π upperBid hupperBid hfloor hrare hN cats L hL in
lemma regime_error (i : Fin (N+1)) :
    |serviceProb K Γ₀ i-(1-P.theta)|≤
      Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2)+Real.exp (-(N:ℝ)*P.bulkWeight^2/2) := by
  rw [OrderedPartialEventRelabel.serviceProb_eq K Q
    (LowBody.realLowBidLaw πL.1 : Measure ℝ) (fun _ _ => rfl)]
  have hj := core_joint P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
    t ht hdR H hUH πL π upperBid hupperBid hfloor hrare
  have hpublic := SourcePartialPublicGuard.source_native_public P E rfl t ht u huU πL
    (partialLaw D P t ht π) (π 0) (π 1) upperBid hupperBid hfloor ξ width hξ hξh hw
    hrare (base_duplicate_gap D) Γ₀ hj
  have hcat := SourcePartialPublicGuard.source_category_nonzero P E rfl t ht u huU πL
    (partialLaw D P t ht π) (π 0) (π 1) upperBid hupperBid hfloor Γ₀ hj
  have hlow := SourcePartialPublicGuard.source_low_singletons P E rfl t ht u huU πL
    (partialLaw D P t ht π) (π 0) (π 1) upperBid hupperBid hfloor ξ Γ₀ hj cats L hL
  have hmenu := SourcePartialPublicGuard.source_menu P E rfl t ht u huU πL
    (partialLaw D P t ht π) (π 0) (π 1) upperBid hupperBid hfloor Γ₀ hj
  have hmass (k : Fin 4) : (userLaw Γ₀).real ((E).coarseTag ⁻¹' {k})=
      (originalCategories P t ht).mass k := by
    rw [measureReal_def,OrderedZeroNativeCategories.native_source_category_mass D P t ht hdR H hUH
      πL π upperBid hupperBid hfloor Γ₀ hj k,
      ENNReal.toReal_ofReal ((originalCategories P t ht).nonneg k)]
  apply PartialRegimeLimit.service_error_le_exponentials Γ₀ K Q hpublic hcat hlow hmenu
    i hN (lowMass P.theta) P.bulkWeight P.low_mass_pos P.bulkWeight_pos
  · change lowMass P.theta≤(userLaw Γ₀).real ((E).coarseTag ⁻¹' {0})
    rw [hmass];rfl
  · change P.bulkWeight≤(userLaw Γ₀).real ((E).coarseTag ⁻¹' {1})
    rw [hmass]
    change P.bulkWeight≤ P.bulkWeight+P.truncatedTailWeight t
    linarith [P.truncatedTailWeight_pos t ht]

def error (P : ValueParameters) (ξ : ℝ) (N : ℕ) : ℝ :=
  2*(badBound P ξ N+Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2)+Real.exp (-(N:ℝ)*P.bulkWeight^2/2))

lemma error_nonnegative (P : ValueParameters) (ξ : ℝ) (N : ℕ) : 0≤ error P ξ N := by
  unfold error
  have hh := badBound_nonnegative P ξ N
  positivity

lemma error_tendsto_zero (P : ValueParameters) {ξ : ℝ} (hξ : 0< ξ) :
    Tendsto (error P ξ) atTop (𝓝 0) := by
  have h0 := exponential_tendsto_zero (div_pos (sq_pos_of_pos P.low_mass_pos) (by norm_num : (0:ℝ)<2))
  have h1 := exponential_tendsto_zero (div_pos (sq_pos_of_pos P.bulkWeight_pos) (by norm_num : (0:ℝ)<2))
  have hh := ((badBound_tendsto_zero P hξ).add h0).add h1
  convert! hh.const_mul 2 using 1
  · funext n
    unfold error
    congr 1
    congr 2 <;> congr 1 <;> ring
  · norm_num

include u U width hξ hξh hu huU hRUp hUp hUB hw t ht hdR H hUH πL π upperBid hupperBid hfloor hrare hN huB hRp hsmall hmSmall hwγ hroom cats L hL in
theorem original_count_mass_error (i : Fin (N+1)) (b : Icc (D).R (D).Up) (r : Fin 3) :
    |((problem Γ i).outcome (RawRoutes.action b ((D).hR.le.trans b.2.1) 1)).mass r-
      (Counts.singletonLaw (1-P.theta) ⟨by linarith [P.theta_small],by linarith [P.theta_pos]⟩).mass r|≤
      error P ξ N := by
  rw [sourceGame_problem D P t ht hdR H hUH πL π upperBid hupperBid hfloor N hrare]
  have he := OrderedNativePartialDeviation.mass_error K Γ₀ (fun _=> rfl) i b 1 r
  have hb := badMass_bound P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
    t ht hdR H hUH πL π upperBid hupperBid hfloor hrare hN huB hRp hsmall hmSmall hwγ hroom cats L hL i
  have hreg := regime_error P ξ u Up U width N hξ hξh hu huU hRUp hUp hUB hw
    t ht hdR H hUH πL π upperBid hupperBid hfloor hrare hN cats L hL i
  simp only [neg_mul] at hreg
  have href : |(referenceLaw K Γ₀ i 1).mass r-
      (Counts.singletonLaw (1-P.theta) ⟨by linarith [P.theta_small],by linarith [P.theta_pos]⟩).mass r|≤
      Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2)+Real.exp (-(N:ℝ)*P.bulkWeight^2/2) := by
    rw [referenceLaw_mass]
    fin_cases r <;>
      norm_num [Counts.singletonLaw,FiniteLaw.mixture,FiniteLaw.dirac]
    · convert! hreg using 1
      rw [←abs_neg]
      congr 1
      ring
    · exact hreg
    · positivity
  have hscalar : 2*badBound P ξ N+
      (Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2)+Real.exp (-(N:ℝ)*P.bulkWeight^2/2))≤
      error P ξ N := by
    unfold error
    linarith only [Real.exp_pos (-(N:ℝ)*(lowMass P.theta)^2/2),
      Real.exp_pos (-(N:ℝ)*P.bulkWeight^2/2)]
  have hb' := (add_le_add hb (le_refl
    (Real.exp (-(N:ℝ)*(lowMass P.theta)^2/2)+Real.exp (-(N:ℝ)*P.bulkWeight^2/2)))).trans hscalar
  exact (abs_sub_le _ _ _).trans ((add_le_add he href).trans hb')

end FCAppendix.Affine.Tail04.OrderedZeroSourcePartialCount
