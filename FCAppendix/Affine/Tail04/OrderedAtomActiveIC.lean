import FCAppendix.Affine.Tail04.OrderedAtomActiveLaw
import FCAppendix.Affine.Tail04.SourceOrderedNoisyFixedPoint

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomActiveIC
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues CompactSourceBidLaws
open SourceTailNoisyFixedPoint LatentNoisyPopulation LatentSpeciesCalculus
open OrderedAtomActiveLaw

attribute [local irreducible] physicalValue

def activeBase (D : FiniteTailNoisyGame.Data) (k : Fin 3) (hk : k≠2)
    (b : Icc (bidLo D k) (bidHi D k)) : Icc (1:ℝ) D.U :=
  ⟨b,by
    fin_cases k
    · exact ⟨b.2.1,b.2.2.trans D.huU⟩
    · exact b.2
    · exact (hk rfl).elim⟩

lemma continuous_activeBase (D : FiniteTailNoisyGame.Data) (k : Fin 3) (hk : k≠2) :
    Continuous (activeBase D k hk) := continuous_subtype_val.subtype_mk _

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (hfloor : ∀ v,t< v→ H≤ upperBid v)
  (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)

local notation "μ" => drawLaw D P t ht πL π upperBid hupperBid
local notation "ν" => Measure.pi (fun _ : Fin N => μ)

def raisedBid (y : Icc (1:ℝ) D.U) (z : Draw) : Icc (1:ℝ) D.B :=
  noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (y,z.1.2)

lemma measurable_raisedBid (y : Icc (1:ℝ) D.U) : Measurable (raisedBid D y) :=
  (continuous_noisyBid (by norm_num : (0:ℝ)<1) D.heps.le).measurable.comp
    (measurable_const.prodMk measurable_fst.snd)

def gain (y : Icc (1:ℝ) D.U) (z : Draw×(Fin N→ Draw)) : ℝ :=
  physicalValue D P t ht π hdR H hBH N (value z.1) (raisedBid D y z.1) z.2-
    physicalValue D P t ht π hdR H hBH N (value z.1) (latentBid D P hdR H hBH z.1) z.2

lemma measurable_gain (y : Icc (1:ℝ) D.U) :
    Measurable (gain D P t ht π hdR H hBH N y) := by
  have hf := measurable_physicalValue_joint D P t ht π hdR H hBH N
  exact (hf.comp (((measurable_value.comp measurable_fst).prodMk
    ((measurable_raisedBid D y).comp measurable_fst)).prodMk measurable_snd)).sub
      (hf.comp (((measurable_value.comp measurable_fst).prodMk
        ((measurable_latentBid D P hdR H hBH).comp measurable_fst)).prodMk measurable_snd))

lemma latentBid_bandDraw (k : Fin 3) (hk : k≠2) (z : BandDraw D P t k) :
    latentBid D P hdR H hBH (bandDraw D P t k z)=
      noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (activeBase D k hk z.1.1.2,z.1.2) := by
  apply Subtype.ext
  have hb := Hybrid.activeNoisyRealBid_mem (by norm_num : (0:ℝ)<1) D.heps.le
    (activeBase D k hk z.1.1.2) z.1.2
  fin_cases k
  · exact OriginalValues.clipToBand_eq 1 D.B
      (by have hh:=hb.1.trans hb.2;exact hh) hb
  · exact OriginalValues.clipToBand_eq 1 D.B
      (by have hh:=hb.1.trans hb.2;exact hh) hb
  · exact (hk rfl).elim

def typedGain (k : Fin 3) (hk : k≠2) (y : Icc (bidLo D k) (bidHi D k))
    (z : BandDraw D P t k×(Fin N→ Draw)) : ℝ :=
  physicalValue D P t ht π hdR H hBH N (z.1.1.1.1:ℝ)
      (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (activeBase D k hk y,z.1.1.2)) z.2-
    physicalValue D P t ht π hdR H hBH N (z.1.1.1.1:ℝ)
      (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le
        (activeBase D k hk z.1.1.1.2,z.1.1.2)) z.2

lemma gain_bandDraw (k : Fin 3) (hk : k≠2) (y : Icc (bidLo D k) (bidHi D k))
    (z : BandDraw D P t k×(Fin N→ Draw)) :
    gain D P t ht π hdR H hBH N (activeBase D k hk y) (bandDraw D P t k z.1,z.2)=
      typedGain D P t ht π hdR H hBH N k hk y z := by
  rw [gain,latentBid_bandDraw D P t hdR H hBH k hk]
  rfl

lemma measurable_typedGain (k : Fin 3) (hk : k≠2) (y : Icc (bidLo D k) (bidHi D k)) :
    Measurable (typedGain D P t ht π hdR H hBH N k hk y) := by
  have hf := (measurable_gain D P t ht π hdR H hBH N (activeBase D k hk y)).comp
    ((measurable_bandDraw D P t k).prodMap measurable_id)
  change Measurable (fun z : BandDraw D P t k×(Fin N→Draw) =>
    gain D P t ht π hdR H hBH N (activeBase D k hk y) (bandDraw D P t k z.1,z.2)) at hf
  simpa only [gain_bandDraw] using hf

def bound (k : Fin 3) : ℝ := 2*(|valueLo P k|+|valueHi P t k|+2*D.B)

lemma typedGain_bound (k : Fin 3) (hk : k≠2) (y : Icc (bidLo D k) (bidHi D k))
    (z : BandDraw D P t k×(Fin N→ Draw)) :
    ‖typedGain D P t ht π hdR H hBH N k hk y z‖≤ bound D P t k := by
  have hv : |(z.1.1.1.1:ℝ)|≤|valueLo P k|+|valueHi P t k| := by
    apply abs_le.mpr
    constructor
    · linarith [z.1.1.1.1.2.1,neg_abs_le (valueLo P k),abs_nonneg (valueHi P t k)]
    · linarith [z.1.1.1.1.2.2,le_abs_self (valueHi P t k),abs_nonneg (valueLo P k)]
  unfold typedGain
  change |physicalValue D P t ht π hdR H hBH N (z.1.1.1.1:ℝ)
      (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (activeBase D k hk y,z.1.1.2)) z.2-
    physicalValue D P t ht π hdR H hBH N (z.1.1.1.1:ℝ)
      (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le
        (activeBase D k hk z.1.1.1.2,z.1.1.2)) z.2|≤
      2*(|valueLo P k|+|valueHi P t k|+2*D.B)
  exact (abs_sub _ _).trans (by
    linarith [physicalValue_bound D P t ht π hdR H hBH N (z.1.1.1.1:ℝ)
      (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (activeBase D k hk y,z.1.1.2)) z.2,
      physicalValue_bound D P t ht π hdR H hBH N (z.1.1.1.1:ℝ)
        (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le
          (activeBase D k hk z.1.1.1.2,z.1.1.2)) z.2])

include πL upperBid hupperBid in
theorem original_gain_integral (k : Fin 3) (hk : k≠2)
    (y : Icc (bidLo D k) (bidHi D k)) (J : Set ℝ) (hJ : MeasurableSet J) :
    (∫ z,gain D P t ht π hdR H hBH N (activeBase D k hk y) z
      ∂((μ).restrict (bandCluster k J)).prod ν)=
      (species P t ht).mass (bandSpecies k)*
        ∫ z,typedGain D P t ht π hdR H hBH N k hk y z
          ∂((((((π k).1 : Measure _).restrict (typedCluster D P t k J)).prod
            (volume : Measure unitInterval)).prod (permLaw 2)).prod ν) := by
  rw [drawLaw_restrict_bandCluster D P t ht πL π upperBid hupperBid k J hJ,
    Measure.prod_smul_left,integral_smul_measure,
    ENNReal.toReal_ofReal ((species P t ht).nonneg (bandSpecies k))]
  congr 1
  rw [show
    (((((((π k).1 : Measure _).restrict (typedCluster D P t k J)).prod volume).prod
      (permLaw 2)).map (bandDraw D P t k)).prod ν)=
      ((((((π k).1 : Measure _).restrict (typedCluster D P t k J)).prod volume).prod
        (permLaw 2)).prod ν).map (Prod.map (bandDraw D P t k) id) by
      simpa only [Measure.map_id] using Measure.map_prod_map _ _
        (measurable_bandDraw D P t k) measurable_id]
  rw [integral_map ((measurable_bandDraw D P t k).prodMap measurable_id).aemeasurable
    (measurable_gain D P t ht π hdR H hBH N (activeBase D k hk y)).aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ fun z => gain_bandDraw D P t ht π hdR H hBH N k hk y z)

include hfloor hrare in
include πL upperBid hupperBid hfloor hrare in
theorem original_cluster_IC (k : Fin 3) (hk : k≠2)
    (y : Icc (bidLo D k) (bidHi D k)) (J : Set ℝ) (hJ : MeasurableSet J)
    (hC1 : AllActionOptimal (π k) (fun x => SourceOrderedNoisyFixedPoint.payoff D P t ht N k (π,x))) :
    (∫ z,gain D P t ht π hdR H hBH N (activeBase D k hk y) z
      ∂((μ).restrict (bandCluster k J)).prod ν)≤0 := by
  rw [original_gain_integral D P t ht πL π upperBid hupperBid hdR H hBH N k hk y J hJ]
  apply mul_nonpos_of_nonneg_of_nonpos ((species P t ht).nonneg (bandSpecies k))
  have hi : Integrable (typedGain D P t ht π hdR H hBH N k hk y)
      ((((((π k).1 : Measure _).restrict (typedCluster D P t k J)).prod volume).prod
        (permLaw 2)).prod ν) :=
    Integrable.of_bound (measurable_typedGain D P t ht π hdR H hBH N k hk y).aestronglyMeasurable
      (bound D P t k) (ae_of_all _ (typedGain_bound D P t ht π hdR H hBH N k hk y))
  rw [integral_prod _ hi,integral_prod _ hi.integral_prod_left,
    integral_prod _ hi.integral_prod_left.integral_prod_left]
  apply integral_nonpos_of_ae
  filter_upwards [ae_restrict_of_ae hC1] with x hx
  have hpoint (b : Icc (1:ℝ) D.U) :
      (∫ u : unitInterval,∫ row,physicalValue D P t ht π hdR H hBH N (x.1:ℝ)
        (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u)) row ∂ν)=
      OrderedFiniteTailNoisyGame.activeExpected (installOriginal D P t ht) N (bidLaws D P t ht π,((x.1:ℝ),b)) :=
    original_noisy_physicalValue D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare x.1 b
  have hir (b : Icc (1:ℝ) D.U) : Integrable (fun p : unitInterval×(Fin N→ Draw) =>
      physicalValue D P t ht π hdR H hBH N (x.1:ℝ)
        (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,p.1)) p.2) (volume.prod ν) :=
    Integrable.of_bound
      ((measurable_physicalValue_joint D P t ht π hdR H hBH N).comp
        ((measurable_const.prodMk
          ((continuous_noisyBid (by norm_num : (0:ℝ)<1) D.heps.le).measurable.comp
            (measurable_const.prodMk measurable_fst))).prodMk measurable_snd)).aestronglyMeasurable
      (|(x.1:ℝ)|+2*D.B) (ae_of_all _ fun p => by
        simpa only [Real.norm_eq_abs] using physicalValue_bound D P t ht π hdR H hBH N x.1 _ p.2)
  have hrow (u : unitInterval) (b : Icc (1:ℝ) D.U) : Integrable
      (physicalValue D P t ht π hdR H hBH N x.1
        (noisyBid (by norm_num : (0:ℝ)<1) D.heps.le (b,u))) ν :=
    Integrable.of_bound (measurable_physicalValue D P t ht π hdR H hBH N x.1 _).aestronglyMeasurable
      (|(x.1:ℝ)|+2*D.B) (ae_of_all _ fun row => by
        simpa only [Real.norm_eq_abs] using physicalValue_bound D P t ht π hdR H hBH N x.1 _ row)
  simp only [typedGain]
  simp_rw [integral_sub (hrow _ (activeBase D k hk y)) (hrow _ (activeBase D k hk x.2)),
    integral_const,probReal_univ,one_smul]
  rw [integral_sub (hir (activeBase D k hk y)).integral_prod_left
      (hir (activeBase D k hk x.2)).integral_prod_left,hpoint,hpoint]
  have hy := hx y
  fin_cases k
  · exact sub_nonpos.mpr hy
  · exact sub_nonpos.mpr hy
  · exact (hk rfl).elim

end FCAppendix.Affine.Tail04.OrderedAtomActiveIC
