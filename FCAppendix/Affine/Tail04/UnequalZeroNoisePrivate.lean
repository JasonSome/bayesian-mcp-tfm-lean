import FCAppendix.Affine.Tail04.EqualZeroNoisePrivate
import FCAppendix.Affine.Tail04.ZeroNoiseGuard

noncomputable section
namespace FCAppendix.Affine.Tail04.UnequalZeroNoisePrivate
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws FixedAmbientNoise
open scoped BigOperators

variable (D : FiniteTailNoisyGame.Data) (N H0 H1 : ℕ) (side reg low : Bool) (vL vU : ℝ)

abbrev H := AllCountAtypical.ownCount H0 H1 side
abbrev Own := EqualZeroNoisePrivate.Own D vL vU
abbrev Sample := EqualZeroNoisePrivate.Sample D N (H H0 H1 side) vL vU

local instance sampleBorel : BorelSpace (Sample D N H0 H1 side vL vU) :=
  EqualZeroNoisePrivate.sampleBorel D N (H H0 H1 side) vL vU

def weight (z : Noise D.eps×Sample D N H0 H1 side vL vU) : ℝ :=
  UnequalPartialCountPayoff.rawWeight N H0 H1 D.c D.ξ (D.U*(1+(z.1:ℝ))) D.R
    (D.Up*(1+(z.1:ℝ))) D.width (D.e0 reg) D.F reg low
    (D.marksLaw H0) (D.marksLaw H1) (fun i=>(z.2.2.1 i:ℝ))

def input (action : C(Own D vL vU,Icc D.R D.Up))
    (z : Noise D.eps×Sample D N H0 H1 side vL vU) : ℝ×Signal (H H0 H1 side) D.R D.V :=
  ((physical D.hR D.hRUp (z.1,action z.2.1,z.2.2.2.2):ℝ),z.2.2.2.1)

lemma continuous_input (action : C(Own D vL vU,Icc D.R D.Up)) :
    Continuous (input D N H0 H1 side vL vU action) := by
  have he : Continuous (fun z : Noise D.eps × Sample D N H0 H1 side vL vU => z.1) := by fun_prop
  have ha : Continuous (fun z : Noise D.eps × Sample D N H0 H1 side vL vU => action z.2.1) := by fun_prop
  have hu : Continuous (fun z : Noise D.eps × Sample D N H0 H1 side vL vU => z.2.2.2.2) := by fun_prop
  exact (continuous_subtype_val.comp
    ((continuous_physical D.hR D.hRUp).comp (he.prodMk (ha.prodMk hu)))).prodMk (by fun_prop)

def inclusion (j : Fin (H H0 H1 side)) (action : C(Own D vL vU,Icc D.R D.Up))
    (z : Noise D.eps×Sample D N H0 H1 side vL vU) : ℝ :=
  weight D N H0 H1 side reg low vL vU z*(if reg then 0 else 1)+
    (1-weight D N H0 H1 side reg low vL vU z)*
      AtypicalPartialNoisy.rankInclusion N H0 H1 D.c side j (input D N H0 H1 side vL vU action z)

def payoff (j : Fin (H H0 H1 side)) (action : C(Own D vL vU,Icc D.R D.Up))
    (z : Noise D.eps×Sample D N H0 H1 side vL vU) : ℝ :=
  ((z.2.1.1:ℝ)-(input D N H0 H1 side vL vU action z).1)*
    inclusion D N H0 H1 side reg low vL vU j action z

lemma measurable_weight : Measurable (weight D N H0 H1 side reg low vL vU) := by
  exact ZeroNoiseGuard.measurable_rawWeight N H0 H1 D.c D.ξ D.R D.width (D.e0 reg) D.F
    reg low (D.marksLaw H0) (D.marksLaw H1) _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)

lemma measurable_payoff (j : Fin (H H0 H1 side)) (action : C(Own D vL vU,Icc D.R D.Up)) :
    Measurable (payoff D N H0 H1 side reg low vL vU j action) := by
  have hi:=(continuous_input D N H0 H1 side vL vU action).measurable
  have hw:=measurable_weight D N H0 H1 side reg low vL vU
  exact ((by fun_prop : Measurable (fun z : Noise D.eps×Sample D N H0 H1 side vL vU=>
    (z.2.1.1:ℝ))).sub hi.fst).mul
      ((hw.mul measurable_const).add ((measurable_const.sub hw).mul
        ((AtypicalPartialNoisy.measurable_rankInclusion N H0 H1 D.c side j).comp hi)))

lemma inclusion_bounds (j : Fin (H H0 H1 side)) (action : C(Own D vL vU,Icc D.R D.Up))
    (z : Noise D.eps×Sample D N H0 H1 side vL vU) :
    inclusion D N H0 H1 side reg low vL vU j action z∈Icc (0:ℝ) 1 := by
  have hw:=UnequalPartialCountPayoff.rawWeight_bounds N H0 H1 D.c D.ξ
    (D.U*(1+(z.1:ℝ))) D.R (D.Up*(1+(z.1:ℝ))) D.width (D.e0 reg) D.F reg low
    (D.marksLaw H0) (D.marksLaw H1) (fun i=>(z.2.2.1 i:ℝ))
  have hr:=AtypicalPartialNoisy.rankInclusion_bounds N H0 H1 D.c side j
    (input D N H0 H1 side vL vU action z)
  rcases hw with ⟨hw0,hw1⟩
  change _∈Icc (0:ℝ) 1
  unfold inclusion weight
  cases reg <;> simp only [Bool.false_eq_true,ite_false,ite_true,mul_zero,mul_one,zero_add] <;>
    constructor <;> nlinarith

lemma payoff_bound (j : Fin (H H0 H1 side)) (action : C(Own D vL vU,Icc D.R D.Up))
    (z : Noise D.eps×Sample D N H0 H1 side vL vU) :
    |payoff D N H0 H1 side reg low vL vU j action z|≤|vL|+|vU|+|D.V| := by
  have hv : |(z.2.1.1:ℝ)|≤|vL|+|vU| := by
    apply abs_le.mpr
    constructor <;> nlinarith [z.2.1.1.2.1,z.2.1.1.2.2,le_abs_self vL,
      neg_le_abs vL,le_abs_self vU,abs_nonneg vL,abs_nonneg vU]
  have hp : |(input D N H0 H1 side vL vU action z).1|≤|D.V| := by
    change |(physical D.hR D.hRUp (z.1,action z.2.1,z.2.2.2.2):ℝ)| ≤ |D.V|
    rw [abs_of_nonneg (D.hR.le.trans (physical D.hR D.hRUp _).2.1)]
    exact (physical D.hR D.hRUp _).2.2.trans (le_abs_self _)
  have hq:=inclusion_bounds D N H0 H1 side reg low vL vU j action z
  unfold payoff
  rw [abs_mul,abs_of_nonneg hq.1]
  exact (mul_le_of_le_one_right (abs_nonneg _) hq.2).trans
    ((abs_sub _ _).trans (by linarith))

def bad (j : Fin (H H0 H1 side)) (action : C(Own D vL vU,Icc D.R D.Up)) :
    Set (Noise D.eps×Sample D N H0 H1 side vL vU) :=
  (fun z=> fun i=>(z.2.2.1 i:ℝ)) ⁻¹' ZeroNoiseFallback.rankBad N ∪
  ⋃ k : Fin (H H0 H1 side),if k=j then ∅ else
    {z | partialBid (z.2.2.2.1 k)=(input D N H0 H1 side vL vU action z).1}

lemma isClosed_bad (j : Fin (H H0 H1 side)) (action : C(Own D vL vU,Icc D.R D.Up)) :
    IsClosed (bad D N H0 H1 side vL vU j action) := by
  apply IsClosed.union
  · exact (ZeroNoiseFallback.isClosed_rankBad N).preimage (by fun_prop)
  · apply isClosed_iUnion_of_finite
    intro k
    split_ifs
    · exact isClosed_empty
    · exact isClosed_eq (continuous_partialBid.comp (by fun_prop))
        ((continuous_input D N H0 H1 side vL vU action).fst)

lemma continuousAt_payoff (j : Fin (H H0 H1 side)) (action : C(Own D vL vU,Icc D.R D.Up))
    (z : Noise D.eps×Sample D N H0 H1 side vL vU)
    (hz : z∉bad D N H0 H1 side vL vU j action) :
    ContinuousAt (payoff D N H0 H1 side reg low vL vU j action) z := by
  have hno (i k : Fin N) (hik : i≠k) : (z.2.2.1 i:ℝ)≠(z.2.2.1 k:ℝ) := by
    intro he
    apply hz
    left
    right
    exact Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨k,by simpa only [if_neg hik,Set.mem_setOf_eq] using he⟩⟩
  let Bfun : Noise D.eps × Sample D N H0 H1 side vL vU → ℝ := fun z => D.U*(1+(z.1:ℝ))
  let Vfun : Noise D.eps × Sample D N H0 H1 side vL vU → ℝ := fun z => D.Up*(1+(z.1:ℝ))
  let bfun : Noise D.eps × Sample D N H0 H1 side vL vU → Fin N → ℝ := fun z i => (z.2.2.1 i:ℝ)
  have hw:=ZeroNoiseGuard.continuousAt_rawWeight N H0 H1 D.c D.ξ D.R D.width (D.e0 reg) D.F
    reg low (D.marksLaw H0) (D.marksLaw H1) Bfun Vfun bfun z
    (by fun_prop) (by fun_prop) (by fun_prop)
    (fun i=>(by norm_num : (0:ℝ)<1).trans_le (z.2.2.1 i).2.1) hno

  have ht (k : Fin (H H0 H1 side)) (hkj : k≠j) :
      partialBid (z.2.2.2.1 k)≠(input D N H0 H1 side vL vU action z).1 := by
    intro he
    apply hz
    right
    exact Set.mem_iUnion.mpr ⟨k,by simpa only [if_neg hkj,Set.mem_setOf_eq] using he⟩
  have hi:=(continuous_input D N H0 H1 side vL vU action).continuousAt (x:=z)
  have hr:=(AtypicalPartialNoisy.continuousAt_rankInclusion N H0 H1 D.c side j _ ht).comp hi
  exact ((by fun_prop : ContinuousAt (fun z : Noise D.eps×Sample D N H0 H1 side vL vU=>
    (z.2.1.1:ℝ)) z).sub hi.fst).mul
      ((hw.mul continuousAt_const).add ((continuousAt_const.sub hw).mul hr))

theorem bad_zero_null (j : Fin (H H0 H1 side)) (action : C(Own D vL vU,Icc D.R D.Up))
    (ν : ProbabilityMeasure (Icc (1:ℝ) D.B)) [NullSingletonClass (ν : Measure (Icc (1:ℝ) D.B))]
    (θ : ProbabilityMeasure (Signal (H H0 H1 side) D.R D.V))
    (hθ : ∀ a : ℝ,0< a→∀ᵐ s ∂(θ : Measure (Signal (H H0 H1 side) D.R D.V)),∀ k,partialBid (s k)≠a)
    (π : ProbabilityMeasure (Own D vL vU)) :
    (ClosedNullExpectations.experiment (zero D.eps D.heps.le)
      (EqualZeroNoisePrivate.sampleLaw D N (H H0 H1 side) vL vU π ν θ) : Measure _)
        (bad D N H0 H1 side vL vU j action)=0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  change ∀ᵐ z ∂(Measure.dirac (zero D.eps D.heps.le)).prod
    ((π : Measure (Own D vL vU)).prod ((rowLaw N ν : Measure (Fin N → Icc (1:ℝ) D.B)).prod ((θ : Measure (Signal (H H0 H1 side) D.R D.V)).prod volume))),_
  apply (Measure.ae_prod_iff_ae_ae
    (isClosed_bad D N H0 H1 side vL vU j action).measurableSet.compl).mpr
  rw [MeasureTheory.ae_dirac_eq]
  change ∀ᵐ x ∂(π : Measure (Own D vL vU)).prod
    ((rowLaw N ν : Measure (Fin N → Icc (1:ℝ) D.B)).prod
      ((θ : Measure (Signal (H H0 H1 side) D.R D.V)).prod (volume : Measure unitInterval))),
    (zero D.eps D.heps.le,x) ∉ bad D N H0 H1 side vL vU j action
  apply (Measure.ae_prod_iff_ae_ae (by
    exact (isClosed_bad D N H0 H1 side vL vU j action).measurableSet.compl.preimage
      (by fun_prop))).mpr
  apply ae_of_all
  intro own
  have hcommon : ∀ᵐ b ∂(rowLaw N ν : Measure (Fin N → Icc (1:ℝ) D.B)),∀ i k,i≠k→(b i:ℝ)≠(b k:ℝ) := by
    have hh:=ZeroNoiseAffine.ae_cons_distinct (N:=N) (ν : Measure (Icc (1:ℝ) D.B)) (1:ℝ) (by norm_num)
    rw [←rowLaw_eq_pi] at hh
    filter_upwards [hh] with b hb
    intro i k hik
    simpa only [Fin.cons_succ] using hb i.succ k.succ (fun he=> hik (Fin.succ_injective N he))
  apply (Measure.ae_prod_iff_ae_ae (by
    exact (isClosed_bad D N H0 H1 side vL vU j action).measurableSet.compl.preimage
      (by fun_prop))).mpr
  filter_upwards [hcommon] with b hb
  apply (Measure.ae_prod_iff_ae_ae (by
    exact (isClosed_bad D N H0 H1 side vL vU j action).measurableSet.compl.preimage
      (by fun_prop))).mpr
  filter_upwards [hθ (action own) (D.hR.trans_le (action own).2.1)] with s hs
  apply ae_of_all
  intro u hbad
  rcases hbad with hr|ht
  · rcases hr with hn|htie
    · obtain ⟨i,hi⟩:=Set.mem_iUnion.mp hn
      exact (not_le.mpr ((by norm_num : (0:ℝ)<1).trans_le (b i).2.1)) hi
    · obtain ⟨i,hi⟩:=Set.mem_iUnion.mp htie
      obtain ⟨k,hk⟩:=Set.mem_iUnion.mp hi
      by_cases hik : i=k
      · simp only [if_pos hik,Set.mem_empty_iff_false] at hk
      · exact hb i k hik (by simpa only [if_neg hik,Set.mem_setOf_eq] using hk)
  · obtain ⟨k,hk⟩:=Set.mem_iUnion.mp ht
    by_cases hkj : k=j
    · simp only [if_pos hkj,Set.mem_empty_iff_false] at hk
    · exact hs k (by simpa only [if_neg hkj,Set.mem_setOf_eq,input,Prod.fst,Prod.snd,physical_zero,EqualPrivateAmbient.widen] using hk)

theorem tendsto_payoff_test (j : Fin (H H0 H1 side))
    (action : C(Own D vL vU,Icc D.R D.Up)) (a : C(Own D vL vU,ℝ))
    (eps : ℕ→ Noise D.eps) (heps : Tendsto eps atTop (𝓝 (zero D.eps D.heps.le)))
    (νn : ℕ→ ProbabilityMeasure (Icc (1:ℝ) D.B))
    (ν : ProbabilityMeasure (Icc (1:ℝ) D.B)) [NullSingletonClass (ν : Measure (Icc (1:ℝ) D.B))]
    (hν : Tendsto νn atTop (𝓝 ν))
    (θn : ℕ→ ProbabilityMeasure (Signal (H H0 H1 side) D.R D.V))
    (θ : ProbabilityMeasure (Signal (H H0 H1 side) D.R D.V)) (hθn : Tendsto θn atTop (𝓝 θ))
    (hθ : ∀ x : ℝ,0< x→∀ᵐ s ∂(θ : Measure (Signal (H H0 H1 side) D.R D.V)),∀ k,partialBid (s k)≠x)
    (πn : ℕ→ ProbabilityMeasure (Own D vL vU)) (π : ProbabilityMeasure (Own D vL vU))
    (hπ : Tendsto πn atTop (𝓝 π)) :
    Tendsto (fun n=>∫ x,a x.1*payoff D N H0 H1 side reg low vL vU j action (eps n,x)
      ∂(EqualZeroNoisePrivate.sampleLaw D N (H H0 H1 side) vL vU (πn n) (νn n) (θn n) : Measure _)) atTop
      (𝓝 (∫ x,a x.1*payoff D N H0 H1 side reg low vL vU j action (zero D.eps D.heps.le,x)
        ∂(EqualZeroNoisePrivate.sampleLaw D N (H H0 H1 side) vL vU π ν θ : Measure _))) := by
  let aa : C(Noise D.eps×Sample D N H0 H1 side vL vU,ℝ):=
    ⟨fun z=> a z.2.1,a.continuous.comp (continuous_fst.comp continuous_snd)⟩
  have hs:=(EqualZeroNoisePrivate.continuous_sampleLaw D N (H H0 H1 side) vL vU).continuousAt.tendsto.comp
    (hπ.prodMk_nhds (hν.prodMk_nhds hθn))
  exact ClosedNullExpectations.tendsto_localized
    (payoff D N H0 H1 side reg low vL vU j action)
    (measurable_payoff D N H0 H1 side reg low vL vU j action)
    (bad D N H0 H1 side vL vU j action) (isClosed_bad D N H0 H1 side vL vU j action)
    (continuousAt_payoff D N H0 H1 side reg low vL vU j action) (by positivity)
    (payoff_bound D N H0 H1 side reg low vL vU j action) eps (zero D.eps D.heps.le) heps
    _ _ hs (bad_zero_null D N H0 H1 side vL vU j action ν θ hθ π) aa

end FCAppendix.Affine.Tail04.UnequalZeroNoisePrivate
