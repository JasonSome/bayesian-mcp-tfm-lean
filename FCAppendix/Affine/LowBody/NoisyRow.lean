import FCAppendix.Affine.LowBody.NoisyEqualPayoff
import FCAppendix.Affine.LowBody.PureTemplate
import FCAppendix.Affine.LowBody.NoiseParameters
import FCAppendix.Affine.LowBody.Rows
import FCAppendix.Proposer.CommonListGame

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set Filter Topology
open Existence.Distributional
open scoped BigOperators
variable {N : ℕ}

def patternRow (kind : Fin N→Fin 4) : Fin N→RowRival := fun j=>(kind j,0)

def patternTemplate (c : ℕ) (kind : Fin N→Fin 4) : PureTemplate (Fin (N+1)) where
  support:=Finset.univ.filter (fun i=>(rowLowList 0 (patternRow kind) i).isSome)
  residual₀:=rowResidual c 0 (patternRow kind)
  residual₁:=rowResidual c 1 (patternRow kind)

def patternBids (kind : Fin N→Fin 4) (d : ℝ) (b : Fin N→LowValue d) : Fin (N+1)→ℝ :=
  Fin.cons 0 (fun j=>if kind j=0 then (b j).1 else 0)

@[fun_prop] theorem continuous_patternBids (kind : Fin N→Fin 4) (d : ℝ) :
    Continuous (patternBids kind d) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact continuous_const
  · by_cases hj : kind j=0
    · simp only [patternBids,Fin.cons_succ,if_pos hj]
      fun_prop
    · simp only [patternBids,Fin.cons_succ,if_neg hj]
      fun_prop

theorem patternBids_nonneg (kind : Fin N→Fin 4) (d : ℝ) (b : Fin N→LowValue d)
    (i : Fin (N+1)) : 0≤patternBids kind d b i := by
  refine Fin.cases ?_ (fun j=>?_) i
  · exact le_rfl
  · by_cases hj : kind j=0
    · simpa only [patternBids,Fin.cons_succ,if_pos hj] using (b j).property.1
    · simp only [patternBids,Fin.cons_succ,if_neg hj,le_refl]

def nonnegPatternBids (kind : Fin N→Fin 4) (d : ℝ) (b : Fin N→LowValue d) :
    Fin (N+1)→Ici (0:ℝ) := fun i=>⟨patternBids kind d b i,patternBids_nonneg kind d b i⟩

@[fun_prop] theorem continuous_nonnegPatternBids (kind : Fin N→Fin 4) (d : ℝ) :
    Continuous (nonnegPatternBids kind d) := by
  apply continuous_pi
  intro i
  exact Continuous.subtype_mk ((continuous_apply i).comp (continuous_patternBids kind d)) _

def positiveBidRatio (ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2) (q : unitInterval) : Ioi (0:ℝ) :=
  ⟨bidRatio ε q,hε.trans_le (bidRatio_bounds hε hsmall q).1⟩

@[fun_prop] theorem continuous_positiveBidRatio (ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2) :
    Continuous (positiveBidRatio ε hε hsmall) := by
  apply Continuous.subtype_mk
  unfold bidRatio
  fun_prop

def patternSmoothedPayoff (d ξ ε : ℝ) (c : ℕ) (kind : Fin N→Fin 4)
    (t : (LowValue d×unitInterval)×(Fin N→LowValue d)) : ℝ :=
  let T:=patternTemplate c kind
  let raw : ℝ×ℝ×(Fin (N+1)→ℝ):=(t.1.1.1,bidRatio ε t.1.2,patternBids kind d t.2)
  if T.residual₀=T.residual₁ then
    parameterEqualPayoff ξ ε T.residual₀ 0 raw
  else
    ∫z,T.noisyUserPayoff (1-ξ) ε 0 (parameterBids 0 raw) z ∂uniformNoise

theorem continuous_patternSmoothedPayoff (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hε : 0<ε) (hsmall : ε≤1/2)
    (c : ℕ) (kind : Fin N→Fin 4) : Continuous (patternSmoothedPayoff d ξ ε c kind) := by
  let T:=patternTemplate c kind
  let X:=(LowValue d×unitInterval)×(Fin N→LowValue d)
  have hwp : Continuous (fun t : X=>(⟨t.1.1.1,t.1.1.property.1⟩ : Ici (0:ℝ))) :=
    Continuous.subtype_mk (by fun_prop) _
  have hqp : Continuous (fun t : X=>positiveBidRatio ε hε hsmall t.1.2) :=
    (continuous_positiveBidRatio ε hε hsmall).comp (continuous_snd.comp continuous_fst)
  have hbp : Continuous (fun t : X=>nonnegPatternBids kind d t.2) :=
    (continuous_nonnegPatternBids kind d).comp continuous_snd
  have hbr : Continuous (fun t : X=>patternBids kind d t.2) :=
    (continuous_patternBids kind d).comp continuous_snd
  unfold patternSmoothedPayoff
  dsimp only
  split_ifs
  · exact (continuous_parameterEqualPayoff_nonnegative hξ hξ1 hε.le T.residual₀ (0:Fin (N+1))).comp
      (hwp.prodMk (hqp.prodMk hbp))
  · exact (T.continuous_parameter_payoff (κ:=1-ξ) (ε:=ε) (by linarith : 0<1-ξ) hε.ne' (0:Fin (N+1))).comp
      (f:=fun t : X=>(t.1.1.1,positiveBidRatio ε hε hsmall t.1.2,patternBids kind d t.2))
      ((show Continuous (fun t : X=>t.1.1.1) from by fun_prop).prodMk (hqp.prodMk hbr))

def implementedBidLaw (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) : ProbabilityMeasure (LowValue d) :=
  (lowNoisyLaw d ε hε hsmall mu pi).1.map measurable_snd.aemeasurable

theorem continuous_implementedBidLaw (d ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] :
    Continuous (implementedBidLaw d ε hε hsmall mu) :=
  (ProbabilityMeasure.continuous_map continuous_snd).comp
    (continuous_subtype_val.comp (continuous_lowNoisyLaw d ε hε hsmall mu))

def noisyExpectedUtility (d ξ ε : ℝ) (hε : 0<ε) (hsmall : ε≤1/2)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (p : Law (A:=unitInterval) mu × (LowValue d×unitInterval)) : ℝ :=
  ∑kind : Fin N→Fin 4,(CommonList.iid categories N).mass kind*
    ∫b : Fin N→LowValue d,patternSmoothedPayoff d ξ ε c kind (p.2,b)
      ∂(rowLaw N (implementedBidLaw d ε hε hsmall mu p.1) : Measure (Fin N→LowValue d))

theorem continuous_noisyExpectedUtility (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hε : 0<ε) (hsmall : ε≤1/2)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] :
    Continuous (noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu) := by
  apply continuous_finsetSum
  intro kind _
  apply continuous_const.mul
  have hf:=continuous_patternSmoothedPayoff d hξ hξ1 hε hsmall c kind
  have hi:=continuous_law_integral (patternSmoothedPayoff d ξ ε c kind) hf
  exact hi.comp (continuous_snd.prodMk
    ((continuous_rowLaw N).comp ((continuous_implementedBidLaw d ε hε hsmall mu).comp continuous_fst)))

theorem exists_noisy_restricted_low_law (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hε : 0<ε) (hsmall : ε≤1/2)
    (c : ℕ) (categories : FiniteLaw (Fin 4))
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] :
    ∃(pi : Law (A:=unitInterval) mu)(sigma : Kernel (LowValue d) unitInterval),
      IsMarkovKernel sigma ∧ mu⊗ₘsigma=(pi.1 : Measure (LowValue d×unitInterval)) ∧
      (∀ᵐw ∂mu,∀ᵐq ∂sigma w,∀q' : unitInterval,
        noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,(w,q'))≤
          noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu (pi,(w,q))) := by
  obtain ⟨pi,sigma,hmark,hdis,_hjoint,hopt⟩:=exists_symmetric_law mu
    (noisyExpectedUtility (N:=N) d ξ ε hε hsmall c categories mu)
    (continuous_noisyExpectedUtility d hξ hξ1 hε hsmall c categories mu)
  exact ⟨pi,sigma,hmark,hdis,hopt⟩

end FCAppendix.Affine.LowBody
