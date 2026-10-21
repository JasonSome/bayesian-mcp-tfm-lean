import FCAppendix.Affine.Tail04.ZeroNoiseGuard
import FCAppendix.Affine.Tail04.FixedAmbientNoise
import FCAppendix.Affine.Tail04.ClosedNullExpectations
import FCAppendix.Affine.Tail04.ActivePhysicalPayoff

noncomputable section
namespace FCAppendix.Affine.Tail04.ZeroNoiseActive
open TopologicalSpace
open MeasureTheory ProbabilityTheory Set Filter Topology Classical
open Existence.Distributional EqualPrivateSignal CompactSourceBidLaws FixedAmbientNoise
open scoped BigOperators

variable (D : FiniteTailNoisyGame.Data) (A H0 H1 : ℕ) (reg low : Bool)
  {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [MetrizableSpace X]

abbrev Prior := WeakProbability.Law (Signal H0 D.R D.V)
abbrev Parameters := Noise D.eps×Prior D H0
abbrev Sample := X×((Fin A→ Icc (1:ℝ) D.B)×unitInterval)

def row (action : C(X,Icc (1:ℝ) D.U))
    (z : Parameters D H0×Sample D A (X:=X)) : Fin (A+1)→ Icc (1:ℝ) D.B :=
  Fin.cons (physical (by norm_num) D.hU (z.1.1,action z.2.1,z.2.2.2)) z.2.2.1

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [MetrizableSpace X] in
lemma continuous_row (action : C(X,Icc (1:ℝ) D.U)) :
    Continuous (row D A H0 action) := by
  unfold row
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · have heps : Continuous (fun z : Parameters D H0×Sample D A (X:=X)=>z.1.1) :=
      continuous_fst.fst
    have ha : Continuous (fun z : Parameters D H0×Sample D A (X:=X)=>action z.2.1) :=
      action.continuous.comp continuous_snd.fst
    have hu : Continuous (fun z : Parameters D H0×Sample D A (X:=X)=>z.2.2.2) :=
      continuous_snd.snd.snd
    exact (continuous_physical (by norm_num) D.hU).comp (heps.prodMk (ha.prodMk hu))
  · exact (continuous_apply j).comp continuous_snd.snd.fst

def count (action : C(X,Icc (1:ℝ) D.U))
    (z : Parameters D H0×Sample D A (X:=X)) : CountLaw 2 :=
  if H0=H1 then
    EqualPrivateCountPayoff.countLaw (A+1) H0 D.c D.R D.V D.ξ 1 D.B
      (row D A H0 action z,z.1.2) 0
  else
    UnequalNoisyCountPayoff.rawCount H0 H1 D.c D.ξ (D.U*(1+(z.1.1:ℝ))) D.R
      (D.Up*(1+(z.1.1:ℝ))) D.width (D.e0 reg) D.F reg low
      (D.marksLaw H0) (D.marksLaw H1) (fun i=>(row D A H0 action z i:ℝ)) 0

def payoff (v : C(X,ℝ)) (action : C(X,Icc (1:ℝ) D.U))
    (z : Parameters D H0×Sample D A (X:=X)) : ℝ :=
  affineCountUtility (count D A H0 H1 reg low action z) (v z.2.1)
    (row D A H0 action z 0) D.eta D.heta0 D.heta1

lemma measurable_count_mass (action : C(X,Icc (1:ℝ) D.U)) (r : Fin 3) :
    Measurable (fun z : Parameters D H0×Sample D A (X:=X)=>
      (count D A H0 H1 reg low action z).mass r) := by
  unfold count
  split_ifs
  · exact (EqualPrivateCountPayoff.continuous_countLaw_mass (A+1) H0 D.c D.R D.V D.ξ 1 D.B
      D.hξ (by norm_num) 0 r).measurable.comp
        ((continuous_row D A H0 action).measurable.prodMk (by fun_prop))
  · exact ZeroNoiseGuard.measurable_rawCount_mass H0 H1 D.c D.ξ D.R D.width (D.e0 reg) D.F
      reg low (D.marksLaw H0) (D.marksLaw H1) _ _ _ (by fun_prop) (by fun_prop)
      ((continuous_pi (fun i=> continuous_subtype_val.comp
        ((continuous_apply i).comp (continuous_row D A H0 action)))).measurable) 0 r

lemma measurable_payoff (v : C(X,ℝ)) (action : C(X,Icc (1:ℝ) D.U)) :
    Measurable (payoff D A H0 H1 reg low v action) := by
  unfold payoff affineCountUtility CountLaw.utility FiniteLaw.expect
  apply Finset.measurable_sum
  intro r _
  apply (measurable_count_mass D A H0 H1 reg low action r).mul
  unfold userPayoff
  exact (((v.continuous.measurable.comp (by fun_prop)).mul measurable_const).sub
    ((continuous_subtype_val.comp ((continuous_apply 0).comp
      (continuous_row D A H0 action))).measurable.mul measurable_const)).sub measurable_const

omit [MeasurableSpace X] [BorelSpace X] [MetrizableSpace X] in
lemma payoff_bound (v : C(X,ℝ)) (action : C(X,Icc (1:ℝ) D.U))
    (z : Parameters D H0×Sample D A (X:=X)) :
    |payoff D A H0 H1 reg low v action z|≤‖v‖+2*D.B := by
  exact (ActivePhysicalPayoff.utility_bound _ (v z.2.1) (row D A H0 action z 0) D.B D.eta
    ((by norm_num : (0:ℝ)≤1).trans (row D A H0 action z 0).2.1)
    (row D A H0 action z 0).2.2 D.heta0 D.heta1).trans
      (add_le_add (by simpa only [Real.norm_eq_abs] using v.norm_coe_le_norm z.2.1) le_rfl)

def bad (action : C(X,Icc (1:ℝ) D.U)) : Set (Parameters D H0×Sample D A (X:=X)) :=
  (fun z=> fun i=>(row D A H0 action z i:ℝ)) ⁻¹' ZeroNoiseFallback.bad (A+1) D.ξ

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [MetrizableSpace X] in
lemma isClosed_bad (action : C(X,Icc (1:ℝ) D.U)) :
    IsClosed (bad D A H0 action) :=
  (ZeroNoiseFallback.isClosed_bad (A+1) D.ξ).preimage
    (continuous_pi (fun i=> continuous_subtype_val.comp
      ((continuous_apply i).comp (continuous_row D A H0 action))))

omit [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [MetrizableSpace X] in
lemma continuousAt_payoff (v : C(X,ℝ)) (action : C(X,Icc (1:ℝ) D.U))
    (z : Parameters D H0×Sample D A (X:=X)) (hz : z∉bad D A H0 action) :
    ContinuousAt (payoff D A H0 H1 reg low v action) z := by
  have hr : ContinuousAt (row D A H0 action) z :=
    (continuous_row D A H0 action).continuousAt
  have hc (r : Fin 3) : ContinuousAt (fun y : Parameters D H0×Sample D A (X:=X)=>
      (count D A H0 H1 reg low action y).mass r) z := by
    unfold count
    split_ifs
    · exact (EqualPrivateCountPayoff.continuous_countLaw_mass (A+1) H0 D.c D.R D.V D.ξ 1 D.B
        D.hξ (by norm_num) 0 r).continuousAt.comp (hr.prodMk (by fun_prop))
    · exact ZeroNoiseGuard.continuousAt_rawCount_mass H0 H1 D.c D.ξ D.R D.width (D.e0 reg) D.F
        reg low (D.marksLaw H0) (D.marksLaw H1) _ _ _ z (by fun_prop) (by fun_prop)
        ((continuous_pi (fun i=> continuous_subtype_val.comp
          ((continuous_apply i).comp (continuous_row D A H0 action)))).continuousAt) hz 0 r
  unfold payoff affineCountUtility CountLaw.utility FiniteLaw.expect
  apply tendsto_finsetSum
  intro r _
  apply (hc r).mul
  unfold userPayoff
  exact (((v.continuous.comp (by fun_prop)).continuousAt.mul continuousAt_const).sub
    (((continuous_subtype_val.comp ((continuous_apply 0).comp
      (continuous_row D A H0 action))).continuousAt).mul continuousAt_const)).sub continuousAt_const

def sampleLaw (π : ProbabilityMeasure X) (ν : ProbabilityMeasure (Icc (1:ℝ) D.B)) :
    ProbabilityMeasure (Sample D A (X:=X)) := productLaw π (productLaw (rowLaw A ν) uniformLaw)

lemma continuous_sampleLaw : Continuous
    (fun z : ProbabilityMeasure X×ProbabilityMeasure (Icc (1:ℝ) D.B)=> sampleLaw D A z.1 z.2) :=
  continuous_productLaw.comp (continuous_fst.prodMk
    (continuous_productLaw.comp (((continuous_rowLaw A).comp continuous_snd).prodMk continuous_const)))

theorem bad_zero_null (action : C(X,Icc (1:ℝ) D.U)) (μ : Prior D H0)
    (π : ProbabilityMeasure X) (ν : ProbabilityMeasure (Icc (1:ℝ) D.B))
    [NullSingletonClass (ν : Measure (Icc (1:ℝ) D.B))] :
    (ClosedNullExpectations.experiment (zero D.eps D.heps.le,μ)
      (sampleLaw D A π ν) : Measure (Parameters D H0×Sample D A (X:=X))) (bad D A H0 action)=0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  change ∀ᵐ z ∂(Measure.dirac (zero D.eps D.heps.le,μ)).prod
    ((π : Measure X).prod ((rowLaw A ν : Measure (Fin A→Icc (1:ℝ) D.B)).prod volume)),_
  have hbad : MeasurableSet (bad D A H0 action) := (isClosed_bad D A H0 action).measurableSet
  rw [Measure.dirac_prod]
  apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hbad.compl).mpr
  apply (Measure.ae_prod_iff_ae_ae
    (hbad.compl.preimage (measurable_const.prodMk measurable_id))).mpr
  apply ae_of_all
  intro own
  have hh:=ZeroNoiseFallback.ae_cons_not_bad (N:=A) D.ξ (by norm_num : (0:ℝ)<1)
    (ν : Measure (Icc (1:ℝ) D.B)) (action own:ℝ) ((by norm_num : (0:ℝ)<1).trans_le (action own).2.1)
  rw [←rowLaw_eq_pi] at hh
  apply (Measure.ae_prod_iff_ae_ae
    (hbad.compl.preimage (measurable_const.prodMk (measurable_const.prodMk measurable_id)))).mpr
  filter_upwards [hh] with rivals hr
  apply ae_of_all
  intro u
  change (fun i=>(row D A H0 action ((zero D.eps D.heps.le,μ),(own,(rivals,u))) i:ℝ))∉
    ZeroNoiseFallback.bad (A+1) D.ξ
  have hrow : (fun i=>(row D A H0 action ((zero D.eps D.heps.le,μ),(own,(rivals,u))) i:ℝ))=
      Fin.cons (action own:ℝ) (fun i=>(rivals i:ℝ)) := by
    funext i
    refine Fin.cases ?_ (fun _=>rfl) i
    simp only [row,Fin.cons_zero,physical_zero,EqualPrivateAmbient.widen]
  rw [hrow]
  exact hr

theorem tendsto_payoff_test (v : C(X,ℝ)) (action : C(X,Icc (1:ℝ) D.U)) (a : C(X,ℝ))
    (eps : ℕ→ Noise D.eps) (heps : Tendsto eps atTop (𝓝 (zero D.eps D.heps.le)))
    (μn : ℕ→ Prior D H0) (μ : Prior D H0) (hμ : Tendsto μn atTop (𝓝 μ))
    (νn : ℕ→ ProbabilityMeasure (Icc (1:ℝ) D.B))
    (ν : ProbabilityMeasure (Icc (1:ℝ) D.B)) [NullSingletonClass (ν : Measure (Icc (1:ℝ) D.B))]
    (hν : Tendsto νn atTop (𝓝 ν))
    (πn : ℕ→ ProbabilityMeasure X) (π : ProbabilityMeasure X) (hπ : Tendsto πn atTop (𝓝 π)) :
    Tendsto (fun n=>∫ x,a x.1*payoff D A H0 H1 reg low v action ((eps n,μn n),x)
      ∂(sampleLaw D A (πn n) (νn n) : Measure (Sample D A (X:=X)))) atTop
      (𝓝 (∫ x,a x.1*payoff D A H0 H1 reg low v action ((zero D.eps D.heps.le,μ),x)
        ∂(sampleLaw D A π ν : Measure (Sample D A (X:=X))))) := by
  let aa : C(Parameters D H0×Sample D A (X:=X),ℝ):=
    ⟨fun z=> a z.2.1,a.continuous.comp (continuous_fst.comp continuous_snd)⟩
  have hs:=(continuous_sampleLaw D A).continuousAt.tendsto.comp (hπ.prodMk_nhds hν)
  have hbound : 0≤‖v‖+2*D.B := by
    have hB : 0≤ D.B:=mul_nonneg ((by norm_num : (0:ℝ)≤1).trans D.hU) (by linarith [D.heps])
    positivity
  exact ClosedNullExpectations.tendsto_localized
    (payoff D A H0 H1 reg low v action) (measurable_payoff D A H0 H1 reg low v action)
    (bad D A H0 action) (isClosed_bad D A H0 action)
    (continuousAt_payoff D A H0 H1 reg low v action) hbound
    (payoff_bound D A H0 H1 reg low v action) (fun n=>(eps n,μn n))
    (zero D.eps D.heps.le,μ) (heps.prodMk_nhds hμ) _ _ hs
    (bad_zero_null D A H0 action μ π ν) aa

end FCAppendix.Affine.Tail04.ZeroNoiseActive
