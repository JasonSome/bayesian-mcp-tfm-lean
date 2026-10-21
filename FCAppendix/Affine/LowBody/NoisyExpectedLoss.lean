import FCAppendix.Affine.LowBody.PatternUniformEnvelope
import FCAppendix.Affine.LowBody.FirstCopyPair
import FCAppendix.Affine.LowBody.NoisyExpectedSurplus
import FCAppendix.Proposer.LotterySupport
import FCAppendix.Existence.R01PayOnceRowIntegration

noncomputable section
namespace FCAppendix.Affine.LowBody
open MeasureTheory ProbabilityTheory Set
open Existence.Distributional
open scoped BigOperators

lemma probabilityMeasure_iid {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (C : FiniteLaw A) (N : ℕ) :
    FiniteLaw.probabilityMeasure (CommonList.iid C N)=
      Measure.pi (fun _ : Fin N=>FiniteLaw.probabilityMeasure C) := by
  have hC : FiniteLaw.ofMeasure (FiniteLaw.probabilityMeasure C) id measurable_id=C :=
    FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure _ id measurable_id C (Measure.map_id)
  have hi:=FiniteLaw.ofMeasure_pi_eq_iid (FiniteLaw.probabilityMeasure C) N
    (fun _=>id) (fun _=>measurable_id) C (fun _=>hC)
  rw [←hi,FiniteLaw.probabilityMeasure_ofMeasure]
  exact Measure.map_id

lemma integral_probabilityMeasure {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (C : FiniteLaw A) (f : A→ℝ) :
    (∫a,f a ∂FiniteLaw.probabilityMeasure C)=C.expect f := by
  have hC : FiniteLaw.ofMeasure (FiniteLaw.probabilityMeasure C) id measurable_id=C :=
    FiniteLaw.ofMeasure_eq_of_map_eq_probabilityMeasure _ id measurable_id C (Measure.map_id)
  calc
    _=(FiniteLaw.ofMeasure (FiniteLaw.probabilityMeasure C) id measurable_id).expect f:=
      (FiniteLaw.expect_ofMeasure _ id measurable_id f).symm
    _=C.expect f:=by rw [hC]

variable {d : ℝ}

def lowRowPoint (x : Fin 4×LowValue d) : RowRival :=
  (x.1,if x.1=0 then x.2.1 else 0)

lemma measurable_lowRowPoint : Measurable (lowRowPoint (d:=d)) := by
  exact measurable_fst.prodMk (Measurable.ite
    (measurableSet_eq_fun measurable_fst measurable_const) measurable_snd.subtype_val measurable_const)

lemma lowRowPoint_dirac_prod (mu : Measure (LowValue d)) [SFinite mu] (k : Fin 4) :
    ((Measure.dirac k).prod mu).map lowRowPoint=
      mu.map (fun b=>(k,if k=0 then b.1 else 0)) := by
  rw [Measure.dirac_prod,Measure.map_map measurable_lowRowPoint
    (show Measurable (Prod.mk k : LowValue d→Fin 4×LowValue d) from
      measurable_const.prodMk measurable_id)]
  rfl

def realLowLaw (mu : Measure (LowValue d)) : Measure ℝ:=mu.map Subtype.val

instance realLowLaw_probability (mu : Measure (LowValue d)) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (realLowLaw mu):=
  Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

section LiteralPayoff
variable {N : ℕ}

lemma measurable_patternPayoff {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ) (w : ℝ) :
    Measurable (fun p : (Fin N→Fin 4)×(Fin (N+1)→ℝ)=>patternPayoff ξ c p.1 w p.2) := by
  classical
  apply measurable_from_prod_countable_right
  intro kind
  unfold patternPayoff
  dsimp only
  split_ifs
  · let r:=(patternTemplate c kind).residual₀
    have hp : Measurable (fun b : Fin (N+1)→ℝ=>EqualCapacity.positiveMarginal ξ r b 0):=
      (measurable_pi_apply 0).comp (EqualCapacity.measurable_positiveMarginal ξ r hξ hξ1)
    unfold equalPayoff
    exact (measurable_const.mul ((measurable_const.mul hp).sub (hp.pow_const 2))).sub
      ((measurable_pi_apply 0).mul ((measurable_const.mul hp).sub (measurable_const.mul (hp.pow_const 2))))
  · have hc : Measurable (fun b : Fin (N+1)→ℝ=>focalCopy
        ((patternTemplate c kind).selection (1-ξ) b) 0):=
      (measurable_of_countable (fun P : Finset (Fin (N+1))×Finset (Fin (N+1))=>focalCopy P 0)).comp
        ((patternTemplate c kind).measurable_selection (1-ξ))
    unfold purePayoff
    exact Measurable.ite (measurableSet_eq_fun hc measurable_const)
      (measurable_const.sub (measurable_const.mul (measurable_pi_apply 0)))
      (Measurable.ite (measurableSet_eq_fun hc measurable_const)
        (measurable_const.sub (measurable_pi_apply 0)) measurable_const)

lemma measurable_rowBids :
    Measurable (fun p : ℝ×(Fin N→RowRival)=>rowBids p.1 p.2) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j=>?_) i
  · exact measurable_fst
  · exact Measurable.ite
      (measurableSet_eq_fun (((measurable_pi_apply j).comp measurable_snd).fst) measurable_const)
      (((measurable_pi_apply j).comp measurable_snd).snd) measurable_const

def literalRowPayoff (ξ : ℝ) (c : ℕ) (w : ℝ) (p : ℝ×(Fin N→RowRival)) : ℝ:=
  patternPayoff ξ c (fun j=>(p.2 j).1) w (rowBids p.1 p.2)

set_option maxHeartbeats 800000 in
lemma measurable_literalRowPayoff {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ) (w : ℝ) :
    Measurable (literalRowPayoff (N:=N) ξ c w) := by
  have hk : Measurable (fun p : ℝ×(Fin N→RowRival)=>fun j=>(p.2 j).1):=
    measurable_pi_lambda _ (fun j=>((measurable_pi_apply j).comp measurable_snd).fst)
  have hpair : Measurable (fun p : ℝ×(Fin N→RowRival)=>
      ((fun j=>(p.2 j).1),rowBids p.1 p.2)):=hk.prodMk (measurable_rowBids (N:=N))
  exact (measurable_patternPayoff (N:=N) hξ hξ1 c w).comp hpair

lemma abs_patternPayoff_le {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ)
    (kind : Fin N→Fin 4) (w : ℝ) (b : Fin (N+1)→ℝ) :
    |patternPayoff ξ c kind w b|≤|w|+(3+2*|1-ξ|)*|b 0| := by
  unfold patternPayoff
  dsimp only
  split_ifs
  · exact (abs_equalPayoff_le hξ hξ1 _ (0:Fin (N+1)) w b).trans
      (by nlinarith [abs_nonneg (1-ξ),abs_nonneg (b 0)])
  · exact (abs_purePayoff_le (1-ξ) w b _ (0:Fin (N+1))).trans
      (by nlinarith [abs_nonneg (b 0)])

lemma abs_literalRowPayoff_le {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1) (c : ℕ) (w x : ℝ)
    (ω : Fin N→RowRival) : |literalRowPayoff ξ c w (x,ω)|≤|w|+(3+2*|1-ξ|)*|x| := by
  simpa only [literalRowPayoff,rowBids,Fin.cons_zero] using
    abs_patternPayoff_le hξ hξ1 c (fun j=>(ω j).1) w (rowBids x ω)

def literalSmoothedRowPayoff (ξ ε : ℝ) (c : ℕ) (w x : ℝ) (ω : Fin N→RowRival) : ℝ:=
  ∫z,literalRowPayoff ξ c w (x*(1+ε*z),ω) ∂uniformNoise

lemma measurable_literalSmoothedRowPayoff {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (ε : ℝ) (c : ℕ) (w x : ℝ) :
    Measurable (literalSmoothedRowPayoff (N:=N) ξ ε c w x) := by
  have hm : Measurable (fun p : (Fin N→RowRival)×ℝ=>literalRowPayoff ξ c w (x*(1+ε*p.2),p.1)):=
    (measurable_literalRowPayoff hξ hξ1 c w).comp
      ((show Measurable (fun p : (Fin N→RowRival)×ℝ=>x*(1+ε*p.2)) from by fun_prop).prodMk measurable_fst)
  exact hm.stronglyMeasurable.integral_prod_right.measurable

lemma abs_literalSmoothedRowPayoff_le {ξ : ℝ} (hξ : 0<ξ) (hξ1 : ξ<1)
    (ε : ℝ) (c : ℕ) (w x : ℝ) (ω : Fin N→RowRival) :
    |literalSmoothedRowPayoff ξ ε c w x ω|≤|w|+(3+2*|1-ξ|)*(|x| *(1+|ε|)) := by
  have hb : ∀ᵐz ∂uniformNoise,‖literalRowPayoff ξ c w (x*(1+ε*z),ω)‖≤
      |w|+(3+2*|1-ξ|)*(|x| *(1+|ε|)) := by
    filter_upwards [uniformNoise_support] with z hz
    have hzabs : |z|≤1:=by rw [abs_of_nonneg hz.1];exact hz.2
    have hmul : |x*(1+ε*z)|≤|x| *(1+|ε|) := by
      rw [abs_mul]
      have hh : |1+ε*z|≤1+|ε|:=by
        calc
          _≤|1|+|ε*z|:=abs_add_le _ _
          _≤1+|ε| *1:=by rw [abs_mul];gcongr;simp
          _=1+|ε|:=by ring
      exact mul_le_mul_of_nonneg_left hh (abs_nonneg _)
    exact (abs_literalRowPayoff_le hξ hξ1 c w (x*(1+ε*z)) ω).trans
      (by gcongr)
  simpa only [literalSmoothedRowPayoff,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const hb

end LiteralPayoff

section Mixture
variable (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
local notation "G"=>realLowLaw mu
local notation "C"=>categoryLaw s a h hs ha hh hsum G

lemma category_probabilityMeasure_explicit :
    FiniteLaw.probabilityMeasure C=
      ENNReal.ofReal s • Measure.dirac 0+ENNReal.ofReal a • Measure.dirac 1+
      ENNReal.ofReal (h/2) • Measure.dirac 2+ENNReal.ofReal (h/2) • Measure.dirac 3 := by
  unfold FiniteLaw.probabilityMeasure
  simp only [categoryLaw_mass]
  simp [Fin.sum_univ_succ]
  abel

theorem lowRowPoint_law :
    ((FiniteLaw.probabilityMeasure C).prod mu).map lowRowPoint=rivalLaw s a h G := by
  rw [category_probabilityMeasure_explicit s a h hs ha hh hsum mu]
  rw [Measure.add_prod,Measure.add_prod,Measure.add_prod,
    Measure.prod_smul_left,Measure.prod_smul_left,Measure.prod_smul_left,Measure.prod_smul_left]
  rw [Measure.map_add _ _ measurable_lowRowPoint,Measure.map_add _ _ measurable_lowRowPoint,
    Measure.map_add _ _ measurable_lowRowPoint,
    Measure.map_smul,Measure.map_smul,Measure.map_smul,Measure.map_smul]
  simp only [lowRowPoint_dirac_prod,ite_true]
  have hlow : mu.map (fun b : LowValue d=>((0:Fin 4),b.1))=
      (G).map (fun b=>((0:Fin 4),b)) := by
    unfold realLowLaw
    rw [Measure.map_map (show Measurable (fun b : ℝ=>((0:Fin 4),b)) from
      measurable_const.prodMk measurable_id) measurable_subtype_coe]
    rfl
  rw [hlow]
  have h1 : (fun b : LowValue d=>((1:Fin 4),if (1:Fin 4)=0 then b.1 else 0))=
      fun _=>((1:Fin 4),(0:ℝ)) := by funext b;norm_num [Fin.ext_iff]
  have h2 : (fun b : LowValue d=>((2:Fin 4),if (2:Fin 4)=0 then b.1 else 0))=
      fun _=>((2:Fin 4),(0:ℝ)) := by funext b;norm_num [Fin.ext_iff]
  have h3 : (fun b : LowValue d=>((3:Fin 4),if (3:Fin 4)=0 then b.1 else 0))=
      fun _=>((3:Fin 4),(0:ℝ)) := by funext b;norm_num [Fin.ext_iff]
  rw [h1,h2,h3,Measure.map_const,Measure.map_const,Measure.map_const,measure_univ,one_smul,one_smul,one_smul]
  rfl

theorem lowRowProfile_law (N : ℕ) :
    ((FiniteLaw.probabilityMeasure (CommonList.iid C N)).prod
      (Measure.pi (fun _ : Fin N=>mu))).map
        (fun p : (Fin N→Fin 4)×(Fin N→LowValue d)=>fun j=>lowRowPoint (p.1 j,p.2 j))=
      Measure.pi (fun _ : Fin N=>rivalLaw s a h G) := by
  rw [probabilityMeasure_iid]
  let e:=MeasurableEquiv.arrowProdEquivProdArrow (Fin 4) (LowValue d) (Fin N)
  have hp:= (measurePreserving_arrowProdEquivProdArrow (Fin 4) (LowValue d) (Fin N)
    (fun _=>FiniteLaw.probabilityMeasure C) (fun _=>mu)).symm
  have hm : Measurable (fun p : Fin N→Fin 4×LowValue d=>fun j=>lowRowPoint (p j)):=
    measurable_pi_lambda _ (fun j=>measurable_lowRowPoint.comp (measurable_pi_apply j))
  calc
    _ = (((Measure.pi (fun _ : Fin N=>FiniteLaw.probabilityMeasure C)).prod
        (Measure.pi (fun _ : Fin N=>mu))).map e.symm).map
          (fun p : Fin N→Fin 4×LowValue d=>fun j=>lowRowPoint (p j)) := by
      rw [Measure.map_map hm hp.measurable]
      rfl
    _ = _ := by
      rw [hp.map_eq,Measure.pi_map_pi (fun _=>measurable_lowRowPoint.aemeasurable),
        lowRowPoint_law s a h hs ha hh hsum mu]

theorem integral_lowRowProfile (N : ℕ) (f : (Fin N→RowRival)→ℝ)
    (hf : Measurable f) (M : ℝ) (hM : ∀ω,|f ω|≤M) :
    (∫ω,f ω ∂Measure.pi (fun _ : Fin N=>rivalLaw s a h G))=
      (CommonList.iid C N).expect (fun kind=>
        ∫b : Fin N→LowValue d,f (fun j=>lowRowPoint (kind j,b j))
          ∂Measure.pi (fun _ : Fin N=>mu)) := by
  let F : (Fin N→Fin 4)×(Fin N→LowValue d)→(Fin N→RowRival):=
    fun p j=>lowRowPoint (p.1 j,p.2 j)
  have hm : Measurable F:=measurable_pi_lambda _ (fun j=>
    measurable_lowRowPoint.comp (((measurable_pi_apply j).comp measurable_fst).prodMk
      ((measurable_pi_apply j).comp measurable_snd)))
  have hi : Integrable (fun p=>f (F p))
      ((FiniteLaw.probabilityMeasure (CommonList.iid C N)).prod
        (Measure.pi (fun _ : Fin N=>mu))) :=
    Integrable.of_bound (hf.comp hm).aestronglyMeasurable M
      (ae_of_all _ (fun p=>by simpa only [Real.norm_eq_abs] using hM (F p)))
  rw [←lowRowProfile_law s a h hs ha hh hsum mu N]
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable,integral_prod _ hi,
    integral_probabilityMeasure]

end Mixture

lemma literalSmoothedRowPayoff_lowRowPoint {N : ℕ} (ξ ε : ℝ) (c : ℕ)
    (kind : Fin N→Fin 4) (w : LowValue d) (q : unitInterval) (b : Fin N→LowValue d) :
    literalSmoothedRowPayoff ξ ε c w.1 (w.1*bidRatio ε q)
      (fun j=>lowRowPoint (kind j,b j))=
      patternSmoothedPayoff d ξ ε c kind ((w,q),b) := by
  rw [patternSmoothedPayoff_eq_integral]
  unfold literalSmoothedRowPayoff
  apply integral_congr_ae
  apply ae_of_all
  intro z
  change patternPayoff ξ c kind w.1
    (rowBids (w.1*bidRatio ε q*(1+ε*z)) (fun j=>lowRowPoint (kind j,b j)))=_
  congr 1
  ext i
  refine Fin.cases ?_ (fun j=>?_) i
  · simp [rowBids,patternNoisyBids,noisyFocal,parameterBids]
  · by_cases hj : kind j=0 <;>
      simp [rowBids,lowRowPoint,patternNoisyBids,noisyFocal,parameterBids,patternBids,hj]

theorem noisyExpectedUtility_eq_literal_row {N : ℕ} (d : ℝ) {ξ ε : ℝ}
    (hξ : 0<ξ) (hξ1 : ξ<1) (hε : 0<ε) (hsmall : ε≤1/2)
    (c : ℕ) (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (mu : Measure (LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=unitInterval) mu) (w : LowValue d) (q : unitInterval) :
    let physical:=implementedBidLaw d ε hε hsmall mu pi
    let G:=realLowLaw (physical : Measure (LowValue d))
    noisyExpectedUtility (N:=N) d ξ ε hε hsmall c
      (categoryLaw s a h hs ha hh hsum G) mu (pi,(w,q))=
      ∫ω : Fin N→RowRival,literalSmoothedRowPayoff ξ ε c w.1 (w.1*bidRatio ε q) ω
        ∂Measure.pi (fun _ : Fin N=>rivalLaw s a h G) := by
  dsimp only
  let physical:=implementedBidLaw d ε hε hsmall mu pi
  have ht:=integral_lowRowProfile s a h hs ha hh hsum
    (physical : Measure (LowValue d)) N
    (literalSmoothedRowPayoff ξ ε c w.1 (w.1*bidRatio ε q))
    (measurable_literalSmoothedRowPayoff hξ hξ1 ε c w.1 (w.1*bidRatio ε q))
    (|w.1|+(3+2*|1-ξ|)*(|w.1*bidRatio ε q| *(1+|ε|)))
    (abs_literalSmoothedRowPayoff_le hξ hξ1 ε c w.1 (w.1*bidRatio ε q))
  rw [ht]
  unfold noisyExpectedUtility FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro kind _
  congr 1
  rw [rowLaw_eq_pi]
  apply integral_congr_ae
  exact ae_of_all _ (fun b=>(literalSmoothedRowPayoff_lowRowPoint ξ ε c kind w q b).symm)

end FCAppendix.Affine.LowBody
