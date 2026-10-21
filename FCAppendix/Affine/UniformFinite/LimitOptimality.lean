import FCAppendix.Affine.UniformFinite.Clearing
import FCAppendix.Affine.UniformFinite.FiniteExperiment

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology
open Existence.Distributional
open scoped BoundedContinuousFunction

section General
variable {T A : Type*} [TopologicalSpace T] [MeasurableSpace T]
  [CompactSpace T] [BorelSpace T]
  [TopologicalSpace A] [MeasurableSpace A] [CompactSpace A] [BorelSpace A]
  [SecondCountableTopology A]

lemma continuous_test_integrable (f : C(T×A,ℝ)) (nu : ProbabilityMeasure (T×A)) :
    Integrable (fun x=> f x) (nu : Measure (T×A)) :=
  (ContinuousMap.equivBoundedOfCompact _ _ f).integrable _

theorem common_allAction_of_gap_zero (mu : Measure T) [IsProbabilityMeasure mu]
    (pi : Law (A:=A) mu) (f : C(T×A,ℝ))
    (hzero : ∀a : A,(∫p,max 0 (f (p.1,a)-f p) ∂(pi.1 : Measure (T×A)))=0) :
    AllActionOptimal pi f := by
  obtain ⟨D,hDc,hDd⟩ := TopologicalSpace.exists_countable_dense A
  have hone (a : A) : ∀ᵐp ∂(pi.1 : Measure (T×A)),f (p.1,a)≤ f p := by
    let g : C(T×A,ℝ) := ⟨fun p=> max 0 (f (p.1,a)-f p),
      continuous_const.max ((f.continuous.comp
        (continuous_fst.prodMk continuous_const)).sub f.continuous)⟩
    have he : ∀ᵐp ∂(pi.1 : Measure (T×A)),g p=0 :=
      (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ (fun p=> le_max_left (0:ℝ) _))
        (continuous_test_integrable g pi.1)).mp (hzero a)
    filter_upwards [he] with p hp
    have h := le_max_right (0:ℝ) (f (p.1,a)-f p)
    change max 0 (f (p.1,a)-f p)=0 at hp
    linarith
  have hall : ∀ᵐp ∂(pi.1 : Measure (T×A)),∀a∈D,f (p.1,a)≤ f p :=
    (ae_ball_iff hDc).mpr (fun a _=> hone a)
  filter_upwards [hall] with p hp
  have hclosed : IsClosed {a : A | f (p.1,a)≤ f p} :=
    isClosed_le (f.continuous.comp (continuous_const.prodMk continuous_id)) continuous_const
  have hsub : closure D⊆{a : A | f (p.1,a)≤ f p} :=
    closure_minimal (fun a ha=> hp a ha) hclosed
  intro a
  exact hsub (hDd.closure_eq ▸ mem_univ a)

theorem allAction_limit_of_uniform_error (mu : Measure T) [IsProbabilityMeasure mu]
    (pi : ℕ→ Law (A:=A) mu) (pi0 : Law (A:=A) mu)
    (hpi : Tendsto pi atTop (𝓝 pi0))
    (f : C(T×A,ℝ)) (fn : ℕ→ T×A→ℝ) (err : ℕ→ℝ)
    (herr : ∀n,0≤ err n) (herr0 : Tendsto err atTop (𝓝 0))
    (happrox : ∀n p,|fn n p-f p|≤ err n)
    (hIC : ∀n,AllActionOptimal (pi n) (fn n)) : AllActionOptimal pi0 f := by
  apply common_allAction_of_gap_zero mu pi0 f
  intro a
  let g : C(T×A,ℝ) := ⟨fun p=> max 0 (f (p.1,a)-f p),
    continuous_const.max ((f.continuous.comp
      (continuous_fst.prodMk continuous_const)).sub f.continuous)⟩
  have hg : Tendsto (fun n=>∫p,g p ∂((pi n).1 : Measure (T×A))) atTop
      (𝓝 (∫p,g p ∂(pi0.1 : Measure (T×A)))) :=
    (ProbabilityMeasure.continuous_integral_continuousMap g).continuousAt.tendsto.comp
      (continuous_subtype_val.continuousAt.tendsto.comp hpi)
  have hb (n : ℕ) : (∫p,g p ∂((pi n).1 : Measure (T×A)))≤2*err n := by
    have hpoint : ∀ᵐp ∂((pi n).1 : Measure (T×A)),g p≤2*err n := by
      filter_upwards [hIC n] with p hp
      have hpa := abs_le.mp (happrox n (p.1,a))
      have hpp := abs_le.mp (happrox n p)
      have hopt := hp a
      apply max_le (mul_nonneg (by norm_num) (herr n))
      linarith
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using
      integral_mono_ae (continuous_test_integrable g (pi n).1) (integrable_const (2*err n)) hpoint
  have hupper : (∫p,g p ∂(pi0.1 : Measure (T×A)))≤0 := by
    simpa using le_of_tendsto_of_tendsto hg (herr0.const_mul 2) (Eventually.of_forall hb)
  exact le_antisymm hupper (integral_nonneg (fun p=> le_max_left (0:ℝ) _))

end General

def choiceProduct (i : Row) (G : Uniform05.RestrictedLaw i) (p : Value i×unitInterval) : ℝ :=
  productPayoff (Uniform05.xi i) p.1 G.multiplier (baseBid i p)

lemma continuous_choiceProduct (i : Row) :
    Continuous (fun p : Uniform05.RestrictedLaw i×(Value i×unitInterval)=> choiceProduct i p.1 p.2) := by
  have hL : Continuous (fun p : Uniform05.RestrictedLaw i×(Value i×unitInterval)=> p.1.multiplier) :=
    Uniform05.RestrictedLaw.continuous_multiplier.comp continuous_fst
  have hB : Continuous (fun p : Uniform05.RestrictedLaw i×(Value i×unitInterval)=>(baseBid i p.2:ℝ)) :=
    continuous_subtype_val.comp ((continuous_baseBid i).comp continuous_snd)
  have hV : Continuous (fun p : Uniform05.RestrictedLaw i×(Value i×unitInterval)=>(p.2.1:ℝ)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hp : Continuous (fun p : Uniform05.RestrictedLaw i×(Value i×unitInterval)=>
      ClippedResidual.exposure (Uniform05.xi i) p.1.multiplier (baseBid i p.2)) := by
    unfold ClippedResidual.exposure
    apply continuous_const.min
    exact (continuous_const.max (hB.sub hL)).div (continuous_const.mul (hB.max hL)) (fun p=> by
      have hl := (Uniform05.demandLo_pos i).trans p.1.multiplier_guards.1
      exact (mul_pos (Uniform05.xi_range i).1 (hl.trans_le (le_max_right _ _))).ne')
  exact (hV.mul ((continuous_const.mul hp).sub (hp.pow 2))).sub
    (((continuous_const.mul hB).mul hp).mul (continuous_const.sub (continuous_const.mul hp)))

def choiceProductMap (i : Row) (G : Uniform05.RestrictedLaw i) : C(Value i×unitInterval,ℝ) :=
  ⟨choiceProduct i G,(continuous_choiceProduct i).comp (continuous_const.prodMk continuous_id)⟩

lemma continuous_choiceProductMap (i : Row) : Continuous (choiceProductMap i) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_choiceProduct i)

lemma productChoice_allAction_to_physical (i : Row) (pi : Joint i)
    (hopt : AllActionOptimal pi (choiceProduct i (restrictedLaw i (0,pi)))) :
    ProductOptimal i (restrictedLaw i (0,pi)) := by
  let G := restrictedLaw i (0,pi)
  have hv := original_value_positive i pi
  have hbase : ∀ᵐp ∂(pi.1 : Measure (Value i×unitInterval)),
      ∀a∈Icc (Uniform05.floorBid i p.1) (min (p.1:ℝ) (Uniform05.cap i)),
        productPayoff (Uniform05.xi i) p.1 G.multiplier a≤
          productPayoff (Uniform05.xi i) p.1 G.multiplier (baseBid i p) := by
    filter_upwards [hopt,hv] with p hp hpos
    intro a ha
    have h := hp (choiceForBid i p.1 a)
    change productPayoff (Uniform05.xi i) p.1 G.multiplier
      (baseBid i (p.1,choiceForBid i p.1 a))≤ _ at h
    rwa [choiceForBid_exact i p.1 hpos a ha] at h

  have hm : (G.1 : Measure (ℝ×Bid i))=(pi.1 : Measure (Value i×unitInterval)).map
      (fun p=>((p.1:ℝ),baseBid i p)) := by
    change (((physicalLaw i (0,pi)).1 : Measure (Value i×Bid i)).map
      (fun p : Value i×Bid i=>((p.1:ℝ),p.2)))=_
    rw [physicalLaw_zero]
    change (((pi.1 : Measure (Value i×unitInterval)).map
      (fun p=>(p.1,baseBid i p))).map (fun p : Value i×Bid i=>((p.1:ℝ),p.2)))=_
    convert! (Measure.map_map (μ := (pi.1 : Measure (Value i×unitInterval)))
      ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
      (measurable_fst.prodMk (continuous_baseBid i).measurable)) using 1

  let B : ℝ→ unitInterval→ℝ := fun v q=>
    Uniform05.floorBid i v+(min v (Uniform05.cap i)-Uniform05.floorBid i v)*(q:ℝ)
  let good : Set (ℝ×Bid i) := {p | ∀q : unitInterval,
    productPayoff (Uniform05.xi i) p.1 G.multiplier (B p.1 q)≤
      productPayoff (Uniform05.xi i) p.1 G.multiplier p.2}
  have hL : 0< G.multiplier := (Uniform05.demandLo_pos i).trans G.multiplier_guards.1
  have hcont:=continuous_product_fixed_root (Uniform05.xi_range i).1 hL
  have hgood : MeasurableSet good := by
    have he : good=⋂q : unitInterval,{p : ℝ×Bid i |
        productPayoff (Uniform05.xi i) p.1 G.multiplier (B p.1 q)≤
          productPayoff (Uniform05.xi i) p.1 G.multiplier p.2} := by ext p; simp [good]
    rw [he]
    apply IsClosed.measurableSet
    apply isClosed_iInter
    intro q
    have hB : Continuous (fun p : ℝ×Bid i=> B p.1 q) := by
      dsimp [B]
      have hf:=Uniform05.continuous_floor i
      fun_prop
    exact isClosed_le (hcont.comp (continuous_fst.prodMk hB))
      (hcont.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  have hq : ∀ᵐp∂(G.1 : Measure (ℝ×Bid i)),p∈good := by
    rw [hm]
    apply (ae_map_iff
      (((measurable_subtype_coe.comp measurable_fst).prodMk
        (continuous_baseBid i).measurable).aemeasurable) hgood).mpr
    filter_upwards [hopt] with p hp
    intro q
    have hh:=hp q
    simpa only [choiceProduct,baseBid_val,width,hiBid,B,good,mem_setOf_eq,
      Function.comp_def, G] using hh
  filter_upwards [hq,G.2.2,G.value_positive] with p hp hpair hvp
  intro a ha
  let v : Value i:=⟨p.1,hpair.1⟩
  have he:=choiceForBid_exact i v hvp a ha
  have hh:=hp (choiceForBid i v a)
  have he' : B p.1 (choiceForBid i v a)=a := by
    simpa only [baseBid_val,width,hiBid,B,v] using he
  rwa [he'] at hh

theorem product_optimality_from_noisy_IC (i : Row)
    (N : ℕ→ℕ) (eps : ℕ→ unitInterval) (pi : ℕ→ Joint i) (pi0 : Joint i)
    (heps : Tendsto eps atTop (𝓝 0)) (hpi : Tendsto pi atTop (𝓝 pi0))
    (hIC : ∀n,NoisyIC i (N n) (eps n) (pi n))
    (err : ℕ→ℝ) (herr : ∀n,0≤ err n) (herr0 : Tendsto err atTop (𝓝 0))
    (hmenu : ∀(n : ℕ) (p : Value i×unitInterval),
      |expectedUtility i (N n) (eps n) (pi n) p.1 p.2-
        choiceProduct i (restrictedLaw i (eps n,pi n)) p|≤ err n) :
    ProductOptimal i (restrictedLaw i (0,pi0)) := by
  let G := fun n=> restrictedLaw i (eps n,pi n)
  let G0 := restrictedLaw i (0,pi0)
  have hG : Tendsto G atTop (𝓝 G0) :=
    (continuous_restrictedLaw i).continuousAt.tendsto.comp (heps.prodMk_nhds hpi)
  let d := fun n=> err n+‖choiceProductMap i (G n)-choiceProductMap i G0‖
  have hd0 : Tendsto d atTop (𝓝 0) := by
    have hf := (continuous_choiceProductMap i).continuousAt.tendsto.comp hG
    have hd := herr0.add ((hf.sub (tendsto_const_nhds (x := choiceProductMap i G0))).norm)
    convert! hd using 1; simp only [sub_self,norm_zero,add_zero]
  have hd : ∀n,0≤ d n := fun n=> add_nonneg (herr n) (norm_nonneg _)
  have happrox (n : ℕ) (p : Value i×unitInterval) :
      |expectedUtility i (N n) (eps n) (pi n) p.1 p.2-choiceProductMap i G0 p|≤ d n := by
    calc
      _ ≤ |expectedUtility i (N n) (eps n) (pi n) p.1 p.2-choiceProduct i (G n) p|+
        |choiceProduct i (G n) p-choiceProduct i G0 p| := abs_sub_le _ _ _
      _ ≤ d n := add_le_add (hmenu n p) (by
        convert! (by simpa only [Real.norm_eq_abs] using
          (choiceProductMap i (G n)-choiceProductMap i G0).norm_coe_le_norm p) using 1)
  apply productChoice_allAction_to_physical i pi0
  exact allAction_limit_of_uniform_error (lowerMeasure i) pi pi0 hpi
    (choiceProductMap i G0)
    (fun n p=> expectedUtility i (N n) (eps n) (pi n) p.1 p.2) d hd hd0 happrox hIC

end FCAppendix.Affine.UniformFinite
