import FCAppendix.Affine.UniformFinite.Late.NativeExceptionalLaw
import FCAppendix.Affine.UniformFinite.Late.ExceptionalSeedErasure
import FCAppendix.Affine.UniformFinite.ConditionalRandomizer

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.Late.NativeExceptionalRow
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game
open Uniform05 ClippedResidual WeightedSampling
open scoped BigOperators
variable {M : ℕ} [NeZero M]

theorem draw_joint_measurable (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) : Measurable (fun x : (Fin M → ℝ) × NativeRow.Seeds => draw i G row a x.1 x.2) := by
  convert! ((select_measurable i G row a 0).comp
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd.fst)).prodMk
      ((select_measurable i G row a 1).comp
        ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd.snd)) using 1

theorem commonLaw_erase (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (S : Finset (Fin M)) (b : Fin M → ℝ) (hS : ∀j∈S,b j≤ t i/2) :
    commonLaw i G row a (SeedErasure.erase S b)=commonLaw i G row a b := by
  simp only [commonLaw,Exceptional.weight_erase i G row S b a hS,
    Exceptional.alpha_erase i G row S b a hS]

theorem privateLaw_erase (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (S : Finset (Fin M)) (b : Fin M → ℝ) (hb : Good i row a b)
    (hS : ∀j∈S,b j≤ t i/2) (hne : Source.residual row 0≠Source.residual row 1)
    (hα : 0< Exceptional.alpha i G row b a) (q : Signal row)
    (hq : 0<(commonLaw i G row a b).mass q) (j : Fin 2) :
    privateLaw i row j (SeedErasure.erase S b) q=privateLaw i row j b q := by
  cases q with
  | none =>
    simp only [privateLaw,if_neg hne,pureSet,
      Exceptional.pure_selection_erase i G row S b a hb.2.1 hS hα]
  | some p =>
    have hp := (common_some_support i G row a b p hq).2.2
    have he := Exceptional.guarded_private_erase i G row S b a hb.1 hb.2.1 hb.2.2 hS hα p hp
    simp only [privateLaw,if_neg hne,smallLaw,largeLaw,he.1,he.2.1]

theorem select_erase (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (S : Finset (Fin M)) (b : Fin M → ℝ) (hb : Good i row a b)
    (hS : ∀j∈S,b j≤ t i/2) (hne : Source.residual row 0≠Source.residual row 1)
    (hα : 0< Exceptional.alpha i G row b a) (j : Fin 2) (u s : unitInterval) :
    select i G row a j (SeedErasure.erase S b) u s=select i G row a j b u s := by
  have hcommon : commonSample i G row a (SeedErasure.erase S b) u=commonSample i G row a b u := by
    simp only [commonSample,commonLaw_erase i G row a S b hS]
  simp only [select,hcommon,privateSample,
    privateLaw_erase i G row a S b hb hS hne hα _ (commonSample_support i G row a b u) j]

theorem draw_erase (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (S : Finset (Fin M)) (b : Fin M → ℝ) (hb : Good i row a b)
    (hS : ∀j∈S,b j≤ t i/2) (hne : Source.residual row 0≠Source.residual row 1)
    (hα : 0< Exceptional.alpha i G row b a) (s : NativeRow.Seeds) :
    draw i G row a (SeedErasure.erase S b) s=draw i G row a b s := by
  simp only [draw,select_erase i G row a S b hb hS hne hα]

theorem commonSample_none (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ)
    (h : Source.residual row 0=Source.residual row 1 ∨ Exceptional.alpha i G row b a=0)
    (u : unitInterval) : commonSample i G row a b u=none := by
  have hP : commonLaw i G row a b=FiniteLaw.dirac none := by
    rcases h with he|hα
    · simp [commonLaw,he]
    · by_cases he : Source.residual row 0=Source.residual row 1
      · simp [commonLaw,he]
      · apply FiniteLaw.ext
        intro q
        simp [commonLaw,he,Literal.signalLaw,FiniteLaw.mixture,hα]
  simp only [commonSample,hP,ExtensionalSampler.dirac]

theorem draw_common_irrelevant (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (b : Fin M → ℝ)
    (h : Source.residual row 0=Source.residual row 1 ∨ Exceptional.alpha i G row b a=0)
    (u u' : unitInterval) (s : unitInterval×unitInterval) :
    draw i G row a b (u,s)=draw i G row a b (u',s) := by
  simp only [draw,select,commonSample_none i G row a b h]

theorem private_integral_common_irrelevant (i : Row) (G : RestrictedLaw i)
    (row : Source.CountRow M) (a : Fin M) (b : Fin M → ℝ)
    (h : Source.residual row 0=Source.residual row 1 ∨ Exceptional.alpha i G row b a=0)
    (u : unitInterval) (f : Allocation M→ℝ) :
    (∫s,f (draw i G row a b (u,s)) ∂((volume : Measure unitInterval).prod volume))=
      (Exceptional.continuationLaw i G row b a).expect f := by
  have hd := draw_integral i G row a b f
  have hint : Integrable (fun s => f (draw i G row a b s)) NativeRow.seedsLaw :=
    Integrable.of_bound ((measurable_of_countable f).comp (draw_measurable i G row a b)).aestronglyMeasurable
      (∑P,|f P|) (ae_of_all _ (fun s => NativeRow.finite_bound f _))
  rw [NativeRow.seedsLaw,integral_prod _ hint] at hd
  have he : (fun q : unitInterval=>∫s,f (draw i G row a b (q,s))
      ∂((volume : Measure unitInterval).prod volume)) =
      fun _ : unitInterval=>∫s,f (draw i G row a b (u,s))
        ∂((volume : Measure unitInterval).prod volume) := by
    funext q
    simp only [draw_common_irrelevant i G row a b h q u]
  rw [he] at hd
  simpa using hd

abbrev Rest (S : Finset (Fin M)) := {a : Fin M // a∉S} → ℝ

def keep (S : Finset (Fin M)) (b : Fin M → ℝ) : Rest S := fun a => b a

def fill (S : Finset (Fin M)) (r : Rest S) : Fin M → ℝ :=
  fun a => if ha : a∈S then 0 else r ⟨a,ha⟩

omit [NeZero M] in
theorem measurable_keep (S : Finset (Fin M)) : Measurable (keep S) :=
  measurable_pi_lambda _ (fun a => measurable_pi_apply a.val)

omit [NeZero M] in
theorem measurable_fill (S : Finset (Fin M)) : Measurable (fill S) := by
  apply measurable_pi_lambda
  intro a
  by_cases ha : a∈S
  · simpa only [fill,dif_pos ha] using (measurable_const : Measurable (fun _ : Rest S => (0:ℝ)))
  · simpa only [fill,dif_neg ha] using (measurable_pi_apply (⟨a,ha⟩ : {a : Fin M // a∉S}))

omit [NeZero M] in
theorem fill_keep (S : Finset (Fin M)) (b : Fin M → ℝ) :
    fill S (keep S b)=SeedErasure.erase S b := by
  funext a
  by_cases ha : a∈S <;> simp [fill,keep,SeedErasure.erase,ha]

def correction (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M) (a : Fin M)
    (S : Finset (Fin M)) (f : Allocation M→ℝ)
    (r : Rest S×(unitInterval×unitInterval)) (u : unitInterval) : ℝ :=
  if Source.residual row 0≠Source.residual row 1 ∧ 0< Exceptional.alpha i G row (fill S r.1) a then
    f (draw i G row a (fill S r.1) (u,r.2))-f (draw i G row a (fill S r.1) (0,r.2))
  else 0

theorem measurable_correction (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (S : Finset (Fin M)) (f : Allocation M→ℝ) :
    Measurable (Function.uncurry (correction i G row a S f)) := by
  have hb : Measurable (fun x : (Rest S×(unitInterval×unitInterval))×unitInterval => fill S x.1.1) :=
    (measurable_fill S).comp measurable_fst.fst
  have hu : Measurable (fun x : (Rest S×(unitInterval×unitInterval))×unitInterval=>
      f (draw i G row a (fill S x.1.1) (x.2,x.1.2))) := by
    convert! (measurable_of_countable f).comp ((draw_joint_measurable i G row a).comp
      (hb.prodMk (measurable_snd.prodMk measurable_fst.snd))) using 1
  have hz : Measurable (fun x : (Rest S×(unitInterval×unitInterval))×unitInterval=>
      f (draw i G row a (fill S x.1.1) (0,x.1.2))) := by
    convert! (measurable_of_countable f).comp ((draw_joint_measurable i G row a).comp
      (hb.prodMk (measurable_const.prodMk measurable_fst.snd))) using 1
  change Measurable (fun x : (Rest S×(unitInterval×unitInterval))×unitInterval=>
    if Source.residual row 0≠Source.residual row 1 ∧
        0<Exceptional.alpha i G row (fill S x.1.1) a then
      f (draw i G row a (fill S x.1.1) (x.2,x.1.2))-
        f (draw i G row a (fill S x.1.1) (0,x.1.2)) else 0)
  by_cases he : Source.residual row 0=Source.residual row 1
  · simp only [he,ne_eq,not_true_eq_false,false_and,if_false]
    exact measurable_const
  · simp only [he,ne_eq,not_false_eq_true,true_and]
    exact Measurable.ite
      (measurableSet_lt measurable_const ((Exceptional.measurable_alpha i G row a).comp hb))
      (hu.sub hz) measurable_const

theorem correction_bound (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (S : Finset (Fin M)) (f : Allocation M→ℝ)
    (r : Rest S×(unitInterval×unitInterval)) (u : unitInterval) :
    |correction i G row a S f r u|≤2*∑P,|f P| := by
  unfold correction
  split_ifs
  · have h0:=NativeRow.finite_bound f (draw i G row a (fill S r.1) (u,r.2))
    have h1:=NativeRow.finite_bound f (draw i G row a (fill S r.1) (0,r.2))
    exact (abs_sub _ _).trans (by linarith)
  · simp only [abs_zero]
    positivity

theorem draw_difference_factors (i : Row) (G : RestrictedLaw i) (row : Source.CountRow M)
    (a : Fin M) (S : Finset (Fin M)) (b : Fin M → ℝ) (hb : Good i row a b)
    (hS : ∀j∈S,b j≤ t i/2) (f : Allocation M→ℝ)
    (s : unitInterval×unitInterval) (u : unitInterval) :
    f (draw i G row a b (u,s))-f (draw i G row a b (0,s))=
      correction i G row a S f (keep S b,s) u := by
  rw [correction,fill_keep]
  by_cases he : Source.residual row 0=Source.residual row 1
  · rw [if_neg (by simp [he]),draw_common_irrelevant i G row a b (Or.inl he) u 0 s,sub_self]
  · by_cases hα : 0< Exceptional.alpha i G row b a
    · rw [if_pos ⟨he,by rwa [Exceptional.alpha_erase i G row S b a hS]⟩,
        draw_erase i G row a S b hb hS he hα,draw_erase i G row a S b hb hS he hα]
    · have hz : Exceptional.alpha i G row b a=0 :=
        le_antisymm (le_of_not_gt hα) (Exceptional.alpha_bounds i G row b a).1
      rw [if_neg (by rw [Exceptional.alpha_erase i G row S b a hS]; exact fun h => hα h.2),
        draw_common_irrelevant i G row a b (Or.inr hz) u 0 s,sub_self]

theorem conditional_minimum_draw_integral (i : Row) (G : RestrictedLaw i)
    (row : Source.CountRow M) (a : Fin M) (S : Finset (Fin M))
    (ν : Fin M→ Measure ℝ) [∀j,IsProbabilityMeasure (ν j)]
    (hgood : ∀ᵐb∂Measure.pi ν,Good i row a b)
    (hbox : ∀j∈S,∀ᵐb∂ν j,b≤ t i/2)
    (n : ℕ) (e : Fin (n+1)≃{j : Fin M // j∈S})
    (μseed : Measure ℝ) [IsProbabilityMeasure μseed]
    (hseed : ∀j,ν (e j)=μseed) (hatom : ∀z : ℝ,μseed {z}=0) (f : Allocation M→ℝ) :
    (∫x : (Fin M→ℝ)×(unitInterval×unitInterval),
      f (draw i G row a x.1 (Hybrid.conditionalMinimumSeed μseed n (fun j=> x.1 (e j)),x.2))
      ∂((Measure.pi ν).prod ((volume : Measure unitInterval).prod volume))) =
    ∫b : Fin M→ℝ,(Exceptional.continuationLaw i G row b a).expect f ∂Measure.pi ν := by
  let μ : Measure (Fin M→ℝ) := Measure.pi ν
  let ω : Measure (unitInterval×unitInterval) := (volume : Measure unitInterval).prod volume
  let T : ((Fin M→ℝ)×(unitInterval×unitInterval))→ unitInterval :=
    fun x=> Hybrid.conditionalMinimumSeed μseed n (fun j=> x.1 (e j))
  let K : ((Fin M→ℝ)×(unitInterval×unitInterval))→ Rest S×(unitInterval×unitInterval) :=
    fun x=>(keep S x.1,x.2)
  let F : ((Fin M→ℝ)×(unitInterval×unitInterval))→ unitInterval→ℝ :=
    fun x u=> f (draw i G row a x.1 (u,x.2))
  have hT : Measurable T := (Hybrid.measurable_conditionalMinimumSeed μseed n).comp
    (measurable_pi_lambda _ (fun j=>(measurable_pi_apply (e j).val).comp measurable_fst))
  have hK : Measurable K := ((measurable_keep S).comp measurable_fst).prodMk measurable_snd
  have hF : Measurable (Function.uncurry F) := by
    convert! (measurable_of_countable f).comp ((draw_joint_measurable i G row a).comp
      (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))) using 1
  have hjoint : (μ.prod ω).map (fun x=>(T x,K x))=
      (volume : Measure unitInterval).prod ((Measure.pi (fun j : {j : Fin M // j∉S}=>ν j)).prod ω) := by
    apply Literal.heterogeneous_minimum_seed_joint ν (fun j=> j∈S) n e
      id measurable_id μseed _ hatom ω
    intro j
    simpa only [Measure.map_id] using hseed j
  have hb : ∀ᵐb∂μ,∀j∈S,b j≤ t i/2 := by
    apply ae_all_iff.mpr
    intro j
    by_cases hj : j∈S
    · exact ((measurePreserving_eval ν j).quasiMeasurePreserving.ae (hbox j hj)).mono
        (fun b hb _=> hb)
    · exact ae_of_all _ (fun b h=> False.elim (hj h))
  have hdiff : ∀ᵐx∂μ.prod ω,∀u,F x u-F x 0=correction i G row a S f (K x) u := by
    filter_upwards [(measurePreserving_fst (μ:=μ) (ν:=ω)).quasiMeasurePreserving.ae hb,
      (measurePreserving_fst (μ:=μ) (ν:=ω)).quasiMeasurePreserving.ae hgood] with x hx hg
    intro u
    exact draw_difference_factors i G row a S x.1 hg hx f x.2 u
  have hreplace := Literal.conditional_randomizer_replacement (μ.prod ω)
    ((Measure.pi (fun j : {j : Fin M // j∉S}=>ν j)).prod ω)
    T hT K hK hjoint F hF (correction i G row a S f) (measurable_correction i G row a S f)
    (∑P,|f P|) (2*∑P,|f P|) (fun x u=> NativeRow.finite_bound f _)
    (correction_bound i G row a S f) hdiff
  change (∫x,F x (T x) ∂μ.prod ω)=_
  rw [hreplace]
  have hiu (u : unitInterval) : Integrable (fun x=> F x u) (μ.prod ω) :=
    Integrable.of_bound (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (∑P,|f P|) (ae_of_all _ (fun x=> NativeRow.finite_bound f _))
  have h3 : Integrable (fun p : (unitInterval×(Fin M→ℝ))×(unitInterval×unitInterval)=>
      f (draw i G row a p.1.2 (p.1.1,p.2)))
      (((volume : Measure unitInterval).prod μ).prod ω) :=
    Integrable.of_bound
      ((measurable_of_countable f).comp ((draw_joint_measurable i G row a).comp
        (measurable_fst.snd.prodMk (measurable_fst.fst.prodMk measurable_snd)))).aestronglyMeasurable
      (∑P,|f P|) (ae_of_all _ (fun p=> NativeRow.finite_bound f _))
  calc
    _=(∫u : unitInterval, (∫b : Fin M→ℝ,
      (∫s,f (draw i G row a b (u,s)) ∂ω) ∂μ) ∂volume) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun u=> integral_prod _ (hiu u))
    _=(∫b : Fin M→ℝ, (∫u : unitInterval,
      (∫s,f (draw i G row a b (u,s)) ∂ω) ∂volume) ∂μ) :=
      integral_integral_swap h3.integral_prod_left
    _=_ := by
      apply integral_congr_ae
      apply ae_of_all
      intro b
      have hi : Integrable (fun s : NativeRow.Seeds=> f (draw i G row a b s)) NativeRow.seedsLaw :=
        Integrable.of_bound ((measurable_of_countable f).comp
          (draw_measurable i G row a b)).aestronglyMeasurable (∑P,|f P|)
          (ae_of_all _ (fun s=> NativeRow.finite_bound f _))
      have hd:=draw_integral i G row a b f
      rw [NativeRow.seedsLaw,integral_prod _ hi] at hd
      convert! hd using 1

end FCAppendix.Affine.UniformFinite.Late.NativeExceptionalRow
