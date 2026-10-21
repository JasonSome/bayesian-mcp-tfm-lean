import FCAppendix.Affine.UniformFinite.NativeSeedErasure
import FCAppendix.Affine.UniformFinite.ConditionalRandomizer

noncomputable section
set_option maxHeartbeats 1000000
namespace FCAppendix.Affine.UniformFinite.NativeRow
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game
open Uniform05 SourceContinuity WeightedSampling
open scoped BigOperators
variable {M : ℕ} [NeZero M]

lemma draw_joint_measurable (i : Row) (row : Source.CountRow M) :
    Measurable (fun x : State i M×Seeds=> draw i row x.1 x.2) := by
  convert! ((select_measurable i row 0).comp
    ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd.fst)).prodMk
      ((select_measurable i row 1).comp
        ((measurable_fst.prodMk measurable_snd.fst).prodMk measurable_snd.snd.snd)) using 1

abbrev Rest (i : Row) (S : Finset (Fin M)) := {a : Fin M // a∉S}→ Bid i

def keep {i : Row} (S : Finset (Fin M)) (b : Fin M→ Bid i) : Rest i S := fun a=> b a

def fill (i : Row) (S : Finset (Fin M)) (r : Rest i S) : Fin M→ Bid i :=
  fun a=> if ha : a∈S then ⟨0,le_rfl,(cap_pos i).le⟩ else r ⟨a,ha⟩

omit [NeZero M] in
lemma measurable_keep (i : Row) (S : Finset (Fin M)) :
    Measurable (keep (i:=i) S) := by
  exact measurable_pi_lambda _ (fun a=> measurable_pi_apply a.val)

omit [NeZero M] in
lemma measurable_fill (i : Row) (S : Finset (Fin M)) : Measurable (fill i S) := by
  apply measurable_pi_lambda
  intro a
  by_cases ha : a∈S
  · simpa only [fill,dif_pos ha] using
      (measurable_const : Measurable (fun _ : Rest i S=>(⟨0,le_rfl,(cap_pos i).le⟩ : Bid i)))
  · simpa only [fill,dif_neg ha] using (measurable_pi_apply (⟨a,ha⟩ : {a : Fin M // a∉S}))

omit [NeZero M] in
lemma fill_keep (i : Row) (S : Finset (Fin M)) (G : RestrictedLaw i) (b : Fin M→ Bid i) :
    (G,fill i S (keep S b))=eraseState i S (G,b) := by
  congr 1

def correction (i : Row) (row : Source.CountRow M) (G : RestrictedLaw i)
    (S : Finset (Fin M)) (f : Allocation M→ℝ)
    (r : Rest i S×(unitInterval×unitInterval)) (u : unitInterval) : ℝ :=
  if Source.residual row 0≠Source.residual row 1 ∧ 0< rawWeight i row (G,fill i S r.1) then
    f (draw i row (G,fill i S r.1) (u,r.2))-f (draw i row (G,fill i S r.1) (0,r.2))
  else 0

lemma measurable_correction (i : Row) (row : Source.CountRow M) (G : RestrictedLaw i)
    (S : Finset (Fin M)) (f : Allocation M→ℝ) :
    Measurable (Function.uncurry (correction i row G S f)) := by
  have hx : Measurable (fun x : (Rest i S×(unitInterval×unitInterval))×unitInterval=>
      (show State i M from (G,fill i S x.1.1))) :=
    (measurable_fixedLawState i G).comp ((measurable_fill i S).comp measurable_fst.fst)
  have hu := (measurable_of_countable f).comp ((draw_joint_measurable i row).comp
    (hx.prodMk (measurable_snd.prodMk measurable_fst.snd)))
  have hz := (measurable_of_countable f).comp ((draw_joint_measurable i row).comp
    (hx.prodMk ((measurable_const (a := (0:unitInterval))).prodMk measurable_fst.snd)))
  change Measurable (fun x : (Rest i S×(unitInterval×unitInterval))×unitInterval=>
    correction i row G S f x.1 x.2)
  by_cases he : Source.residual row 0=Source.residual row 1
  · simp only [correction,he,ne_eq,not_true_eq_false,false_and,if_false]
    exact measurable_const
  · simp only [correction,he,ne_eq,not_false_eq_true,true_and]
    convert! Measurable.ite
      (measurableSet_lt measurable_const ((continuous_rawWeight i row).measurable.comp hx))
      (hu.sub hz) measurable_const using 1

lemma correction_bound (i : Row) (row : Source.CountRow M) (G : RestrictedLaw i)
    (S : Finset (Fin M)) (f : Allocation M→ℝ)
    (r : Rest i S×(unitInterval×unitInterval)) (u : unitInterval) :
    |correction i row G S f r u|≤2*∑P,|f P| := by
  unfold correction
  split_ifs
  · have h1 := finite_bound f (draw i row (G,fill i S r.1) (u,r.2))
    have h2 := finite_bound f (draw i row (G,fill i S r.1) (0,r.2))
    exact (abs_sub _ _).trans (by linarith)
  · simp only [abs_zero]
    positivity

lemma draw_difference_factors (i : Row) (row : Source.CountRow M) (G : RestrictedLaw i)
    (S : Finset (Fin M)) (b : Fin M→ Bid i) (hS : ∀a∈S,(b a:ℝ)≤ t i/2)
    (f : Allocation M→ℝ) (s : unitInterval×unitInterval) (u : unitInterval) :
    f (draw i row (G,b) (u,s))-f (draw i row (G,b) (0,s))=
      correction i row G S f (keep S b,s) u := by
  rw [correction,fill_keep]
  by_cases he : Source.residual row 0=Source.residual row 1
  · rw [if_neg (by simp [he]),draw_common_irrelevant i row (G,b) (Or.inl he) u 0 s,sub_self]
  · by_cases hr : 0< rawWeight i row (G,b)
    · rw [if_pos ⟨he,by rwa [rawWeight_erase i row S (G,b) hS]⟩,
        draw_erase i row he S (G,b) hS hr,draw_erase i row he S (G,b) hS hr]
    · have hz : Source.rawAlpha i G row (bids i (G,b))=0 :=
        le_antisymm (le_of_not_gt hr) (rawWeight_bounds i row (G,b)).1
      have ha : Source.guardAlpha i G row (bids i (G,b))=0 := by
        simp only [Source.guardAlpha,hz,ite_self]
      rw [if_neg (by rw [rawWeight_erase i row S (G,b) hS]; exact fun h=> hr h.2),
        draw_common_irrelevant i row (G,b) (Or.inr ha) u 0 s,sub_self]

theorem conditional_minimum_draw_integral (i : Row) (row : Source.CountRow M)
    (G : RestrictedLaw i) (S : Finset (Fin M))
    (ν : Fin M→ Measure (Bid i)) [∀a,IsProbabilityMeasure (ν a)]
    (hbox : ∀a∈S,∀ᵐ(b : Bid i)∂ν a,(b:ℝ)≤ t i/2)
    (n : ℕ) (e : Fin (n+1)≃{a : Fin M // a∈S})
    (μseed : Measure ℝ) [IsProbabilityMeasure μseed]
    (hseed : ∀j,(ν (e j)).map (fun b : Bid i=>(b:ℝ))=μseed)
    (hatom : ∀z : ℝ,μseed {z}=0) (f : Allocation M→ℝ) :
    (∫x : (Fin M→ Bid i)×(unitInterval×unitInterval),
      f (draw i row (G,x.1)
        (Hybrid.conditionalMinimumSeed μseed n (fun j=>(x.1 (e j):ℝ)),x.2))
      ∂((Measure.pi ν).prod ((volume : Measure unitInterval).prod volume))) =
    ∫b : Fin M→ Bid i,(continuationLaw i G row (bids i (G,b))).expect f ∂Measure.pi ν := by
  let μ : Measure (Fin M→ Bid i):=Measure.pi ν
  let ω : Measure (unitInterval×unitInterval):=(volume : Measure unitInterval).prod volume
  let T : ((Fin M→ Bid i)×(unitInterval×unitInterval))→ unitInterval :=
    fun x=> Hybrid.conditionalMinimumSeed μseed n (fun j=>(x.1 (e j):ℝ))
  let K : ((Fin M→ Bid i)×(unitInterval×unitInterval))→ Rest i S×(unitInterval×unitInterval) :=
    fun x=>(keep S x.1,x.2)
  let F : ((Fin M→ Bid i)×(unitInterval×unitInterval))→ unitInterval→ℝ :=
    fun x u=> f (draw i row (G,x.1) (u,x.2))
  have hT : Measurable T := (Hybrid.measurable_conditionalMinimumSeed μseed n).comp
    (measurable_pi_lambda _ (fun j=> measurable_subtype_coe.comp
      ((measurable_pi_apply (e j).val).comp measurable_fst)))
  have hK : Measurable K := ((measurable_keep i S).comp measurable_fst).prodMk measurable_snd
  have hF : Measurable (Function.uncurry F) := by
    convert! (measurable_of_countable f).comp ((draw_joint_measurable i row).comp
      (((measurable_fixedLawState i G).comp measurable_fst.fst).prodMk
        (measurable_snd.prodMk measurable_fst.snd))) using 1
  have hjoint : (μ.prod ω).map (fun x=>(T x,K x))=
      (volume : Measure unitInterval).prod ((Measure.pi (fun a : {a : Fin M // a∉S}=>ν a)).prod ω) :=
    Literal.heterogeneous_minimum_seed_joint ν (fun a=> a∈S) n e
      (fun b : Bid i=>(b:ℝ)) measurable_subtype_coe μseed hseed hatom ω
  have hb : ∀ᵐb∂μ,∀a∈S,(b a:ℝ)≤ t i/2 := by
    apply ae_all_iff.mpr
    intro a
    by_cases ha : a∈S
    · have hb' : ∀ᵐb∂Measure.pi ν,(b a:ℝ)≤t i/2 :=
        (measurePreserving_eval ν a).quasiMeasurePreserving.ae (hbox a ha)
      exact hb'.mono (fun b hb _=>hb)
    · exact ae_of_all _ (fun b h=> False.elim (ha h))
  have hdiff : ∀ᵐx∂μ.prod ω,∀u,F x u-F x 0=correction i row G S f (K x) u := by
    filter_upwards [(measurePreserving_fst (μ:=μ) (ν:=ω)).quasiMeasurePreserving.ae hb] with x hx
    intro u
    exact draw_difference_factors i row G S x.1 hx f x.2 u
  have hreplace := Literal.conditional_randomizer_replacement (μ.prod ω)
    ((Measure.pi (fun a : {a : Fin M // a∉S}=>ν a)).prod ω)
    T hT K hK hjoint F hF (correction i row G S f) (measurable_correction i row G S f)
    (∑P,|f P|) (2*∑P,|f P|) (fun x u=> finite_bound f _)
    (correction_bound i row G S f) hdiff
  change (∫x,F x (T x) ∂μ.prod ω)=_
  rw [hreplace]
  have hiu (u : unitInterval) : Integrable (fun x=> F x u) (μ.prod ω) :=
    Integrable.of_bound (hF.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
      (∑P,|f P|) (Eventually.of_forall (fun x=> finite_bound f _))
  have h3 : Integrable (fun p : (unitInterval×(Fin M→ Bid i))×(unitInterval×unitInterval)=>
      f (draw i row (G,p.1.2) (p.1.1,p.2)))
      (((volume : Measure unitInterval).prod μ).prod ω) :=
    Integrable.of_bound
      ((measurable_of_countable f).comp ((draw_joint_measurable i row).comp
        (((measurable_fixedLawState i G).comp measurable_fst.snd).prodMk
          (measurable_fst.fst.prodMk measurable_snd)))).aestronglyMeasurable
      (∑P,|f P|) (Eventually.of_forall (fun p=> finite_bound f _))
  calc
    _=∫u : unitInterval,∫b : Fin M→ Bid i,∫s,f (draw i row (G,b) (u,s)) ∂ω ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun u=> integral_prod _ (hiu u))
    _=∫b : Fin M→ Bid i,(∫u : unitInterval,∫s,f (draw i row (G,b) (u,s)) ∂ω) ∂μ :=
      integral_integral_swap h3.integral_prod_left
    _=_ := by
      apply integral_congr_ae
      apply ae_of_all
      intro b
      have hi : Integrable (fun s : Seeds=> f (draw i row (G,b) s)) seedsLaw :=
        Integrable.of_bound ((measurable_of_countable f).comp
          (draw_measurable i row (G,b))).aestronglyMeasurable (∑P,|f P|)
          (Eventually.of_forall (fun s=> finite_bound f _))
      convert! (integral_prod _ hi).symm.trans
        (draw_integral i row (show State i M from (G,b)) f) using 1

end FCAppendix.Affine.UniformFinite.NativeRow
