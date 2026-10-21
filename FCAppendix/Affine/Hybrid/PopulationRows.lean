import FCAppendix.Affine.Hybrid.PopulationGame

noncomputable section
namespace FCAppendix.Affine.Hybrid
open MeasureTheory ProbabilityTheory Set Game Bayes Classical
open Existence.Distributional

theorem collapse_low_population (P : ProbabilityMeasure (ℝ×JointAction 2)) (d U : ℝ)
    (hP : ∀ᵐx ∂(P : Measure (ℝ×JointAction 2)),x.2.bid≤d) :
    ((P : Measure (ℝ×JointAction 2)).prod (permLaw 2)).map
      (fun u : UserDraw 2=>collapseAction d U (u.1.2,u.2))=
      ((P : Measure (ℝ×JointAction 2)).map (fun x=>x.2.bid)).map (fun b=>((0:Fin 4),b)) := by
  have hpoint:= (measurePreserving_fst (μ:=(P : Measure (ℝ×JointAction 2))) (ν:=permLaw 2)).quasiMeasurePreserving.ae hP
  have he : ((P : Measure (ℝ×JointAction 2)).prod (permLaw 2)).map
      (fun u : UserDraw 2=>collapseAction d U (u.1.2,u.2))=
      ((P : Measure (ℝ×JointAction 2)).prod (permLaw 2)).map (fun u : UserDraw 2=>((0:Fin 4),u.1.2.bid)) := by
    apply Measure.map_congr
    filter_upwards [hpoint] with u hu
    exact if_pos hu
  rw [he]
  have hb : Measurable (fun x : ℝ×JointAction 2=>x.2.bid):=(measurable_bid 2).comp measurable_snd
  have htag : Measurable (fun b : ℝ=>((0:Fin 4),b)):=measurable_const.prodMk measurable_id
  have hproj := (Measure.map_map (htag.comp hb) measurable_fst
    (μ:=(P : Measure (ℝ×JointAction 2)).prod (permLaw 2))).symm
  simpa only [Measure.map_fst_prod,measure_univ,one_smul,Function.comp_def,
    Measure.map_map htag hb] using hproj

theorem collapse_active_population (P : ProbabilityMeasure (ℝ×JointAction 2)) (d U : ℝ)
    (hP : ∀ᵐx ∂(P : Measure (ℝ×JointAction 2)),d<x.2.bid ∧ x.2.bid≤U) :
    ((P : Measure (ℝ×JointAction 2)).prod (permLaw 2)).map
      (fun u : UserDraw 2=>collapseAction d U (u.1.2,u.2))=Measure.dirac (1,0) := by
  have hpoint:= (measurePreserving_fst (μ:=(P : Measure (ℝ×JointAction 2))) (ν:=permLaw 2)).quasiMeasurePreserving.ae hP
  calc
    _=((P : Measure (ℝ×JointAction 2)).prod (permLaw 2)).map
        (fun _ : UserDraw 2=>((1:Fin 4),(0:ℝ))) := by
      apply Measure.map_congr
      filter_upwards [hpoint] with u hu
      simp only [collapseAction,if_neg (not_le.mpr hu.1),if_pos hu.2]
    _=Measure.dirac (1,0):=by rw [Measure.map_const,measure_univ,one_smul]

theorem collapse_upper_population (P : ProbabilityMeasure (ℝ×JointAction 2)) {d U : ℝ}
    (hdU : d≤U) (hP : ∀ᵐx ∂(P : Measure (ℝ×JointAction 2)),U<x.2.bid) :
    ((P : Measure (ℝ×JointAction 2)).prod (permLaw 2)).map
      (fun u : UserDraw 2=>collapseAction d U (u.1.2,u.2))=
      ENNReal.ofReal (1/2 : ℝ) • Measure.dirac (2,0)+
        ENNReal.ofReal (1/2 : ℝ) • Measure.dirac (3,0) := by
  have hpoint:= (measurePreserving_fst (μ:=(P : Measure (ℝ×JointAction 2))) (ν:=permLaw 2)).quasiMeasurePreserving.ae hP
  calc
    _=((P : Measure (ℝ×JointAction 2)).prod (permLaw 2)).map
        (fun u : UserDraw 2=>upperRow u.2) := by
      apply Measure.map_congr
      filter_upwards [hpoint] with u hu
      simp only [collapseAction,if_neg (not_le.mpr (hdU.trans_lt hu)),if_neg (not_le.mpr hu)]
    _=(permLaw 2).map upperRow := by
      change (((P : Measure (ℝ×JointAction 2)).prod (permLaw 2)).map
        (upperRow ∘ (Prod.snd : UserDraw 2→Equiv.Perm (Fin 2))))=_
      rw [←Measure.map_map (measurable_of_countable upperRow) measurable_snd]
      simp only [Measure.map_snd_prod,measure_univ,one_smul]
    _=_:=upperRow_law

theorem population_collapsed_row {d U : ℝ} (hdU : d≤U) (s a h : ℝ) (hh : 0 ≤ h)
    (mu : Measure (LowBody.LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=LowBody.LowValue d) mu) (PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hactive : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),d<x.2.bid ∧ x.2.bid≤U)
    (hupper : ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),U<x.2.bid) :
    ((populationJoint s a h (lowJoint mu pi) PA PH).prod (permLaw 2)).map
      (fun u : UserDraw 2=>collapseAction d U (u.1.2,u.2))=
      LowBody.rivalLaw s a h (LowBody.realLowBidLaw pi.1 : Measure ℝ) := by
  have hlo : ∀ᵐx ∂(lowJoint mu pi : Measure (ℝ×JointAction 2)),x.2.bid≤d := by
    change ∀ᵐx ∂(pi.1 : Measure (LowBody.LowValue d×LowBody.LowValue d)).map
      (fun x=>(x.1.1,lowBroadcast x.2)),x.2.bid≤d
    apply (ae_map_iff
      (show Measurable (fun x : LowBody.LowValue d×LowBody.LowValue d=>(x.1.1,lowBroadcast x.2)) from
        measurable_fst.subtype_val.prodMk ((measurable_lowBroadcast d).comp measurable_snd)).aemeasurable
      (measurableSet_le ((measurable_bid 2).comp measurable_snd) measurable_const)).mpr
    exact ae_of_all _ (fun x=>x.2.property.2)
  have hm : Measurable (fun u : UserDraw 2=>collapseAction d U (u.1.2,u.2)):=
    (measurable_collapseAction d U).comp (measurable_fst.snd.prodMk measurable_snd)
  rw [populationJoint,Measure.add_prod,Measure.add_prod,
    Measure.prod_smul_left,Measure.prod_smul_left,Measure.prod_smul_left,
    Measure.map_add _ _ hm,Measure.map_add _ _ hm]
  simp only [Measure.map_smul]
  rw [collapse_low_population (lowJoint mu pi) d U hlo,lowJoint_bid_marginal,
    collapse_active_population PA d U hactive,collapse_upper_population PH hdU hupper]
  rw [smul_add,smul_smul,smul_smul]
  have hhalf : ENNReal.ofReal h*ENNReal.ofReal (1/2 : ℝ)=ENNReal.ofReal (h/2):=by
    rw [←ENNReal.ofReal_mul hh]
    congr 1
    ring
  rw [hhalf]
  exact (add_assoc _ _ _).symm

theorem population_shape {d U : ℝ} (hdU : d≤U) (s a h : ℝ)
    (mu : Measure (LowBody.LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=LowBody.LowValue d) mu) (PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hactive : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),x.2.bid≤U ∧ x.2.routeCount=2)
    (hupper : ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),U<x.2.bid ∧ x.2.routeCount=1) :
    ∀ᵐx ∂populationJoint s a h (lowJoint mu pi) PA PH,PopulationGame.actionShape U x.2 := by
  have hlow : ∀ᵐx ∂(lowJoint mu pi : Measure (ℝ×JointAction 2)),PopulationGame.actionShape U x.2 := by
    change ∀ᵐx ∂(pi.1 : Measure (LowBody.LowValue d×LowBody.LowValue d)).map
      (fun x=>(x.1.1,lowBroadcast x.2)),PopulationGame.actionShape U x.2
    have hS : MeasurableSet {x : ℝ×JointAction 2 | PopulationGame.actionShape U x.2} := by
      unfold PopulationGame.actionShape
      have hb : Measurable (fun x : ℝ×JointAction 2=>x.2.bid):=(measurable_bid 2).comp measurable_snd
      have hr : Measurable (fun x : ℝ×JointAction 2=>x.2.routeCount):=(measurable_routeCount 2).comp measurable_snd
      measurability
    apply (ae_map_iff
      (show Measurable (fun x : LowBody.LowValue d×LowBody.LowValue d=>(x.1.1,lowBroadcast x.2)) from
        measurable_fst.subtype_val.prodMk ((measurable_lowBroadcast d).comp measurable_snd)).aemeasurable hS).mpr
    exact ae_of_all _ (fun x=>Or.inl ⟨x.2.property.2.trans hdU,rfl⟩)
  have ha' : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),PopulationGame.actionShape U x.2:=
    hactive.mono (fun _ hx=>Or.inl hx)
  have hh' : ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),PopulationGame.actionShape U x.2:=
    hupper.mono (fun _ hx=>Or.inr hx)
  exact ae_add_measure_iff.mpr ⟨ae_add_measure_iff.mpr
    ⟨Measure.ae_smul_measure hlow (ENNReal.ofReal s),Measure.ae_smul_measure ha' (ENNReal.ofReal a)⟩,
      Measure.ae_smul_measure hh' (ENNReal.ofReal h)⟩

theorem native_population_row {m c : ℕ} {d U : ℝ} (hdU : d≤U)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (mu : Measure (LowBody.LowValue d)) [IsProbabilityMeasure mu]
    (pi : Law (A:=LowBody.LowValue d) mu) (PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hactive : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),d<x.2.bid ∧ x.2.bid≤U)
    (hupper : ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),U<x.2.bid)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η<1) :
    let P:=populationLaw s a h hs ha hh hsum (lowJoint mu pi) PA PH
    let Gamma:=PopulationGame.game m c P η hη0 hη1 U
    (userLaw Gamma).map (nativeRowRival Gamma d U)=
      LowBody.rivalLaw s a h (LowBody.realLowBidLaw pi.1 : Measure ℝ) := by
  dsimp only
  rw [userLaw,PopulationGame.joint_law]
  exact population_collapsed_row hdU s a h hh mu pi PA PH hactive hupper

theorem deleted_rival_rows_law {N c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma : FiniteGame (N+1) 2 c Seed) (i : Fin (N+1))
    (f : UserDraw 2→LowBody.RowRival) (hf : Measurable f) (nu : Measure LowBody.RowRival)
    (hrow : (userLaw Gamma).map f=nu) :
    (userProfileLaw Gamma).map (fun x (j : Fin N)=>f (x (i.succAbove j)))=
      Measure.pi (fun _ : Fin N=>nu) := by
  let delete : UserProfile (N+1) 2→(Fin N→UserDraw 2):=fun x j=>x (i.succAbove j)
  have hp : MeasurePreserving delete (userProfileLaw Gamma)
      (Measure.pi (fun _ : Fin N=>userLaw Gamma)) :=
    (measurePreserving_snd (μ:=userLaw Gamma)
      (ν:=Measure.pi (fun _ : Fin N=>userLaw Gamma))).comp
        (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1)=>userLaw Gamma) i)
  have hm : Measurable (fun x : Fin N→UserDraw 2=>fun j=>f (x j)):=
    measurable_pi_lambda _ (fun j=>hf.comp (measurable_pi_apply j))
  calc
    _=((userProfileLaw Gamma).map delete).map (fun x : Fin N→UserDraw 2=>fun j=>f (x j)) :=
      (Measure.map_map hm hp.measurable).symm
    _=_:=by rw [hp.map_eq,Measure.pi_map_pi (fun _=>hf.aemeasurable),hrow]

end FCAppendix.Affine.Hybrid
