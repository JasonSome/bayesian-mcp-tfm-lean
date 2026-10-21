import FCAppendix.Affine.Hybrid.PopulationGame
import FCAppendix.Affine.Hybrid.UpperLaw
import FCAppendix.Affine.Hybrid.ActiveNoisyRow
import FCAppendix.Game.JointMeasurability
import FCAppendix.Finite.ConditionalCountLaw

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Set Game Bayes Filter Topology
open Existence.Distributional

def activeBroadcast {L U : ℝ} (hL : 0 ≤ L) (b : ActiveBaseBid L U) : JointAction 2 :=
  ⟨b.1,hL.trans b.property.1,2,le_rfl⟩

theorem measurable_activeBroadcast {L U : ℝ} (hL : 0 ≤ L) :
    Measurable (activeBroadcast (U:=U) hL) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction,MeasurableSpace.comap_comp]
  exact (measurable_subtype_coe.prodMk measurable_const).comap_le

def activeJoint {vlo vhi L U : ℝ} (hL : 0 ≤ L)
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu]
    (pi : Law (A:=ActiveBaseBid L U) mu) : ProbabilityMeasure (ℝ×JointAction 2) :=
  pi.1.map (measurable_fst.subtype_val.prodMk ((measurable_activeBroadcast hL).comp measurable_snd)).aemeasurable

theorem activeJoint_value_marginal {vlo vhi L U : ℝ} (hL : 0 ≤ L)
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu]
    (pi : Law (A:=ActiveBaseBid L U) mu) :
    (activeJoint hL mu pi : Measure (ℝ×JointAction 2)).map Prod.fst=
      mu.map Subtype.val := by
  change ((pi.1 : Measure (ActiveValue vlo vhi×ActiveBaseBid L U)).map
    (fun x=>(x.1.1,activeBroadcast hL x.2))).map Prod.fst=_
  rw [Measure.map_map measurable_fst (by exact measurable_fst.subtype_val.prodMk ((measurable_activeBroadcast hL).comp measurable_snd))]
  calc
    _=((pi.1 : Measure (ActiveValue vlo vhi×ActiveBaseBid L U)).map Prod.fst).map
        Subtype.val := (Measure.map_map measurable_subtype_coe measurable_fst).symm
    _=mu.map Subtype.val := by rw [pi.2]

theorem activeJoint_bid_marginal {vlo vhi L U : ℝ} (hL : 0 ≤ L)
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu]
    (pi : Law (A:=ActiveBaseBid L U) mu) :
    (activeJoint hL mu pi : Measure (ℝ×JointAction 2)).map (fun x=>x.2.bid)=
      ((pi.1 : Measure (ActiveValue vlo vhi×ActiveBaseBid L U)).map Prod.snd).map
        Subtype.val := by
  change ((pi.1 : Measure (ActiveValue vlo vhi×ActiveBaseBid L U)).map
    (fun x=>(x.1.1,activeBroadcast hL x.2))).map (fun x=>x.2.bid)=_
  rw [Measure.map_map (by exact (measurable_bid 2).comp measurable_snd)
    (by exact measurable_fst.subtype_val.prodMk ((measurable_activeBroadcast hL).comp measurable_snd)),
    Measure.map_map measurable_subtype_coe measurable_snd]
  rfl

theorem activeJoint_support {vlo vhi L U : ℝ} (hL : 0 ≤ L)
    (mu : Measure (ActiveValue vlo vhi)) [IsProbabilityMeasure mu]
    (pi : Law (A:=ActiveBaseBid L U) mu) :
    ∀ᵐx ∂(activeJoint hL mu pi : Measure (ℝ×JointAction 2)),
      x.1∈ Icc vlo vhi ∧ x.2.bid∈ Icc L U ∧ x.2.routeCount=2 := by
  apply (ae_map_iff
    (measurable_fst.subtype_val.prodMk
      ((measurable_activeBroadcast hL).comp measurable_snd)).aemeasurable ?_).mpr
  · exact ae_of_all _ (fun x=>⟨x.1.property,x.2.property,rfl⟩)
  · exact (measurable_fst measurableSet_Icc).inter
      ((((measurable_bid 2).comp measurable_snd) measurableSet_Icc).inter
        (measurableSet_eq_fun ((measurable_routeCount 2).comp measurable_snd) measurable_const))

theorem low_bound_pos {d : ℝ} (mu : Measure (LowBody.LowValue d))
    [IsProbabilityMeasure mu] (hpos : ∀ᵐv ∂mu,0<v.1) : 0<d := by
  obtain ⟨v,hv⟩ := hpos.exists
  exact hv.trans_le v.property.2

def originalValueLaw (s a h : ℝ) (FL FA FH : Measure ℝ) : Measure ℝ :=
  ENNReal.ofReal s • FL+ENNReal.ofReal a • FA+ENNReal.ofReal h • FH

theorem original_population_marginal (s a h : ℝ)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (FL FA FH : Measure ℝ)
    (hL : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=FL)
    (hA : (PA : Measure (ℝ×JointAction 2)).map Prod.fst=FA)
    (hH : (PH : Measure (ℝ×JointAction 2)).map Prod.fst=FH) :
    (populationJoint s a h PL PA PH).map Prod.fst=originalValueLaw s a h FL FA FH := by
  rw [populationJoint,Measure.map_add _ _ measurable_fst,
    Measure.map_add _ _ measurable_fst]
  simp only [Measure.map_smul,hL,hA,hH,originalValueLaw]

theorem population_game_original_marginal (m c : ℕ) (s a h : ℝ)
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2)) (FL FA FH : Measure ℝ)
    (hL : (PL : Measure (ℝ×JointAction 2)).map Prod.fst=FL)
    (hA : (PA : Measure (ℝ×JointAction 2)).map Prod.fst=FA)
    (hH : (PH : Measure (ℝ×JointAction 2)).map Prod.fst=FH)
    (eta : ℝ) (he0 : 0 ≤ eta) (he1 : eta<1) (U : ℝ) :
    let P:=populationLaw s a h hs ha hh hsum PL PA PH
    let G:=PopulationGame.game m c P eta he0 he1 U
    G.F=originalValueLaw s a h FL FA FH ∧
      G.F⊗ₘG.σ=populationJoint s a h PL PA PH := by
  dsimp only
  constructor
  · exact original_population_marginal s a h PL PA PH FL FA FH hL hA hH
  · exact PopulationGame.joint_law _ _ _ _ _ _ _

theorem original_population_mixture_ae (s a h : ℝ)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2)) (P : ℝ×JointAction 2→ Prop)
    (hL : ∀ᵐx ∂(PL : Measure (ℝ×JointAction 2)),P x)
    (hA : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),P x)
    (hH : ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),P x) :
    ∀ᵐx ∂populationJoint s a h PL PA PH,P x := by
  rw [populationJoint,ae_add_measure_iff,ae_add_measure_iff]
  exact ⟨⟨Measure.ae_smul_measure hL _,Measure.ae_smul_measure hA _⟩,
    Measure.ae_smul_measure hH _⟩

theorem disintegrate_joint_IC {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : FiniteGame m 2 c Seed)
    (hIC : ∀ i,∀ᵐx ∂G.F⊗ₘG.σ,(problem G i).BestResponse x.1 x.2) :
    UsersOptimal G := by
  intro i
  exact Measure.ae_ae_of_ae_compProd (hIC i)

theorem original_population_mixture_IC {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : FiniteGame m 2 c Seed) (s a h : ℝ)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hjoint : G.F⊗ₘG.σ=populationJoint s a h PL PA PH)
    (hL : ∀ i,∀ᵐx ∂(PL : Measure (ℝ×JointAction 2)),(problem G i).BestResponse x.1 x.2)
    (hA : ∀ i,∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),(problem G i).BestResponse x.1 x.2)
    (hH : ∀ i,∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),(problem G i).BestResponse x.1 x.2) :
    UsersOptimal G := by
  apply disintegrate_joint_IC G
  intro i
  rw [hjoint]
  exact original_population_mixture_ae s a h PL PA PH _ (hL i) (hA i) (hH i)

theorem usersOptimal_common_conull {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : FiniteGame m 2 c Seed) (hG : UsersOptimal G) :
    ∀ᵐv ∂G.F,∀ᵐact ∂G.σ v,∀ i : Fin m,∀ dev : JointAction 2,
      (problem G i).payoff v dev ≤ (problem G i).payoff v act := by
  have hv : ∀ᵐv ∂G.F,∀ i : Fin m,∀ᵐact ∂G.σ v,(problem G i).BestResponse v act :=
    ae_all_iff.mpr hG
  filter_upwards [hv] with v hv
  have ha : ∀ᵐact ∂G.σ v,∀ i : Fin m,(problem G i).BestResponse v act :=
    ae_all_iff.mpr hv
  exact ha.mono (fun act h i dev=>h i dev)

theorem family_common_conull {M C : ℕ→ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (G : ∀ k,FiniteGame (M k) 2 (C k) Seed) (F : Measure ℝ)
    (hF : ∀ k,(G k).F=F) (hIC : ∀ k,UsersOptimal (G k)) :
    ∀ᵐv ∂F,∀ k,∀ᵐact ∂(G k).σ v,∀ i : Fin (M k),∀ dev : JointAction 2,
      (problem (G k) i).payoff v dev ≤ (problem (G k) i).payoff v act := by
  apply ae_all_iff.mpr
  intro k
  simpa only [hF k] using usersOptimal_common_conull (G k) (hIC k)

end FCAppendix.Affine.Hybrid.Native02
