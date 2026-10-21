import FCAppendix.AppendixRepair.LowGroup
import FCAppendix.AppendixRepair.TailConditioning

noncomputable section
namespace FCAppendix.Appendix08.Tail
open MeasureTheory ProbabilityTheory Set Game Bayes Filter Topology Classical
open Information Affine
open scoped BigOperators

theorem coefficient_two_information {m : ℕ} (kind : Fin m→ Fin 3)
    (x : Realization m 2) {d R P U Rm : ℝ}
    (hdR : d< R) (hRP : R≤ P) (hP : P<1) (hU : 1≤ U) (hRm : U< Rm)
    (hboxes : ∀i,
      (kind i=0→(x.action i).bid≤ d) ∧
      (kind i=1→(x.action i).bid∈Icc 1 U) ∧
      (kind i=2→(x.action i).bid∈Icc R P ∨ Rm≤(x.action i).bid))
    (hr : Routes kind x) (c : ℕ) (j : Fin 2) :
    Correct (intervalClassifier d 1 U) kind x ∧
      part (intervalClassifier d 1 U) 0 (observe x j)=
        part (intervalClassifier d 1 U) 0 (observe x (other j)) ∧
      otherResidual (intervalClassifier d 1 U) c (observe x j)=
        min (countKind kind 0) (c-countKind kind 1-privateAt kind x (other j)) := by
  have hc : Correct (intervalClassifier d 1 U) kind x := by
    apply intervalClassifier_correct kind x hdR hRP hP hU
    intro i
    refine ⟨(hboxes i).1,(hboxes i).2.1,?_⟩
    intro hi
    rcases (hboxes i).2.2 hi with hp|hh
    · exact Or.inl hp
    · exact upperFloor_subset_privateUnion hRm hh
  exact ⟨hc,(common_broadcast_parts _ kind x hc hr j (other j)).1,
    (residuals_correct _ c kind x hc hr j).2⟩

theorem coefficient_one_information {m : ℕ} (kind : Fin m→ Fin 3)
    (x : Realization m 2) {d L U R : ℝ}
    (hdL : d< L) (hLU : L≤ U) (hUR : U< R)
    (hboxes : ∀i,
      (kind i=0→(x.action i).bid≤ d) ∧
      (kind i=1→(x.action i).bid∈Icc L U) ∧
      (kind i=2→ R≤(x.action i).bid))
    (hr : Routes kind x) (c : ℕ) (j : Fin 2) :
    Correct (intervalClassifier d L U) kind x ∧
      otherResidual (intervalClassifier d L U) c (observe x j)=
        min (countKind kind 0) (c-countKind kind 1-privateAt kind x (other j)) := by
  have hc : Correct (intervalClassifier d L U) kind x := by
    intro i
    rcases hk : kind i with ⟨k,hklt⟩
    interval_cases k
    · exact intervalClassifier_low ((hboxes i).1 (by simp [hk]))
    · exact intervalClassifier_active hdL ((hboxes i).2.1 (by simp [hk]))
    · have hb := (hboxes i).2.2 (by simp [hk])
      have hbd : ¬(x.action i).bid≤ d := not_le.mpr
        (((hdL.trans_le hLU).trans hUR).trans_le hb)
      have hba : (x.action i).bid∉Icc L U := by
        intro hh
        exact not_le_of_gt (hUR.trans_le hb) hh.2
      simp only [intervalClassifier, if_neg hbd, if_neg hba]
      rfl
  exact ⟨hc,(residuals_correct _ c kind x hc hr j).2⟩

def recodeBid (C : Classifier) (bA bP : ℝ) (b : ℝ) : ℝ :=
  if C.label b=0 then b else if C.label b=1 then bA else bP

theorem measurable_recodeBid (C : Classifier) (bA bP : ℝ) :
    Measurable (recodeBid C bA bP) := by
  exact Measurable.ite
    (measurableSet_eq_fun C.measurable_label measurable_const) measurable_id
    (Measurable.ite (measurableSet_eq_fun C.measurable_label measurable_const)
      measurable_const measurable_const)

theorem recodeBid_nonneg (C : Classifier) {bA bP b : ℝ}
    (hA : 0≤ bA) (hP : 0≤ bP) (hb : 0≤ b) :
    0≤ recodeBid C bA bP b := by
  unfold recodeBid
  split_ifs <;> assumption

def recodeAction (C : Classifier) (bA bP : ℝ) (hA : 0≤ bA) (hP : 0≤ bP)
    (a : JointAction 2) : JointAction 2 :=
  ⟨recodeBid C bA bP a.bid,recodeBid_nonneg C hA hP a.bid_nonneg,
    a.routeCount,a.routeCount_le⟩

theorem measurable_recodeAction (C : Classifier) (bA bP : ℝ)
    (hA : 0≤ bA) (hP : 0≤ bP) : Measurable (recodeAction C bA bP hA hP) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction,MeasurableSpace.comap_comp]
  exact (((measurable_recodeBid C bA bP).comp (measurable_bid 2)).prodMk
    (measurable_routeCount 2)).comap_le

def recodeJoint (C : Classifier) (bA bP : ℝ) (hA : 0≤ bA) (hP : 0≤ bP)
    (z : ℝ×JointAction 2) : ℝ×JointAction 2 :=
  (z.1,recodeAction C bA bP hA hP z.2)

def recodeDraw (C : Classifier) (bA bP : ℝ) (hA : 0≤ bA) (hP : 0≤ bP)
    (z : UserDraw 2) : UserDraw 2 :=
  (recodeJoint C bA bP hA hP z.1,z.2)

theorem measurable_recodeJoint (C : Classifier) (bA bP : ℝ)
    (hA : 0≤ bA) (hP : 0≤ bP) : Measurable (recodeJoint C bA bP hA hP) :=
  measurable_fst.prodMk ((measurable_recodeAction C bA bP hA hP).comp measurable_snd)

theorem measurable_recodeDraw (C : Classifier) (bA bP : ℝ)
    (hA : 0≤ bA) (hP : 0≤ bP) : Measurable (recodeDraw C bA bP hA hP) :=
  ((measurable_recodeJoint C bA bP hA hP).comp measurable_fst).prodMk measurable_snd

def recodePopulation (C : Classifier) (bA bP : ℝ) (hA : 0≤ bA) (hP : 0≤ bP)
    (P : ProbabilityMeasure (ℝ×JointAction 2)) : ProbabilityMeasure (ℝ×JointAction 2) :=
  P.map (measurable_recodeJoint C bA bP hA hP).aemeasurable

def referenceActiveBid (d : ℝ) : ℝ := 2*(d+1)
def referencePrivateBid (d : ℝ) : ℝ := referenceActiveBid d+1

theorem referenceActiveBid_nonneg {d : ℝ} (hd : 0≤ d) : 0≤ referenceActiveBid d := by
  unfold referenceActiveBid
  positivity

theorem referencePrivateBid_nonneg {d : ℝ} (hd : 0≤ d) : 0≤ referencePrivateBid d := by
  unfold referencePrivateBid
  exact add_nonneg (referenceActiveBid_nonneg hd) zero_le_one

theorem reference_bid_guards {d eta : ℝ} (hd : 0≤ d) (he : 0≤ eta) :
    d≤ referenceActiveBid d ∧
      d<((1+eta)/2)*referenceActiveBid d ∧
      referenceActiveBid d< referencePrivateBid d := by
  have hh := mul_nonneg he (show 0≤ d+1 by linarith)
  dsimp [referenceActiveBid,referencePrivateBid]
  constructor
  · linarith
  constructor
  · nlinarith
  · linarith

theorem recoded_active_support (C : Classifier) (d eta : ℝ) (hd : 0≤ d) (he : 0≤ eta)
    (PA : ProbabilityMeasure (ℝ×JointAction 2))
    (hclass : ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)),
      C.label x.2.bid=1 ∧ x.2.routeCount=2) :
    ∀ᵐx ∂(recodePopulation C (referenceActiveBid d) (referencePrivateBid d)
      (referenceActiveBid_nonneg hd) (referencePrivateBid_nonneg hd) PA :
        Measure (ℝ×JointAction 2)),
      d<((1+eta)/2)*x.2.bid ∧ x.2.bid≤ referenceActiveBid d ∧ x.2.routeCount=2 := by
  let f := recodeJoint C (referenceActiveBid d) (referencePrivateBid d)
    (referenceActiveBid_nonneg hd) (referencePrivateBid_nonneg hd)
  have hf : Measurable f := measurable_recodeJoint _ _ _ _ _
  change ∀ᵐx ∂(PA : Measure (ℝ×JointAction 2)).map f,_
  have hb : Measurable (fun x : ℝ×JointAction 2=>x.2.bid) :=
    (measurable_bid 2).comp measurable_snd
  have hk : Measurable (fun x : ℝ×JointAction 2=>x.2.routeCount) :=
    (measurable_routeCount 2).comp measurable_snd
  apply (ae_map_iff hf.aemeasurable
    ((measurableSet_lt measurable_const (measurable_const.mul hb)).inter
      ((measurableSet_le hb measurable_const).inter
        (measurableSet_eq_fun hk measurable_const)))).mpr
  filter_upwards [hclass] with x hx
  change d<((1+eta)/2)*(f x).2.bid ∧ (f x).2.bid≤referenceActiveBid d ∧ (f x).2.routeCount=2
  simpa [f,recodeJoint,recodeAction,recodeBid,hx.1] using
    (show d<((1+eta)/2)*referenceActiveBid d ∧
      referenceActiveBid d≤ referenceActiveBid d ∧ x.2.routeCount=2 from
      ⟨(reference_bid_guards hd he).2.1,le_rfl,hx.2⟩)

theorem recoded_private_support (C : Classifier) (d : ℝ) (hd : 0≤ d)
    (PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hclass : ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)),
      C.label x.2.bid=2 ∧ x.2.routeCount=1) :
    ∀ᵐx ∂(recodePopulation C (referenceActiveBid d) (referencePrivateBid d)
      (referenceActiveBid_nonneg hd) (referencePrivateBid_nonneg hd) PH :
        Measure (ℝ×JointAction 2)),
      referenceActiveBid d< x.2.bid ∧ x.2.routeCount=1 := by
  let f := recodeJoint C (referenceActiveBid d) (referencePrivateBid d)
    (referenceActiveBid_nonneg hd) (referencePrivateBid_nonneg hd)
  have hf : Measurable f := measurable_recodeJoint _ _ _ _ _
  change ∀ᵐx ∂(PH : Measure (ℝ×JointAction 2)).map f,_
  have hb : Measurable (fun x : ℝ×JointAction 2=>x.2.bid) :=
    (measurable_bid 2).comp measurable_snd
  have hk : Measurable (fun x : ℝ×JointAction 2=>x.2.routeCount) :=
    (measurable_routeCount 2).comp measurable_snd
  apply (ae_map_iff hf.aemeasurable
    ((measurableSet_lt measurable_const hb).inter
      (measurableSet_eq_fun hk measurable_const))).mpr
  filter_upwards [hclass] with x hx
  change referenceActiveBid d<(f x).2.bid ∧ (f x).2.routeCount=1
  simpa [f,recodeJoint,recodeAction,recodeBid,hx.1] using
    (show referenceActiveBid d< referencePrivateBid d ∧ x.2.routeCount=1 from
      ⟨by unfold referencePrivateBid;linarith,hx.2⟩)

theorem recodeJoint_eq_of_low (C : Classifier) (bA bP : ℝ)
    (hA : 0≤ bA) (hP : 0≤ bP) (z : ℝ×JointAction 2)
    (hz : C.label z.2.bid=0) : recodeJoint C bA bP hA hP z=z := by
  rcases z with ⟨v,⟨b,hb,k,hk⟩⟩
  simp only [recodeJoint,recodeAction,recodeBid,if_pos hz]

theorem recode_low_population (C : Classifier) (bA bP : ℝ)
    (hA : 0≤ bA) (hP : 0≤ bP) (PL : ProbabilityMeasure (ℝ×JointAction 2))
    (hlow : ∀ᵐz ∂(PL : Measure (ℝ×JointAction 2)),C.label z.2.bid=0) :
    (PL : Measure (ℝ×JointAction 2)).map (recodeJoint C bA bP hA hP)=PL := by
  calc
    _=(PL : Measure (ℝ×JointAction 2)).map id := by
      apply Measure.map_congr
      filter_upwards [hlow] with z hz
      exact recodeJoint_eq_of_low C bA bP hA hP z hz
    _=PL := by simp only [Measure.map_id]

theorem recode_populationJoint (C : Classifier) (bA bP : ℝ)
    (hA : 0≤ bA) (hP : 0≤ bP) (s a h : ℝ)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hlow : ∀ᵐz ∂(PL : Measure (ℝ×JointAction 2)),C.label z.2.bid=0) :
    (Hybrid.populationJoint s a h PL PA PH).map (recodeJoint C bA bP hA hP)=
      Hybrid.populationJoint s a h PL
        (recodePopulation C bA bP hA hP PA) (recodePopulation C bA bP hA hP PH) := by
  rw [Hybrid.populationJoint,Hybrid.populationJoint,
    Measure.map_add _ _ (measurable_recodeJoint C bA bP hA hP),
    Measure.map_add _ _ (measurable_recodeJoint C bA bP hA hP)]
  simp only [Measure.map_smul,recode_low_population C bA bP hA hP PL hlow]
  rfl

def recodeLocalList {m : ℕ} (C : Classifier) (bA bP : ℝ)
    (L : LocalList m) : LocalList m :=
  fun i=>(L i).map (recodeBid C bA bP)

def recodeSample {m : ℕ} {Seed : Type*} (C : Classifier) (bA bP : ℝ)
    (hA : 0≤ bA) (hP : 0≤ bP) (w : Sample m 2 Seed) : Sample m 2 Seed :=
  ((fun i=>recodeDraw C bA bP hA hP (w.1.1 i),w.1.2),w.2)

theorem recodeSample_preserves_value {m : ℕ} {Seed : Type*}
    (C : Classifier) (bA bP : ℝ) (hA : 0≤ bA) (hP : 0≤ bP)
    (w : Sample m 2 Seed) (i : Fin m) :
    ((recodeSample C bA bP hA hP w).1.1 i).1.1=(w.1.1 i).1.1 := rfl

theorem recodeSample_preserves_routes {m : ℕ} {Seed : Type*}
    (C : Classifier) (bA bP : ℝ) (hA : 0≤ bA) (hP : 0≤ bP)
    (w : Sample m 2 Seed) (i : Fin m) :
    ((recodeSample C bA bP hA hP w).1.1 i).1.2.routeCount=
      (w.1.1 i).1.2.routeCount ∧
    ((recodeSample C bA bP hA hP w).1.1 i).2=(w.1.1 i).2 := ⟨rfl,rfl⟩

theorem measurePreserving_recodeSample {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma Reference : FiniteGame m 2 c Seed) (C : Classifier)
    (bA bP : ℝ) (hA : 0≤ bA) (hP : 0≤ bP)
    (hjoint : (Gamma.F⊗ₘGamma.σ).map (recodeJoint C bA bP hA hP)=
      Reference.F⊗ₘReference.σ)
    (hseed : Gamma.seedLaw=Reference.seedLaw) :
    MeasurePreserving (recodeSample (m:=m) (Seed:=Seed) C bA bP hA hP)
      (sampleLaw Gamma) (sampleLaw Reference) := by
  have hdraw : MeasurePreserving (recodeDraw C bA bP hA hP)
      (userLaw Gamma) (userLaw Reference) := by
    refine ⟨measurable_recodeDraw C bA bP hA hP,?_⟩
    change ((Gamma.F⊗ₘGamma.σ).prod (permLaw 2)).map
      (Prod.map (recodeJoint C bA bP hA hP) id)=_
    rw [←Measure.map_prod_map _ _ (measurable_recodeJoint C bA bP hA hP)
      measurable_id,hjoint,Measure.map_id]
    rfl
  have hprofile := measurePreserving_pi (fun _ : Fin m=>userLaw Gamma)
    (fun _ : Fin m=>userLaw Reference) (fun _=>hdraw)
  have hseeds : MeasurePreserving (id : (Fin 2→ Seed)→(Fin 2→ Seed))
      (Measure.pi (fun _ : Fin 2=>Gamma.seedLaw))
      (Measure.pi (fun _ : Fin 2=>Reference.seedLaw)) := by
    rw [hseed]
    exact MeasurePreserving.id _
  exact (hprofile.prod hseeds).prod (MeasurePreserving.id (permLaw 2))

theorem observe_deviated_recode {m : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (C : Classifier) (bA bP : ℝ) (hA : 0≤ bA) (hP : 0≤ bP)
    (i : Fin m) (a : JointAction 2) (ha : C.label a.bid=0)
    (w : Sample m 2 Seed) (j : Fin 2) :
    observe (deviated i a (recodeSample C bA bP hA hP w)) j=
      recodeLocalList C bA bP (observe (deviated i a w) j) := by
  funext k
  by_cases hk:k=i
  · subst k
    simp only [observe,deviated_recipients_self,deviated_bid_self,
      recodeLocalList,recodeSample]
    split_ifs <;> simp [recodeBid,ha]
  · simp only [observe,deviated_recipients_other i k hk,deviated_bid_other i k hk,
      recodeLocalList,recodeSample,recodeDraw,recodeJoint,recodeAction]
    split_ifs <;> rfl

def tail_low_copy_of_local_rule {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma Reference : FiniteGame m 2 c Seed) (C : Classifier) (d bA bP : ℝ)
    (hA : 0≤ bA) (hP : 0≤ bP)
    (hlow : ∀b : ℝ,0≤ b→ b≤ d→ C.label b=0)
    (hjoint : (Gamma.F⊗ₘGamma.σ).map (recodeJoint C bA bP hA hP)=
      Reference.F⊗ₘReference.σ)
    (hseed : Gamma.seedLaw=Reference.seedLaw)
    (hcopy : ∀j (L : LocalList m) s i b,L i=some b→ b≤ d→
      (i∈(Gamma.policy j L s).val ↔
        i∈(Reference.policy j (recodeLocalList C bA bP L) s).val)) :
    LowAllocationReproduction Gamma Reference d := by
  refine ⟨recodeSample C bA bP hA hP,
    measurePreserving_recodeSample Gamma Reference C bA bP hA hP hjoint hseed,?_⟩
  intro i
  apply ae_of_all
  intro w a ha j
  have hobs := observe_deviated_recode C bA bP hA hP i a
    (hlow a.bid a.bid_nonneg ha) w j
  change (i∈(Gamma.policy j (observe (deviated i a w) j) (w.1.2 j)).val) ↔
    (i∈(Reference.policy j
      (observe (deviated i a (recodeSample C bA bP hA hP w)) j)
      (w.1.2 j)).val)
  rw [hobs]
  by_cases hrec:j∈firstK w.2 a.routeCount
  · apply hcopy j _ _ i a.bid _ ha
    simp [observe,deviated_recipients_self,deviated_bid_self,hrec]
  · have hn : observe (deviated i a w) j i=none := by
      simp [observe,deviated_recipients_self,hrec]
    have hn' : recodeLocalList C bA bP (observe (deviated i a w) j) i=none := by
      simp [recodeLocalList,hn]
    constructor
    · intro hi
      exact ((Gamma.policy j _ _).property.2 i hi hn).elim
    · intro hi
      exact ((Reference.policy j _ _).property.2 i hi hn').elim

theorem low_rule_of_selection_union {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma Reference : FiniteGame m 2 c Seed) (C : Classifier) (d bA bP : ℝ)
    (higher : Fin 2→ LocalList m→ Seed→ Finset (Fin m))
    (hhigher : ∀j L s i b,L i=some b→ b≤ d→ i∉higher j L s)
    (hdefinition : ∀j L s,
      (Gamma.policy j L s).val=higher j L s ∪
        ((Reference.policy j (recodeLocalList C bA bP L) s).val.filter
          (fun i=>∃b,L i=some b ∧ b≤ d))) :
    ∀j (L : LocalList m) s i b,L i=some b→ b≤ d→
      (i∈(Gamma.policy j L s).val ↔
        i∈(Reference.policy j (recodeLocalList C bA bP L) s).val) := by
  intro j L s i b hib hbd
  rw [hdefinition j L s]
  have hn := hhigher j L s i b hib hbd
  simp [hn,show ∃b,L i=some b ∧ b≤ d from ⟨b,hib,hbd⟩]

def tail_low_copy_of_constructed_policy {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Gamma Reference : FiniteGame m 2 c Seed) (C : Classifier) (d bA bP : ℝ)
    (hA : 0≤ bA) (hP : 0≤ bP)
    (hlow : ∀b : ℝ,0≤ b→ b≤ d→ C.label b=0)
    (hjoint : (Gamma.F⊗ₘGamma.σ).map (recodeJoint C bA bP hA hP)=
      Reference.F⊗ₘReference.σ)
    (hseed : Gamma.seedLaw=Reference.seedLaw)
    (higher : Fin 2→ LocalList m→ Seed→ Finset (Fin m))
    (hhigher : ∀j L s i b,L i=some b→ b≤ d→ i∉higher j L s)
    (hdefinition : ∀j L s,
      (Gamma.policy j L s).val=higher j L s ∪
        ((Reference.policy j (recodeLocalList C bA bP L) s).val.filter
          (fun i=>∃b,L i=some b ∧ b≤ d))) :
    LowCountReproduction Gamma Reference d :=
  (tail_low_copy_of_local_rule Gamma Reference C d bA bP hA hP hlow hjoint hseed
    (low_rule_of_selection_union Gamma Reference C d bA bP higher hhigher hdefinition)).toCounts

end FCAppendix.Appendix08.Tail
