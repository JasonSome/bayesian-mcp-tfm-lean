import FCAppendix.Affine.Tail04.ClosedUpperPriority
import FCAppendix.Probability.FinitePushforward

noncomputable section
namespace FCAppendix.Affine.Tail04.ClosedUpperPriority
open MeasureTheory ProbabilityTheory Set Game Bayes Classical
open scoped BigOperators

def eraseList {m : ℕ} (R : ℝ) (L : LocalList m) : LocalList m :=
  fun i => (L i).map (fun b => min b R)

theorem encode_erased_tag {m : ℕ} (R : ℝ) (L : LocalList m) (i : Fin m) :
    TaggedLocal.tag R R (encodeList R (eraseList R L) i)=
      TaggedLocal.tag R R (encodeList R L i) := by
  cases he : L i with
  | none => simp [encodeList,eraseList,he,TaggedLocal.tag]
  | some b =>
    by_cases hb : b< R
    · simp [encodeList,eraseList,he,min_eq_left hb.le,encodeBid_lower R b hb]
    · have hbR : R≤ b := le_of_not_gt hb
      have hb1 : ¬b+1≤ R := by linarith
      have hR1 : ¬R+1≤ R := by linarith
      simp [encodeList,eraseList,he,min_eq_right hbR,encodeBid_upper R b hbR,
        encodeBid_upper R R le_rfl,TaggedLocal.tag,hb1,hR1]

theorem encode_erased_broadcastPart {m : ℕ} (R : ℝ) (L : LocalList m) :
    Hybrid.broadcastPart R (encodeList R (eraseList R L))=
      Hybrid.broadcastPart R (encodeList R L) := by
  funext i
  cases he : L i with
  | none => simp [Hybrid.broadcastPart,TaggedLocal.lowList,encodeList,eraseList,he]
  | some b =>
    by_cases hb : b< R
    · simp [Hybrid.broadcastPart,TaggedLocal.lowList,encodeList,eraseList,he,
        min_eq_left hb.le,encodeBid_lower R b hb]
    · have hbR : R≤ b := le_of_not_gt hb
      have hb1 : ¬b+1≤ R := by linarith
      have hR1 : ¬R+1≤ R := by linarith
      simp [Hybrid.broadcastPart,TaggedLocal.lowList,encodeList,eraseList,he,
        min_eq_right hbR,encodeBid_upper R b hbR,encodeBid_upper R R le_rfl,
        TaggedLocal.tag,hb1,hR1]

theorem encode_erased_context {m : ℕ} (R : ℝ) (j : Fin 2) (L : LocalList m) :
    Hybrid.observedContext R j (encodeList R (eraseList R L))=
      Hybrid.observedContext R j (encodeList R L) := by
  have hc (k : Fin 4) :
      TaggedLocal.localCount R R (encodeList R (eraseList R L)) k=
        TaggedLocal.localCount R R (encodeList R L) k := by
    unfold TaggedLocal.localCount
    simp_rw [encode_erased_tag]
  simp only [Hybrid.observedContext,hc,encode_erased_broadcastPart]

section LowerPolicy
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  (C : Hybrid.ContextPolicy m c Seed)

theorem lower_selection_erase_iff (R : ℝ) (j : Fin 2) (L : LocalList m)
    (s : Seed) (i : Fin m) (b : ℝ) (hb : b< R) (hi : L i=some b) :
    i∈selection C R j (eraseList R L) s ↔ i∈selection C R j L s := by
  have hiE : encodeList R L i=some b := by
    simp [encodeList,hi,encodeBid_lower R b hb]
  have hiEE : encodeList R (eraseList R L) i=some b := by
    simp [encodeList,eraseList,hi,min_eq_left hb.le,encodeBid_lower R b hb]
  have hp : Hybrid.broadcastPart R (encodeList R L) i≠none := by
    rw [Hybrid.broadcastPart_some _ i hiE hb.le]
    simp
  have hpE : Hybrid.broadcastPart R (encodeList R (eraseList R L)) i≠none := by
    rw [Hybrid.broadcastPart_some _ i hiEE hb.le]
    simp
  change i∈C.selection R j (encodeList R (eraseList R L)) s ↔
    i∈C.selection R j (encodeList R L) s
  rw [C.factors R j _ s i hpE,C.factors R j _ s i hp,encode_erased_context]

end LowerPolicy

def eraseAction (R : ℝ) (hR : 0≤ R) (a : JointAction 2) : JointAction 2 :=
  ⟨min a.bid R,le_min a.bid_nonneg hR,a.routeCount,a.routeCount_le⟩

theorem measurable_eraseAction (R : ℝ) (hR : 0≤ R) :
    Measurable (eraseAction R hR) := by
  apply Measurable.of_comap_le
  rw [instMeasurableSpaceJointAction,MeasurableSpace.comap_comp]
  exact (((measurable_bid 2).min measurable_const).prodMk
    (measurable_routeCount 2)).comap_le

def eraseValueAction (R : ℝ) (hR : 0≤ R) (x : ℝ×JointAction 2) : ℝ×JointAction 2 :=
  (0,eraseAction R hR x.2)

theorem measurable_eraseValueAction (R : ℝ) (hR : 0≤ R) :
    Measurable (eraseValueAction R hR) :=
  measurable_const.prodMk ((measurable_eraseAction R hR).comp measurable_snd)

def eraseUser (R : ℝ) (hR : 0≤ R) : UserDraw 2 → UserDraw 2 :=
  Prod.map (eraseValueAction R hR) id

theorem measurable_eraseUser (R : ℝ) (hR : 0≤ R) : Measurable (eraseUser R hR) :=
  (measurable_eraseValueAction R hR).prodMap measurable_id

def eraseProfile {m : ℕ} (R : ℝ) (hR : 0≤ R) (d : UserProfile m 2) : UserProfile m 2 :=
  fun i => eraseUser R hR (d i)

theorem measurable_eraseProfile {m : ℕ} (R : ℝ) (hR : 0≤ R) :
    Measurable (eraseProfile (m:=m) R hR) :=
  measurable_pi_lambda _ (fun i => (measurable_eraseUser R hR).comp (measurable_pi_apply i))

def eraseBackground {m : ℕ} {Seed : Type*} (R : ℝ) (hR : 0≤ R) :
    Background m 2 Seed → Background m 2 Seed :=
  Prod.map (eraseProfile R hR) id

theorem measurable_eraseBackground {m : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (R : ℝ) (hR : 0≤ R) : Measurable (eraseBackground (m:=m) (Seed:=Seed) R hR) :=
  (measurable_eraseProfile R hR).prodMap measurable_id

def eraseSample {m : ℕ} {Seed : Type*} (R : ℝ) (hR : 0≤ R) :
    Sample m 2 Seed → Sample m 2 Seed :=
  Prod.map (eraseBackground R hR) id

theorem measurable_eraseSample {m : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (R : ℝ) (hR : 0≤ R) : Measurable (eraseSample (m:=m) (Seed:=Seed) R hR) :=
  (measurable_eraseBackground R hR).prodMap measurable_id

theorem observe_deviated_erase {m : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (R : ℝ) (hR : 0≤ R) (i : Fin m) (a : JointAction 2) (ha : a.bid< R)
    (ω : Sample m 2 Seed) (j : Fin 2) :
    observe (deviated i a (eraseSample R hR ω)) j=
      eraseList R (observe (deviated i a ω) j) := by
  funext k
  by_cases hk : k=i
  · subst k
    simp only [observe,deviated_recipients_self,deviated_bid_self,
      eraseList,eraseSample]
    change (if j∈firstK ω.2 a.routeCount then some a.bid else none)=
      (if j∈firstK ω.2 a.routeCount then some a.bid else none).map (fun b => min b R)
    split_ifs <;> simp [min_eq_left ha.le]
  · simp only [observe,deviated_recipients_other i k hk,deviated_bid_other i k hk,
      eraseList,eraseSample,eraseBackground]
    change (if j∈firstK (ω.1.1 k).2 (ω.1.1 k).1.2.routeCount
        then some (min (ω.1.1 k).1.2.bid R) else none)=
      (if j∈firstK (ω.1.1 k).2 (ω.1.1 k).1.2.routeCount
        then some (ω.1.1 k).1.2.bid else none).map (fun b => min b R)
    split_ifs <;> rfl

section NativeCount
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  (C : Hybrid.ContextPolicy m c Seed) (Γ : FiniteGame m 2 c Seed)

theorem focalCount_erase (R : ℝ) (hR : 0≤ R) (i : Fin m)
    (a : JointAction 2) (ha : a.bid< R) (ω : Sample m 2 Seed) :
    focalCount (nativeGame C Γ R) i a (eraseSample R hR ω)=
      focalCount (nativeGame C Γ R) i a ω := by
  apply Fin.ext
  simp only [focalCount,boundedCount,inclusionCount_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hmem : i∈allocation (deviated i a (eraseSample R hR ω))
      (nativeGame C Γ R).policy (eraseSample R hR ω).1.2 j ↔
      i∈allocation (deviated i a ω) (nativeGame C Γ R).policy ω.1.2 j := by
    change i∈selection C R j (observe (deviated i a (eraseSample R hR ω)) j) (ω.1.2 j) ↔
      i∈selection C R j (observe (deviated i a ω) j) (ω.1.2 j)
    rw [observe_deviated_erase R hR i a ha ω j]
    by_cases hj : j∈firstK ω.2 a.routeCount
    · apply lower_selection_erase_iff C R j _ (ω.1.2 j) i a.bid ha
      simp only [observe,deviated_recipients_self,deviated_bid_self,if_pos hj]
    · have hi : observe (deviated i a ω) j i=none := by
        simp only [observe,deviated_recipients_self,deviated_bid_self,if_neg hj]
      have hiE : eraseList R (observe (deviated i a ω) j) i=none := by
        simp only [eraseList,hi,Option.map_none]
      have hn : i∉selection C R j (observe (deviated i a ω) j) (ω.1.2 j) :=
        fun h => (selection_feasible C R j _ _).2 i h hi
      have hnE : i∉selection C R j (eraseList R (observe (deviated i a ω) j)) (ω.1.2 j) :=
        fun h => (selection_feasible C R j _ _).2 i h hiE
      simp only [hn,hnE]
  simp only [hmem]

theorem erased_sampleLaw (R : ℝ) (hR : 0≤ R) :
    (sampleLaw Γ).map (eraseSample R hR)=
      ((Measure.pi (fun _ : Fin m => (userLaw Γ).map (eraseUser R hR))).prod
        (Measure.pi (fun _ : Fin 2 => Γ.seedLaw))).prod (permLaw 2) := by
  rw [sampleLaw,eraseSample,←Measure.map_prod_map _ _
    (measurable_eraseBackground R hR) measurable_id,Measure.map_id]
  rw [backgroundLaw,eraseBackground,←Measure.map_prod_map _ _
    (measurable_eraseProfile R hR) measurable_id,Measure.map_id]
  have he : (Measure.pi (fun _ : Fin m => userLaw Γ)).map (eraseProfile R hR) =
      Measure.pi (fun _ : Fin m => (userLaw Γ).map (eraseUser R hR)) :=
    Measure.pi_map_pi (fun _ => (measurable_eraseUser R hR).aemeasurable)
  rw [he]

theorem native_lower_count_law_of_erased_userLaw
    (Γ' : FiniteGame m 2 c Seed) (R : ℝ) (hR : 0≤ R)
    (husers : (userLaw Γ).map (eraseUser R hR)=
      (userLaw Γ').map (eraseUser R hR))
    (hseed : Γ.seedLaw=Γ'.seedLaw) (i : Fin m)
    (a : JointAction 2) (ha : a.bid< R) :
    (problem (nativeGame C Γ R) i).outcome a=
      (problem (nativeGame C Γ' R) i).outcome a := by
  let K := focalCount (nativeGame C Γ R) i a
  have hK : Measurable K := measurable_focalCount _ i a
  have hE := measurable_eraseSample (m:=m) (Seed:=Seed) R hR
  have hmap : (sampleLaw Γ).map (eraseSample R hR)=
      (sampleLaw Γ').map (eraseSample R hR) := by
    rw [erased_sampleLaw Γ R hR,erased_sampleLaw Γ' R hR,husers,hseed]
  have hfactor : K ∘ eraseSample R hR=K := by
    funext ω
    exact focalCount_erase C Γ R hR i a ha ω
  have hcount : (sampleLaw Γ).map K=(sampleLaw Γ').map K := by
    calc
      _=((sampleLaw Γ).map (eraseSample R hR)).map K := by
        rw [Measure.map_map hK hE,hfactor]
      _=((sampleLaw Γ').map (eraseSample R hR)).map K := by rw [hmap]
      _=_ := by rw [Measure.map_map hK hE,hfactor]
  rw [problem_outcome,problem_outcome]
  apply FiniteLaw.ext
  intro r
  change (∫ ω,if K ω=r then (1:ℝ) else 0 ∂sampleLaw Γ)=
    ∫ ω,if K ω=r then (1:ℝ) else 0 ∂sampleLaw Γ'
  have hi : Measurable (fun k : Fin 3 => if k=r then (1:ℝ) else 0) := measurable_of_countable _
  rw [← integral_map hK.aemeasurable hi.aestronglyMeasurable,
    ← integral_map hK.aemeasurable hi.aestronglyMeasurable,hcount]

end NativeCount

section PopulationReplacement
variable {m c : ℕ} (C : Hybrid.ContextPolicy m c unitInterval)

def erasedUpperAction (R : ℝ) (hR : 0≤ R) : JointAction 2 :=
  ⟨R,hR,1,by norm_num⟩

private theorem jointAction_eq {n : ℕ} (a b : JointAction n)
    (hbid : a.bid=b.bid) (hroute : a.routeCount=b.routeCount) : a=b := by
  cases a
  cases b
  cases hbid
  cases hroute
  rfl

theorem erased_upperJoint (R : ℝ) (hR : 0≤ R)
    (PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hH : ∀ᵐ x ∂(PH : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1) :
    (PH : Measure (ℝ×JointAction 2)).map (eraseValueAction R hR)=
      Measure.dirac (0,erasedUpperAction R hR) := by
  calc
    (PH : Measure (ℝ×JointAction 2)).map (eraseValueAction R hR)=
        (PH : Measure (ℝ×JointAction 2)).map (fun _ => (0,erasedUpperAction R hR)) := by
      apply Measure.map_congr (f := eraseValueAction R hR)
      filter_upwards [hH] with x hx
      change ((0:ℝ),eraseAction R hR x.2)=((0:ℝ),erasedUpperAction R hR)
      exact congrArg (fun a : JointAction 2 => ((0:ℝ),a))
        (jointAction_eq (eraseAction R hR x.2) (erasedUpperAction R hR)
          (min_eq_right hx.1) hx.2)
    _=_ := by rw [Measure.map_const,measure_univ,one_smul]

theorem population_lower_count_law_invariant
    (U R s a h : ℝ) (hR : 0≤ R)
    (hs : 0≤ s) (ha : 0≤ a) (hh : 0≤ h) (hsum : s+a+h=1)
    (PL PA PH PH' : ProbabilityMeasure (ℝ×JointAction 2))
    (hH : ∀ᵐ x ∂(PH : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (hH' : ∀ᵐ x ∂(PH' : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) (i : Fin m)
    (act : JointAction 2) (hb : act.bid< R) :
    (problem (populationGame C U R s a h hs ha hh hsum PL PA PH η hη0 hη1) i).outcome act=
      (problem (populationGame C U R s a h hs ha hh hsum PL PA PH' η hη0 hη1) i).outcome act := by
  let P := Hybrid.populationLaw s a h hs ha hh hsum PL PA PH
  let P' := Hybrid.populationLaw s a h hs ha hh hsum PL PA PH'
  let Γ := Hybrid.PopulationGame.game m c P η hη0 hη1 U
  let Γ' := Hybrid.PopulationGame.game m c P' η hη0 hη1 U
  apply native_lower_count_law_of_erased_userLaw C Γ Γ' R hR _ rfl i act hb
  rw [userLaw,userLaw,eraseUser,←Measure.map_prod_map _ _
    (measurable_eraseValueAction R hR) measurable_id,←Measure.map_prod_map _ _
    (measurable_eraseValueAction R hR) measurable_id,Measure.map_id,
    Hybrid.PopulationGame.joint_law,Hybrid.PopulationGame.joint_law]
  change ((Hybrid.populationJoint s a h PL PA PH).map (eraseValueAction R hR)).prod
    (permLaw 2)=((Hybrid.populationJoint s a h PL PA PH').map (eraseValueAction R hR)).prod
      (permLaw 2)
  congr 1
  simp only [Hybrid.populationJoint,Measure.map_add _ _ (measurable_eraseValueAction R hR),
    Measure.map_smul,erased_upperJoint R hR PH hH,erased_upperJoint R hR PH' hH']

theorem population_lower_payoff_invariant
    (U R s a h : ℝ) (hR : 0≤ R)
    (hs : 0≤ s) (ha : 0≤ a) (hh : 0≤ h) (hsum : s+a+h=1)
    (PL PA PH PH' : ProbabilityMeasure (ℝ×JointAction 2))
    (hH : ∀ᵐ x ∂(PH : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (hH' : ∀ᵐ x ∂(PH' : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) (i : Fin m)
    (v : ℝ) (act : JointAction 2) (hb : act.bid< R) :
    (problem (populationGame C U R s a h hs ha hh hsum PL PA PH η hη0 hη1) i).payoff v act=
      (problem (populationGame C U R s a h hs ha hh hsum PL PA PH' η hη0 hη1) i).payoff v act := by
  have hcount := population_lower_count_law_invariant C U R s a h hR hs ha hh hsum
    PL PA PH PH' hH hH' η hη0 hη1 i act hb
  change ((problem (populationGame C U R s a h hs ha hh hsum PL PA PH η hη0 hη1) i).outcome act).utility
    v act.bid 0 (Schedule.affine 2 η hη0 hη1.le) (Schedule.once 2)=
      ((problem (populationGame C U R s a h hs ha hh hsum PL PA PH' η hη0 hη1) i).outcome act).utility
        v act.bid 0 (Schedule.affine 2 η hη0 hη1.le) (Schedule.once 2)
  rw [hcount]

end PopulationReplacement
end FCAppendix.Affine.Tail04.ClosedUpperPriority
