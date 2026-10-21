import FCAppendix.Affine.Uniform07Finishing.Native.StrictContext

noncomputable section
namespace FCAppendix.Affine.Uniform07Finishing.StrictNative
open MeasureTheory ProbabilityTheory Bayes Game Set Filter
open scoped BigOperators

lemma univ_erase_two (j : Fin 2) : Finset.univ.erase j={otherProposer j} := by
  ext l
  fin_cases j <;> fin_cases l <;> simp [otherProposer]

lemma otherInclusionCount_two {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (j : Fin 2) (i : Fin m) (ω : Background m 2 Seed) :
    (otherInclusionCount Γ j i ω).val=
      if i∈allocation (drawsRealization ω.1) Γ.policy ω.2 (otherProposer j) then 1 else 0 := by
  rw [otherInclusionCount_eq_sum,univ_erase_two,Finset.sum_singleton]

def posteriorOtherMean {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (B : PosteriorSystem Γ)
    (j : Fin 2) (L : LocalList m) (i : Fin m) : ℝ :=
  (posteriorCountBelief Γ B j L i).expect (fun r=>(r.val:ℝ))

lemma posteriorOtherMean_eq_profile_integral {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (B : PosteriorSystem Γ)
    (j : Fin 2) (L : LocalList m) (i : Fin m) :
    posteriorOtherMean Γ B j L i=
      ∫d,∫s : Fin 2 → Seed,((otherInclusionCount Γ j i (d,s)).val:ℝ)
        ∂Measure.pi (fun _ : Fin 2=>Γ.seedLaw) ∂B.posterior j L := by
  rw [posteriorOtherMean,posteriorCountBelief,FiniteLaw.expect_ofMeasure]
  apply integral_prod
  have hm : Measurable (fun ω : Background m 2 Seed=>(otherInclusionCount Γ j i ω).val :
      Background m 2 Seed→ℝ) :=
    (measurable_of_countable (fun r : Fin 2=>(r.val:ℝ))).comp
      (measurable_otherInclusionCount Γ j i)
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Eventually.of_forall (fun ω=>by
    rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Nat.le_of_lt_succ (otherInclusionCount Γ j i ω).isLt)

lemma posterior_affine_receipt {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (B : PosteriorSystem Γ) (η : ℝ)
    (hη0 : 0≤η) (hη1 : η≤ 1) (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (j : Fin 2) (L : LocalList m) (i : Fin m) (b : ℝ) :
    Finite.conditionalReceipt Γ.A (posteriorCountBelief Γ B j L i) b=
      b*(1-(1-η)/2*posteriorOtherMean Γ B j L i) := by
  rw [hA,Finite.conditionalReceipt]
  let ν := posteriorCountBelief Γ B j L i
  have he (r : Fin 2) :
      b*(Schedule.affine 2 η hη0 hη1).charge (r.val+1)/((r.val:ℝ)+1)=
        b*(1-(1-η)/2*(r.val:ℝ)) := by
    fin_cases r
    · simp [Schedule.affine,successIndicator]
    · simp [Schedule.affine,successIndicator]
      ring
  rw [ν.expect_congr he,FiniteLaw.expect_const_mul,FiniteLaw.expect_sub,
    FiniteLaw.expect_const,FiniteLaw.expect_const_mul]
  rfl

lemma broadcastPart_some {m : ℕ} {U b : ℝ} (L : LocalList m) (i : Fin m)
    (hi : L i=some b) (hb : b< U) : broadcastPart U L i=some b := by
  simp [broadcastPart,StrictTags.lowList,StrictTags.tag,hi,hb]

def ContextFactors {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) (U : ℝ)
    (C : Fin 2 → ClassifiedContext m → Seed → Finset (Fin m)) : Prop :=
  ∀j L s i,broadcastPart U L i≠none →
    (i∈(Γ.policy j L s).val ↔ i∈C j (observedContext U j L) s)

def contextAcceptance {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed)
    (C : Fin 2 → ClassifiedContext m → Seed → Finset (Fin m))
    (j : Fin 2) (X : ClassifiedContext m) (i : Fin m) : ℝ :=
  ∫s,if i∈C j X s then (1:ℝ) else 0 ∂Γ.seedLaw

theorem classifiedPosterior_lower_mean {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) {U R : ℝ} (hU : 0≤ U) (hR : U≤ R)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈classifiedProfiles m U)
    (C : Fin 2 → ClassifiedContext m → Seed → Finset (Fin m))
    (hC : ∀j,Measurable (Function.uncurry (C j))) (hfactor : ContextFactors Γ U C)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (i : Fin m) (b : ℝ) (hi : L i=some b) (hb : b< U) :
    posteriorOtherMean Γ (classifiedPosterior Γ (R:=R) hfull) j L i=
      contextAcceptance Γ C (otherProposer j) (observedContext U j L) i := by
  classical
  rw [posteriorOtherMean_eq_profile_integral]
  have hstat : ∀ᵐd ∂(classifiedPosterior Γ (R:=R) hfull).posterior j L,
      (∫s : Fin 2 → Seed,((otherInclusionCount Γ j i (d,s)).val:ℝ)
          ∂Measure.pi (fun _ : Fin 2=>Γ.seedLaw))=
        contextAcceptance Γ C (otherProposer j) (observedContext U j L) i := by
    filter_upwards [classifiedPosterior_support Γ hU hR hfull j L hL] with d hd
    have hctx : observedContext U (otherProposer j) (observe (drawsRealization d) (otherProposer j))=
        observedContext U j L := by
      rw [observedContext_eq_actual d hd.2,←observedContext_eq_actual d hd.2 j,hd.1]
    have hlow : broadcastPart U (observe (drawsRealization d) (otherProposer j)) i≠none := by
      rw [broadcastPart_common d hd.2 (otherProposer j) j,hd.1,broadcastPart_some L i hi hb]
      exact Option.some_ne_none b
    have heq (s : Fin 2 → Seed) : ((otherInclusionCount Γ j i (d,s)).val : ℝ)=
        if i∈C (otherProposer j) (observedContext U j L) (s (otherProposer j)) then 1 else 0 := by
      rw [otherInclusionCount_two]
      have hf := hfactor (otherProposer j) (observe (drawsRealization d) (otherProposer j))
        (s (otherProposer j)) i hlow
      rw [hctx] at hf
      simp only [allocation,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
      simp only [hf]
    rw [integral_congr_ae (Eventually.of_forall heq)]
    let f : Seed→ℝ := fun s=>if i∈C (otherProposer j) (observedContext U j L) s then 1 else 0
    have hm : Measurable f := Measurable.ite
      (((hC (otherProposer j)).comp (measurable_const.prodMk measurable_id))
        (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin m) | i∈S}))
      measurable_const measurable_const
    have hp := measurePreserving_eval (fun _ : Fin 2=>Γ.seedLaw) (otherProposer j)
    change (∫s : Fin 2→ Seed,f (s (otherProposer j)) ∂Measure.pi (fun _=>Γ.seedLaw))=
      ∫s,f s ∂Γ.seedLaw
    calc
      _ = ∫s,f s ∂(Measure.pi (fun _ : Fin 2=>Γ.seedLaw)).map (fun s=>s (otherProposer j)) :=
        (integral_map hp.measurable.aemeasurable hm.aestronglyMeasurable).symm
      _ = _ := by rw [hp.map_eq]
  calc
    _ = ∫_d,contextAcceptance Γ C (otherProposer j) (observedContext U j L) i
        ∂(classifiedPosterior Γ (R:=R) hfull).posterior j L := integral_congr_ae hstat
    _ = _ := by simp

lemma classified_upper_other_absent {m : ℕ} {U b : ℝ} (d : UserProfile m 2)
    (hd : d∈classifiedProfiles m U) (j : Fin 2) (i : Fin m)
    (hi : observe (drawsRealization d) j i=some b) (hb : U≤ b) :
    observe (drawsRealization d) (otherProposer j) i=none := by
  classical
  have hj : j∈(drawsRealization d).recipients i := by
    by_contra hn
    simp only [observe,if_neg hn] at hi
    cases hi
  have hbid : (d i).1.2.bid=b := by
    change ((drawsRealization d).action i).bid=b
    apply Option.some.inj
    simpa only [observe,if_pos hj] using hi
  have hr : (d i).1.2.routeCount=1 := by
    rcases hd i with hlow | hupp
    · rw [hbid] at hlow
      exact False.elim (not_lt.mpr hb hlow.1)
    · exact hupp.2
  have hc : ((drawsRealization d).recipients i).card=1 := by
    rw [(drawsRealization d).chosen_size]
    exact hr
  obtain ⟨l,hl⟩ := Finset.card_eq_one.mp hc
  have hlj : l=j := by
    rw [hl] at hj
    exact (Finset.mem_singleton.mp hj).symm
  rw [hlj] at hl
  simp only [observe,hl,Finset.mem_singleton,otherProposer_ne,if_false]

theorem classifiedPosterior_upper_mean {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) {U R : ℝ} (hU : 0≤ U) (hR : U≤ R)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈classifiedProfiles m U)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (i : Fin m) (b : ℝ) (hi : L i=some b) (hb : U≤ b) :
    posteriorOtherMean Γ (classifiedPosterior Γ (R:=R) hfull) j L i=0 := by
  classical
  rw [posteriorOtherMean_eq_profile_integral]
  apply integral_eq_zero_of_ae
  filter_upwards [classifiedPosterior_support Γ hU hR hfull j L hL] with d hd
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro s
  have hobs : observe (drawsRealization d) j i=some b := by rw [hd.1,hi]
  have hnone := classified_upper_other_absent d hd.2 j i hobs hb
  have hnot : i∉allocation (drawsRealization d) Γ.policy s (otherProposer j) := by
    intro hin
    exact ((Γ.policy (otherProposer j) (observe (drawsRealization d) (otherProposer j))
      (s (otherProposer j))).property.2 i hin) hnone
  change ((otherInclusionCount Γ j i (d,s)).val:ℝ)=0
  rw [otherInclusionCount_two,if_neg hnot]
  norm_num

theorem classifiedPosterior_lower_receipt {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) {U R : ℝ} (hU : 0≤ U) (hR : U≤ R)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈classifiedProfiles m U)
    (η : ℝ) (hη0 : 0≤η) (hη1 : η≤ 1) (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (C : Fin 2 → ClassifiedContext m → Seed → Finset (Fin m))
    (hC : ∀j,Measurable (Function.uncurry (C j))) (hfactor : ContextFactors Γ U C)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (i : Fin m) (b : ℝ) (hi : L i=some b) (hb : b< U) :
    Finite.conditionalReceipt Γ.A
        (posteriorCountBelief Γ (classifiedPosterior Γ (R:=R) hfull) j L i) b=
      b*(1-(1-η)/2*contextAcceptance Γ C (otherProposer j) (observedContext U j L) i) := by
  rw [posterior_affine_receipt Γ _ η hη0 hη1 hA,
    classifiedPosterior_lower_mean Γ hU hR hfull C hC hfactor j L hL i b hi hb]

theorem classifiedPosterior_upper_receipt {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed) {U R : ℝ} (hU : 0≤ U) (hR : U≤ R)
    (hfull : ∀ᵐd ∂userProfileLaw Γ,d∈classifiedProfiles m U)
    (η : ℝ) (hη0 : 0≤η) (hη1 : η≤ 1) (hA : Γ.A=Schedule.affine 2 η hη0 hη1)
    (j : Fin 2) (L : LocalList m) (hL : FeasibleObservedList j L)
    (i : Fin m) (b : ℝ) (hi : L i=some b) (hb : U≤ b) :
    Finite.conditionalReceipt Γ.A
      (posteriorCountBelief Γ (classifiedPosterior Γ (R:=R) hfull) j L i) b=b := by
  rw [posterior_affine_receipt Γ _ η hη0 hη1 hA,
    classifiedPosterior_upper_mean Γ hU hR hfull j L hL i b hi hb]
  ring

end FCAppendix.Affine.Uniform07Finishing.StrictNative
