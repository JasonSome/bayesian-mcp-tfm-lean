import FCAppendix.Affine.Hybrid.NativeUpperRank
import FCAppendix.Affine.Hybrid.UpperNativeEnvelope
import FCAppendix.Affine.Tail04.UpperOriginal

noncomputable section
namespace FCAppendix.Affine.Tail04.ClosedUpperPriority
open MeasureTheory ProbabilityTheory Set Game Bayes Classical
open scoped BigOperators

def encodeBid (R b : ℝ) : ℝ := if R≤ b then b+1 else b

theorem measurable_encodeBid (R : ℝ) : Measurable (encodeBid R) :=
  Measurable.ite (measurableSet_le measurable_const measurable_id)
    (measurable_id.add_const 1) measurable_id

theorem encodeBid_upper (R b : ℝ) (hb : R≤ b) : encodeBid R b=b+1 :=
  if_pos hb

theorem encodeBid_lower (R b : ℝ) (hb : b< R) : encodeBid R b=b :=
  if_neg (not_le.mpr hb)

theorem encodeBid_injective (R : ℝ) : Function.Injective (encodeBid R) := by
  intro a b hab
  unfold encodeBid at hab
  split_ifs at hab <;> linarith

theorem encodeBid_nonnegative (R b : ℝ) (hb : 0≤ b) : 0≤ encodeBid R b := by
  unfold encodeBid
  split_ifs <;> linarith

def encodeList {m : ℕ} (R : ℝ) (L : LocalList m) : LocalList m :=
  fun i => (L i).map (encodeBid R)

theorem measurable_encodeList {m : ℕ} (R : ℝ) :
    Measurable (encodeList (m:=m) R) := by
  have hopt : Measurable (Option.map (encodeBid R)) := by
    intro S hS
    change MeasurableSet ((encodeBid R) ⁻¹' (some ⁻¹' S))
    exact measurable_encodeBid R (measurable_some hS)
  exact measurable_pi_lambda _ (fun i => hopt.comp (measurable_pi_apply i))

theorem encodeList_present {m : ℕ} (R : ℝ) (L : LocalList m) (i : Fin m) :
    encodeList R L i≠none ↔ L i≠none := by
  cases he : L i <;> simp [encodeList,he]

theorem encodeList_some {m : ℕ} (R : ℝ) (L : LocalList m) (i : Fin m) (b : ℝ) :
    encodeList R L i=some (encodeBid R b) ↔ L i=some b := by
  cases he : L i with
  | none => simp [encodeList,he]
  | some a =>
    simp only [encodeList,he,Option.map_some,Option.some.injEq]
    exact ⟨fun h => encodeBid_injective R h,congrArg (encodeBid R)⟩

theorem encodeList_nonnegative {m : ℕ} (R : ℝ) (L : LocalList m)
    (hL : NonnegativeList L) : NonnegativeList (encodeList R L) := by
  intro i
  cases he : L i with
  | none => simp only [encodeList,he,Option.map_none,entryBid];exact le_rfl
  | some b =>
    change 0≤ entryBid ((L i).map (encodeBid R))
    rw [he]
    exact encodeBid_nonnegative R b (by simpa only [he,entryBid] using hL i)

theorem higher_encodeList_iff {m : ℕ} (R y : ℝ) (hR : 0< R) (hy : R≤ y)
    (L : LocalList m) (i : Fin m) :
    y+1< entryBid (encodeList R L i) ↔ y< entryBid (L i) := by
  cases he : L i with
  | none =>
    simp only [encodeList,he,Option.map_none,entryBid]
    constructor <;> intro hh <;> linarith
  | some b =>
    simp only [encodeList,he,Option.map_some,entryBid]
    by_cases hb : R≤ b
    · rw [encodeBid_upper R b hb]
      constructor <;> intro hh <;> linarith
    · rw [encodeBid,if_neg hb]
      constructor <;> intro hh <;> linarith

section Carrier
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
  (C : Hybrid.ContextPolicy m c Seed)

def selection (R : ℝ) (j : Fin 2) (L : LocalList m) (s : Seed) : Finset (Fin m) :=
  C.selection R j (encodeList R L) s

theorem selection_feasible (R : ℝ) (j : Fin 2) (L : LocalList m) (s : Seed) :
    LocallyFeasible L c (selection C R j L s) := by
  have h := C.selection_feasible R j (encodeList R L) s
  exact ⟨h.1,fun i hi => (encodeList_present R L i).mp (h.2 i hi)⟩

theorem measurable_selection (R : ℝ) (j : Fin 2) :
    Measurable (Function.uncurry (selection C R j)) :=
  (C.measurable_selection R j).comp
    (((measurable_encodeList R).comp measurable_fst).prodMk measurable_snd)

def localPolicy (R : ℝ) (j : Fin 2) : LocalPolicy m c Seed :=
  fun L s => ⟨selection C R j L s,selection_feasible C R j L s⟩

def nativeGame (Γ : FiniteGame m 2 c Seed) (R : ℝ) : FiniteGame m 2 c Seed :=
  {Γ with policy:=localPolicy C R,policy_measurable:=measurable_selection C R}

theorem upper_selection_iff_rank (R : ℝ) (hR : 0< R) (L : LocalList m)
    (hL : NonnegativeList L) (j : Fin 2) (s : Seed) (i : Fin m)
    (y : ℝ) (hy : R≤ y) (hi : L i=some y)
    (hno : ∀ k, k≠i → L k≠some y) :
    i∈selection C R j L s ↔
      (Finset.univ.filter (fun k => y< entryBid (L k))).card< c := by
  have hiE : encodeList R L i=some (y+1) := by
    rw [←encodeBid_upper R y hy]
    exact (encodeList_some R L i y).mpr hi
  have hnoE : ∀ k, k≠i → encodeList R L k≠some (y+1) := by
    intro k hk he
    apply hno k hk
    apply (encodeList_some R L k y).mp
    simpa only [encodeBid_upper R y hy] using he
  have hr := C.upper_selection_iff_rank hR.le (encodeList R L)
    (encodeList_nonnegative R L hL) j s i hiE (by linarith : R< y+1) hnoE
  have he : Finset.univ.filter (fun k => y+1< entryBid (encodeList R L k))=
      Finset.univ.filter (fun k => y< entryBid (L k)) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact higher_encodeList_iff R y hR hy L k
  rw [he] at hr
  exact hr

variable (Γ : FiniteGame m 2 c Seed) (R : ℝ)
local notation "G" => nativeGame C Γ R

theorem native_upper_accepts_iff_rank (hR : 0< R)
    (hatom : ∀ (j : Fin 2) (b : ℝ), R≤ b →
      userLaw G {d | j∈firstK d.2 d.1.2.routeCount ∧ d.1.2.bid=b}=0)
    (i : Fin m) (j : Fin 2) (y : ℝ) (hy : R≤ y) :
    ∀ᵐ ω ∂backgroundLaw G,
      Accepts G i y j ω ↔ rivals i (aboveAt j y) ω< c := by
  have hz := measure_eq_zero_iff_ae_notMem.mp (hatom j y hy)
  have hall : ∀ᵐ d ∂userProfileLaw G,
      ∀ k, ¬(j∈firstK (d k).2 (d k).1.2.routeCount ∧ (d k).1.2.bid=y) :=
    ae_all_iff.mpr (fun k =>
      (measurePreserving_eval (fun _ : Fin m => userLaw G) k).quasiMeasurePreserving.ae hz)
  have hback : ∀ᵐ ω ∂backgroundLaw G,
      ∀ k, ¬(j∈firstK (ω.1 k).2 (ω.1 k).1.2.routeCount ∧ (ω.1 k).1.2.bid=y) :=
    measurePreserving_fst.quasiMeasurePreserving.ae hall
  filter_upwards [hback] with ω hno
  let L := presentList ω i y j
  have hL : NonnegativeList L := by
    intro k
    cases he : L k with
    | none => simp only [entryBid];exact le_rfl
    | some b => exact presentList_bid_nonneg ω i y (hR.le.trans hy) j k b he
  have hn : ∀ k, k≠i → L k≠some y := fun k hk hky =>
    hno k (presentList_other_some ω i k hk y j y hky)
  have hs := upper_selection_iff_rank C R hR L hL j (ω.2 j) i y hy
    (presentList_self ω i y j) hn
  have he : Finset.univ.filter (fun k => y< entryBid (L k))=
      (Finset.univ.erase i).filter (fun k => ω.1 k∈aboveAt j y) := by
    ext k
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase,and_true,
      aboveAt,mem_setOf_eq]
    by_cases hk : k=i
    · subst k
      simp only [L,presentList_self,entryBid,lt_self_iff_false,ne_eq,
        not_true_eq_false,false_and]
    · rw [show L k=if j∈firstK (ω.1 k).2 (ω.1 k).1.2.routeCount
        then some (ω.1 k).1.2.bid else none from presentList_other ω i k hk y j]
      by_cases hr : j∈firstK (ω.1 k).2 (ω.1 k).1.2.routeCount
      · simp [hr,entryBid,hk]
      · simp [hr,entryBid,not_lt_of_ge (hR.le.trans hy)]
  rw [he] at hs
  change i∈selection C R j L (ω.2 j) ↔ _
  simpa only [rivals_eq_card] using hs

theorem native_upper_acceptProb (hR : 0< R)
    (hatom : ∀ (j : Fin 2) (b : ℝ), R≤ b →
      userLaw G {d | j∈firstK d.2 d.1.2.routeCount ∧ d.1.2.bid=b}=0)
    (i : Fin m) (j : Fin 2) (y : ℝ) (hy : R≤ y) :
    acceptProb G i y j=binomBelow (m-1) (alphaGt G j y) c := by
  rw [alphaGt,←prob_rivals_lt G i _ (measurableSet_aboveAt j y) c]
  apply measureReal_congr
  exact (native_upper_accepts_iff_rank C Γ R hR hatom i j y hy).mono
    (fun _ h => propext h)

theorem native_upper_meanAcceptProb (hR : 0< R)
    (hatom : ∀ (j : Fin 2) (b : ℝ), R≤ b →
      userLaw G {d | j∈firstK d.2 d.1.2.routeCount ∧ d.1.2.bid=b}=0)
    (i : Fin m) (y : ℝ) (hy : R≤ y) :
    meanAcceptProb G i y=binomBelow (m-1) (alphaGt G 0 y) c := by
  unfold meanAcceptProb
  simp_rw [native_upper_acceptProb C Γ R hR hatom i _ y hy,alphaGt_eq G _ 0]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

theorem native_upper_mean_eq_bidRank (hR : 0< R) (mu : Measure ℝ) (b : ℝ → ℝ)
    (hcm : c≤ m)
    (hatom : ∀ (j : Fin 2) (y : ℝ), R≤ y →
      userLaw G {d | j∈firstK d.2 d.1.2.routeCount ∧ d.1.2.bid=y}=0)
    (htail : ∀ (j : Fin 2) (y : ℝ), R≤ y →
      alphaGt G j y=(mu.map b).real (Ioi y)/2)
    (i : Fin m) (y : ℝ) (hy : R≤ y) :
    meanAcceptProb G i y=Existence.RankEnvelope.bidRank mu (m-1) c 2 b y :=
  _root_.FCAppendix.Affine.Tail04.native_upper_mean_of_policy_rank G mu b R hcm
    (native_upper_accepts_iff_rank C Γ R hR hatom) htail i y hy

end Carrier

section OriginalPopulation
variable {m c : ℕ} (C : Hybrid.ContextPolicy m c unitInterval)

def populationGame (U R s a h : ℝ) (hs : 0≤ s) (ha : 0≤ a) (hh : 0≤ h)
    (hsum : s+a+h=1) (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) : FiniteGame m 2 c unitInterval :=
  nativeGame C (Hybrid.PopulationGame.game m c
    (Hybrid.populationLaw s a h hs ha hh hsum PL PA PH) η hη0 hη1 U) R

theorem populationGame_joint_law (U R s a h : ℝ)
    (hs : 0≤ s) (ha : 0≤ a) (hh : 0≤ h) (hsum : s+a+h=1)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) :
    let G := populationGame C U R s a h hs ha hh hsum PL PA PH η hη0 hη1
    G.F⊗ₘG.σ=Hybrid.populationJoint s a h PL PA PH := by
  exact Hybrid.PopulationGame.joint_law m c
    (Hybrid.populationLaw s a h hs ha hh hsum PL PA PH) η hη0 hη1 U

theorem population_upper_mean_eq_bidRank
    (U R s a h : ℝ) (hR : 0< R) (hUR : U< R)
    (hs : 0≤ s) (ha : 0≤ a) (hh : 0≤ h) (hsum : s+a+h=1)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2)) (FH : ProbabilityMeasure ℝ)
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (hH : ∀ᵐ x ∂(PH : Measure (ℝ×JointAction 2)), x.2.routeCount=1)
    (hnull : ∀ y : ℝ, (PH : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0)
    (b : ℝ → ℝ)
    (hbid : (PH : Measure (ℝ×JointAction 2)).map (fun x => x.2.bid)=
      (FH : Measure ℝ).map b)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) (hcm : c≤ m)
    (i : Fin m) (y : ℝ) (hy : R≤ y) :
    meanAcceptProb (populationGame C U R s a h hs ha hh hsum PL PA PH η hη0 hη1) i y=
      Existence.RankEnvelope.bidRank (ENNReal.ofReal h • (FH : Measure ℝ))
        (m-1) c 2 b y := by
  let P := Hybrid.populationLaw s a h hs ha hh hsum PL PA PH
  let Γ := Hybrid.PopulationGame.game m c P η hη0 hη1 U
  change meanAcceptProb (nativeGame C Γ R) i y=_
  apply native_upper_mean_eq_bidRank C Γ R hR _ b hcm _ _ i y hy
  · intro j z hz
    exact Hybrid.population_upper_visible_atomless m c U s a h hs ha hh hsum
      PL PA PH hL hA hnull η hη0 hη1 j z (hUR.trans_le hz)
  · intro j z hz
    have ht := Hybrid.population_upper_alphaGt m c U s a h hs ha hh hsum
      PL PA PH hL hA hH η hη0 hη1 j z (hUR.trans_le hz)
    have hw := Hybrid.weighted_upper_bid_tail FH PH b hbid h hh z
    change alphaGt Γ j z=_
    rw [ht,hw]

theorem population_floor_mean
    (U R s a h : ℝ) (hR : 0< R) (hUR : U< R)
    (hs : 0≤ s) (ha : 0≤ a) (hh : 0≤ h) (hsum : s+a+h=1)
    (PL PA PH : ProbabilityMeasure (ℝ×JointAction 2))
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ×JointAction 2)), x.2.bid≤ U)
    (hH : ∀ᵐ x ∂(PH : Measure (ℝ×JointAction 2)), R≤ x.2.bid ∧ x.2.routeCount=1)
    (hnull : ∀ y : ℝ, (PH : Measure (ℝ×JointAction 2)) {x | x.2.bid=y}=0)
    (η : ℝ) (hη0 : 0≤ η) (hη1 : η<1) (i : Fin m) :
    meanAcceptProb (populationGame C U R s a h hs ha hh hsum PL PA PH η hη0 hη1) i R=
      binomBelow (m-1) (h/2) c := by
  let P := Hybrid.populationLaw s a h hs ha hh hsum PL PA PH
  let Γ := Hybrid.PopulationGame.game m c P η hη0 hη1 U
  have hgt : ∀ᵐ x ∂(PH : Measure (ℝ×JointAction 2)), R< x.2.bid := by
    filter_upwards [hH,measure_eq_zero_iff_ae_notMem.mp (hnull R)] with x hx hn
    exact lt_of_le_of_ne hx.1 (Ne.symm hn)
  have htail : (PH : Measure (ℝ×JointAction 2)).real {x | R< x.2.bid}=1 := by
    have he : {x : ℝ×JointAction 2 | R< x.2.bid}=ᵐ[(PH : Measure (ℝ×JointAction 2))] univ :=
      hgt.mono (fun x hx => propext (iff_of_true hx (mem_univ x)))
    rw [measureReal_congr he]
    simp
  change meanAcceptProb (nativeGame C Γ R) i R=_
  rw [native_upper_meanAcceptProb C Γ R hR
    (fun j z hz => Hybrid.population_upper_visible_atomless m c U s a h hs ha hh hsum
      PL PA PH hL hA hnull η hη0 hη1 j z (hUR.trans_le hz)) i R le_rfl]
  have ht := Hybrid.population_upper_alphaGt m c U s a h hs ha hh hsum
    PL PA PH hL hA (hH.mono (fun _ hx => hx.2)) η hη0 hη1 0 R hUR
  change alphaGt Γ 0 R=h*(PH : Measure (ℝ×JointAction 2)).real {x | R< x.2.bid}/2 at ht
  change binomBelow (m-1) (alphaGt Γ 0 R) c=_
  rw [ht,htail,mul_one]

end OriginalPopulation

section StrictClassifierObstruction
variable {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem strict_classifier_gap_profitable
    (C : Hybrid.ContextPolicy m c Seed) (Γ : FiniteGame m 2 c Seed)
    (U R y : ℝ) (hU : 0≤ U) (hyU : U< y) (hyR : y< R)
    (hatom : ∀ (j : Fin 2) (b : ℝ), U< b →
      userLaw (C.nativeGame Γ U)
        {d | j∈firstK d.2 d.1.2.routeCount ∧ d.1.2.bid=b}=0)
    (hsupport : ∀ᵐ d ∂userLaw (C.nativeGame Γ U), d.1.2.bid≤ U ∨ R< d.1.2.bid)
    (i : Fin m) (hq : 0< meanAcceptProb (C.nativeGame Γ U) i R) (v : ℝ) :
    (problem (C.nativeGame Γ U) i).payoff v
      (⟨R,hU.trans (hyU.trans hyR).le,1,by norm_num⟩ : JointAction 2) <
    (problem (C.nativeGame Γ U) i).payoff v
      (⟨y,hU.trans hyU.le,1,by norm_num⟩ : JointAction 2) := by
  have htail : alphaGt (C.nativeGame Γ U) 0 y=alphaGt (C.nativeGame Γ U) 0 R := by
    apply measureReal_congr
    filter_upwards [hsupport] with d hd
    apply propext
    change (0∈firstK d.2 d.1.2.routeCount ∧ y< d.1.2.bid) ↔
      (0∈firstK d.2 d.1.2.routeCount ∧ R< d.1.2.bid)
    rcases hd with hd | hd
    · have hyb : ¬y< d.1.2.bid := not_lt.mpr (hd.trans hyU.le)
      have hRb : ¬R< d.1.2.bid := not_lt.mpr (hd.trans (hyU.trans hyR).le)
      simp only [hyb,hRb,and_false]
    · simp only [hyR.trans hd,hd,and_true]
  have hmean : meanAcceptProb (C.nativeGame Γ U) i y=
      meanAcceptProb (C.nativeGame Γ U) i R := by
    rw [C.native_upper_meanAcceptProb Γ hU hatom i y hyU,
      C.native_upper_meanAcceptProb Γ hU hatom i R (hyU.trans hyR),htail]
  rw [singleton_payoff _ (by norm_num) i _ rfl,
    singleton_payoff _ (by norm_num) i _ rfl,hmean]
  change (v-(C.nativeGame Γ U).g-R)*meanAcceptProb (C.nativeGame Γ U) i R <
    (v-(C.nativeGame Γ U).g-y)*meanAcceptProb (C.nativeGame Γ U) i R
  exact mul_lt_mul_of_pos_right (by linarith) hq

end StrictClassifierObstruction
end FCAppendix.Affine.Tail04.ClosedUpperPriority
