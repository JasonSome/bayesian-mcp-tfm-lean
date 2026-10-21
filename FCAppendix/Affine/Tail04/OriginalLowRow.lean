import FCAppendix.Affine.Tail04.OriginalPopulationSupport

noncomputable section
namespace FCAppendix.Affine.Tail04.OriginalPopulation
open MeasureTheory ProbabilityTheory Set Filter Game Bayes
open Existence.Distributional OriginalValues Hybrid

variable (E : Observable.Regions)

def jointRow (x : UserDraw 2) : LowBody.RowRival := E.collapse (x.1.2,x.2)

theorem measurable_jointRow : Measurable (jointRow E) :=
  E.measurable_collapse.comp (measurable_fst.snd.prodMk measurable_snd)

theorem jointRow_low (Q : ProbabilityMeasure (ℝ × JointAction 2))
    (hQ : ∀ᵐ x ∂(Q : Measure (ℝ × JointAction 2)), x.2.bid ≤ E.d) :
    ((Q : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map (jointRow E) =
      ((Q : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid)).map
        (fun b => ((0:Fin 4),b)) := by
  have he : ((Q : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map (jointRow E) =
      ((Q : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map
        (fun x => ((0:Fin 4),x.1.2.bid)) := by
    apply Measure.map_congr
    have hp := (measurePreserving_fst (μ:=(Q : Measure (ℝ × JointAction 2)))
      (ν:=permLaw 2)).quasiMeasurePreserving.ae hQ
    exact hp.mono (fun _ hx => by simp only [jointRow, Observable.Regions.collapse, if_pos hx])
  have hb : Measurable (fun x : ℝ × JointAction 2 => x.2.bid) :=
    (measurable_bid 2).comp measurable_snd
  have hf : Measurable (fun x : ℝ × JointAction 2 => ((0:Fin 4),x.2.bid)) :=
    measurable_const.prodMk hb
  rw [he]
  change ((Q : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map
    ((fun x : ℝ × JointAction 2 => ((0:Fin 4),x.2.bid)) ∘ Prod.fst) = _
  rw [← Measure.map_map hf measurable_fst, Measure.map_fst_prod, measure_univ, one_smul]
  exact (Measure.map_map (measurable_const.prodMk measurable_id) hb).symm

theorem jointRow_common (Q : ProbabilityMeasure (ℝ × JointAction 2))
    (hQ : ∀ᵐ x ∂(Q : Measure (ℝ × JointAction 2)),
      E.d < x.2.bid ∧ x.2.bid ∉ E.privateBids) :
    ((Q : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map (jointRow E) =
      Measure.dirac (1,0) := by
  have he : ((Q : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map (jointRow E) =
      ((Q : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map
        (fun _ => ((1:Fin 4),(0:ℝ))) := by
    apply Measure.map_congr
    have hp := (measurePreserving_fst (μ:=(Q : Measure (ℝ × JointAction 2)))
      (ν:=permLaw 2)).quasiMeasurePreserving.ae hQ
    exact hp.mono (fun _ hx => by simp only [jointRow, Observable.Regions.collapse,
      if_neg (not_le.mpr hx.1), if_neg hx.2])
  rw [he, Measure.map_const, measure_univ, one_smul]

theorem jointRow_private (Q : ProbabilityMeasure (ℝ × JointAction 2))
    (hQ : ∀ᵐ x ∂(Q : Measure (ℝ × JointAction 2)), x.2.bid ∈ E.privateBids) :
    ((Q : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map (jointRow E) =
      (permLaw 2).map upperRow := by
  have he : ((Q : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map (jointRow E) =
      ((Q : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map (upperRow ∘ Prod.snd) := by
    apply Measure.map_congr
    have hp := (measurePreserving_fst (μ:=(Q : Measure (ℝ × JointAction 2)))
      (ν:=permLaw 2)).quasiMeasurePreserving.ae hQ
    exact hp.mono (fun _ hx => by simp only [jointRow, Observable.Regions.collapse,
      if_neg (not_le.mpr (E.private_above_low hx)), if_pos hx, Function.comp_apply])
  rw [he, ← Measure.map_map (measurable_of_countable upperRow) measurable_snd,
    Measure.map_snd_prod, measure_univ, one_smul]

theorem fourJoint_low_row (s h a z : ℝ) (hh : 0 ≤ h) (hz : 0 ≤ z)
    (PL PP PA PH : ProbabilityMeasure (ℝ × JointAction 2))
    (hL : ∀ᵐ x ∂(PL : Measure (ℝ × JointAction 2)), x.2.bid ≤ E.d)
    (hP : ∀ᵐ x ∂(PP : Measure (ℝ × JointAction 2)), x.2.bid ∈ E.privateBids)
    (hA : ∀ᵐ x ∂(PA : Measure (ℝ × JointAction 2)),
      E.d < x.2.bid ∧ x.2.bid ∉ E.privateBids)
    (hH : ∀ᵐ x ∂(PH : Measure (ℝ × JointAction 2)), x.2.bid ∈ E.privateBids) :
    ((fourJoint s h a z PL PP PA PH).prod (permLaw 2)).map (jointRow E) =
      LowBody.rivalLaw s a (h+z)
        ((PL : Measure (ℝ × JointAction 2)).map (fun x => x.2.bid)) := by
  rw [fourJoint, Measure.add_prod, Measure.add_prod, Measure.add_prod,
    Measure.prod_smul_left, Measure.prod_smul_left, Measure.prod_smul_left, Measure.prod_smul_left]
  simp only [Measure.map_add _ _ (measurable_jointRow E), Measure.map_smul]
  rw [jointRow_low E PL hL, jointRow_private E PP hP,
    jointRow_common E PA hA, jointRow_private E PH hH,
    upperRow_law, LowBody.rivalLaw]
  have hcoef : ENNReal.ofReal ((h+z)/2) =
      ENNReal.ofReal h*ENNReal.ofReal (1/2:ℝ)+
        ENNReal.ofReal z*ENNReal.ofReal (1/2:ℝ) := by
    rw [show (h+z)/2=(h+z)*(1/2) by ring,
      ENNReal.ofReal_mul (add_nonneg hh hz), ENNReal.ofReal_add hh hz, add_mul]
  rw [hcoef]
  simp only [smul_add, smul_smul, add_smul]
  ac_rfl

variable (P : ValueParameters) (hd : E.d=P.d0) (t : ℝ) (ht : P.M ≤ t)

local instance : IsProbabilityMeasure (P.originalMovingActiveLaw t ht) :=
  P.originalMovingActiveLaw_probability t ht

variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
    (πP : Law (A:=Icc E.R E.Rp) P.originalPartialLaw)
    (πA : Law (A:=Icc (1:ℝ) E.U) (P.originalMovingActiveLaw t ht))
    (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
    (hfloor : ∀ v, t < v → E.H ≤ upperBid v)

local notation "hR" => E.d_nonneg.trans E.d_lt_R.le
local notation "J" => originalJoint P t ht E.R E.Rp E.U hR πL πP πA upperBid hupperBid

include hd hfloor in
theorem original_exact_low_row :
    ((J : Measure (ℝ × JointAction 2)).prod (permLaw 2)).map (jointRow E) =
      LowBody.rivalLaw (lowMass P.theta)
        (activeMass P.theta-activeMass P.theta*P.zeta*powerTail P.M 10 t)
        (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)
        (LowBody.realLowBidLaw πL.1 : Measure ℝ) := by
  have hL : ∀ᵐ x ∂(lowJoint P.originalLowLaw πL : Measure (ℝ × JointAction 2)),
      x.2.bid ≤ E.d := by
    apply (ae_map_iff (measurable_fst.subtype_val.prodMk
      ((measurable_lowBroadcast P.d0).comp measurable_snd)).aemeasurable
      (measurableSet_le ((measurable_bid 2).comp measurable_snd) measurable_const)).mpr
    exact Eventually.of_forall (fun x => by
      change (x.2:ℝ) ≤ E.d
      rw [hd]
      exact x.2.2.2)
  have hP := (bandJoint_support hR 1 (by norm_num) P.originalPartialLaw πP).mono
    (fun _ hx => (Or.inl hx.2.1 : _ ∈ E.privateBids))
  have hA := (bandJoint_support (by norm_num : (0:ℝ)≤1) 2 le_rfl
    (P.originalMovingActiveLaw t ht) πA).mono (fun x hx =>
      (show E.d < x.2.bid ∧ x.2.bid ∉ E.privateBids from
        ⟨E.d_lt_one.trans_le hx.2.1.1, by
          rintro (hp | hp)
          · linarith [hp.2, hx.2.1.1, E.Rp_lt_one]
          · change E.H ≤ x.2.bid at hp
            linarith [hx.2.1.2, E.U_lt_H]⟩))
  let FH : ProbabilityMeasure ℝ :=
    ⟨P.originalMovingUpperLaw t, P.originalMovingUpperLaw_probability t⟩
  have hH := (upperJoint_support FH upperBid hupperBid E.H
    ((P.originalMovingUpperLaw_support t).mono (fun v hv => hfloor v hv))).mono
      (fun _ hx => (Or.inr hx.1 : _ ∈ E.privateBids))
  have he := fourJoint_low_row E (lowMass P.theta) partialMass
    (activeMass P.theta-activeMass P.theta*P.zeta*powerTail P.M 10 t)
    (activeMass P.theta*P.zeta*powerTail P.M 10 t)
    (by norm_num [partialMass]) (P.tailMass_nonneg t ht) _ _ _ _ hL hP hA hH
  rw [lowJoint_bid_marginal] at he
  exact he

include hd hfloor in
theorem native_original_exact_low_row {m c : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (Γ : FiniteGame m 2 c Seed)
    (hjoint : Γ.F ⊗ₘ Γ.σ = (J : Measure (ℝ × JointAction 2))) :
    (userLaw Γ).map (E.nativeRow Γ) =
      LowBody.rivalLaw (lowMass P.theta)
        (activeMass P.theta-activeMass P.theta*P.zeta*powerTail P.M 10 t)
        (partialMass+activeMass P.theta*P.zeta*powerTail P.M 10 t)
        (LowBody.realLowBidLaw πL.1 : Measure ℝ) := by
  change ((Γ.F ⊗ₘ Γ.σ).prod (permLaw 2)).map (jointRow E) = _
  rw [hjoint]
  exact original_exact_low_row E P hd t ht πL πP πA upperBid hupperBid hfloor

end FCAppendix.Affine.Tail04.OriginalPopulation
