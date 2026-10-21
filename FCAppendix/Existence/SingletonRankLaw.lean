import FCAppendix.Existence.SingletonGame
import FCAppendix.Existence.SingletonPrimitives
import FCAppendix.Finite.ReceiptBounds

noncomputable section
namespace FCAppendix.Bayes.SingletonConstruction
open MeasureTheory ProbabilityTheory Game Set Filter

def positiveBidMeasure (F : Measure ℝ) (g : ℝ) (b : ℝ → ℝ) : Measure ℝ :=
  (F.restrict (Ioi g)).map (fun v => max (b (v-g)) 0)

instance positiveBidMeasure_finite (F : Measure ℝ) [IsFiniteMeasure F] (g : ℝ) (b : ℝ → ℝ) :
    IsFiniteMeasure (positiveBidMeasure F g b) := by unfold positiveBidMeasure; infer_instance

theorem positiveBidMeasure_eq_net_map (F : Measure ℝ) (g : ℝ) (b : ℝ → ℝ)
    (hb : Measurable b) (hpos : ∀ w, 0 ≤ b w) :
    positiveBidMeasure F g b=(Existence.Singleton.positiveNetLaw F g).map b := by
  have hm : Measurable (fun v : ℝ => v-g) := measurable_id.sub_const g
  rw [Existence.Singleton.positiveNetLaw,Measure.map_map hb hm]
  unfold positiveBidMeasure
  apply Measure.map_congr
  exact ae_of_all _ fun v => max_eq_left (hpos (v-g))

variable {m n c : ℕ} (hn : 0<n) (F : Measure ℝ) [IsProbabilityMeasure F]
    (b : ℝ → ℝ) (hb : Measurable b) (A G : Schedule n) (g : ℝ) (hg : 0 ≤ g)

local notation "Gamma" => singletonGame m n c hn F b hb A G g hg

theorem singletonGame_action_routes :
    ∀ᵐ x ∂((Gamma).F ⊗ₘ (Gamma).σ), x.2.routeCount ≤ 1 := by
  rw [singletonGame_value_action_law hn F b hb A G g hg]
  apply (ae_map_iff (measurable_id.prodMk (measurable_pureAction n hn g b hb)).aemeasurable
    (measurableSet_le ((measurable_routeCount n).comp measurable_snd) measurable_const)).mpr
  exact ae_of_all _ (pureAction_route_le_one hn b g)

theorem singletonGame_contact_measure (j : Fin n) (B : Set ℝ) (hB : MeasurableSet B) :
    userLaw Gamma {d | j ∈ firstK d.2 d.1.2.routeCount ∧ d.1.2.bid ∈ B} =
      positiveBidMeasure F g b B * (permLaw n) {tau | j ∈ firstK tau 1} := by
  let E : Set (ℝ × JointAction n) := {x | x.2.routeCount=1 ∧ x.2.bid ∈ B}
  let R : Set (Equiv.Perm (Fin n)) := {tau | j ∈ firstK tau 1}
  have hE : MeasurableSet E :=
    (measurableSet_eq_fun ((measurable_routeCount n).comp measurable_snd) measurable_const).inter
      (((measurable_bid n).comp measurable_snd) hB)
  have hpair : Measurable (fun v => (v,pureAction n hn g b v)) :=
    measurable_id.prodMk (measurable_pureAction n hn g b hb)
  have hbid : Measurable (fun v : ℝ => max (b (v-g)) 0) :=
    (hb.comp (measurable_id.sub_const g)).max measurable_const
  have heq : ((Gamma).F ⊗ₘ (Gamma).σ) E=positiveBidMeasure F g b B := by
    rw [singletonGame_value_action_law hn F b hb A G g hg,Measure.map_apply hpair hE,
      positiveBidMeasure,Measure.map_apply hbid hB,Measure.restrict_apply (hbid hB)]
    congr 1
    ext v
    by_cases hv : g<v
    · simp [E,pureAction,hv]
    · simp [E,pureAction,hv,Interim.abstain]
  have hr : ∀ᵐ d ∂userLaw Gamma, d.1.2.routeCount ≤ 1 :=
    (measurePreserving_fst (μ:=(Gamma).F ⊗ₘ (Gamma).σ) (ν:=permLaw n)).quasiMeasurePreserving.ae
      (singletonGame_action_routes hn F b hb A G g hg)
  have hcongr : {d : UserDraw n | j ∈ firstK d.2 d.1.2.routeCount ∧ d.1.2.bid ∈ B} =ᵐ[userLaw Gamma] E ×ˢ R := by
    filter_upwards [hr] with d hd
    change (_ ∧ _) = ((_ ∧ _) ∧ _)
    apply propext
    rcases Nat.eq_zero_or_pos d.1.2.routeCount with hz | hp
    · simp [hz,mem_firstK]
    · have hone : d.1.2.routeCount=1 := by omega
      simp only [hone,true_and]
      exact and_comm
  rw [measure_congr hcongr,userLaw,Measure.prod_prod,heq]

theorem singletonGame_alphaGt (j : Fin n) (y : ℝ) :
    alphaGt Gamma j y=(positiveBidMeasure F g b).real (Ioi y)/(n:ℝ) := by
  have he := congrArg ENNReal.toReal (singletonGame_contact_measure (m:=m) (c:=c) hn F b hb A G g hg j (Ioi y) measurableSet_Ioi)
  rw [ENNReal.toReal_mul] at he
  change alphaGt Gamma j y=(positiveBidMeasure F g b).real (Ioi y)*
    (permLaw n).real {tau | j ∈ firstK tau 1} at he
  rw [permLaw_mem_firstK n 1 hn hn j,Nat.cast_one,mul_one_div] at he
  exact he

theorem singletonGame_visible_atomless [NullSingletonClass (positiveBidMeasure F g b)] :
    VisibleAtomless Gamma := by
  intro j y
  change userLaw Gamma {d | j ∈ firstK d.2 d.1.2.routeCount ∧ d.1.2.bid ∈ ({y}:Set ℝ)}=0
  rw [singletonGame_contact_measure (m:=m) (c:=c) hn F b hb A G g hg j {y} (measurableSet_singleton y),measure_singleton,zero_mul]

end FCAppendix.Bayes.SingletonConstruction
