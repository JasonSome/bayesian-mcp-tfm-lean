import FCAppendix.Affine.Hybrid.Native02.PrimitiveInput
import FCAppendix.Existence.R01PayOnceRowIntegration

noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open MeasureTheory ProbabilityTheory Game Bayes LowBody Set Filter Topology Classical
open Existence.Distributional
open scoped BigOperators

lemma measurableEmbedding_activeJointPoint {vlo vhi L U : ℝ} (hL : 0 ≤ L) :
    MeasurableEmbedding (fun x : ActiveValue vlo vhi × ActiveBaseBid L U =>
      (x.1.1, activeBroadcast hL x.2)) := by
  apply (measurable_fst.subtype_val.prodMk
    ((measurable_activeBroadcast hL).comp measurable_snd)).measurableEmbedding
  intro x y hxy
  apply Prod.ext
  · exact Subtype.ext (congrArg Prod.fst hxy)
  · exact Subtype.ext (congrArg (fun p : ℝ × JointAction 2 => p.2.bid) hxy)

namespace PrimitiveInput

lemma lowReal_ae_box (p : PrimitiveInput) (low : ProbabilityMeasure p.Low) :
    ∀ᵐ b ∂p.lowReal low, b ∈ Icc 0 p.d := by
  apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
  exact ae_of_all _ (fun b => b.property)

lemma bidReal_ae_box (p : PrimitiveInput)
    (pi : Law (A := p.Bid) (p.activeValues : Measure p.Value)) :
    ∀ᵐ b ∂p.bidReal pi, b ∈ Icc p.L p.U := by
  apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
  exact ae_of_all _ (fun b => b.property)

theorem finite_reference_exposure_mem (p : PrimitiveInput)
    (pi : Law (A := p.Bid) (p.activeValues : Measure p.Value))
    (b : ℝ) (hb : b ∈ Icc p.L p.U) :
    exposure p.xi (p.h0/reciprocalMean (p.bidReal pi)) b ∈ Icc (0:ℝ) 1 := by
  have hh0 : 0 ≤ p.h0 := by
    dsimp only [h0, qbar]
    have ht := mul_lt_mul_of_pos_left p.qbar_lt_one p.xi_pos
    linarith [p.xi_lt_one]
  exact exposure_mem_of_mean_factor (p.bidReal pi) p.xi_pos p.xi_lt_one p.L_pos
    (p.bidReal_ae_box pi) hb hh0 p.box_lower p.box_upper

theorem source_reference_exposure_mem (p : PrimitiveInput) (A : FrozenActiveFamily p)
    (b : ℝ) (hb : b ∈ Icc p.L p.U) :
    exposure p.xi p.lam b ∈ Icc (0:ℝ) 1 := by
  have ht : Tendsto (fun m => exposure p.xi
      (p.h0/reciprocalMean (p.bidReal (A.joint m))) b) atTop
      (nhds (exposure p.xi p.lam b)) := by
    unfold exposure
    exact (tendsto_const_nhds.sub (A.price_limit.div_const b)).div_const p.xi
  exact isClosed_Icc.mem_of_tendsto ht
    (Eventually.of_forall (fun m => p.finite_reference_exposure_mem (A.joint m) b hb))

def compactSourceUtility (p : PrimitiveInput) (N c : ℕ)
    (low : ProbabilityMeasure p.Low)
    (pi : Law (A := p.Bid) (p.activeValues : Measure p.Value))
    (t : p.Value × p.Bid) : ℝ :=
  ∑ kind : Fin N → Fin 4, (CommonList.iid p.categories N).mass kind *
    ∫ rows : (Fin N → p.Low) × (Fin N → p.Bid),
      activePhysicalPatternPayoff p.xi p.z p.L p.U c kind
        (t.1.1, t.2.1, (fun j => (rows.1 j).1), fun j => (rows.2 j).1)
      ∂(productLaw (rowLaw N low) (rowLaw N (pi.1.map measurable_snd.aemeasurable)) :
        Measure ((Fin N → p.Low) × (Fin N → p.Bid)))

lemma abs_source_physical_box (p : PrimitiveInput) {N : ℕ} (c : ℕ)
    (kind : Fin N → Fin 4) (v b : ℝ) (hb : b ∈ Icc p.L p.U)
    (low active : Fin N → ℝ) (hactive : ∀ j, active j ∈ Icc p.L p.U) :
    |activePhysicalPatternPayoff p.xi p.z p.L p.U c kind (v,b,low,active)| ≤
      |v|+3*p.U := by
  have hbid : |b| ≤ p.U := by rw [abs_of_pos (p.L_pos.trans_le hb.1)]; exact hb.2
  have hbact : ∀ i, activePhysicalActiveBids kind (v,b,low,active) i ∈ Icc p.L p.U := by
    intro ⟨i, hi⟩
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro _
      exact hb
    · intro _
      exact hactive j
  unfold activePhysicalPatternPayoff
  dsimp only
  split_ifs with hg he
  · have heta : |1-2*p.xi| ≤ 1 := abs_le.mpr ⟨by linarith [p.xi_lt_one], by linarith [p.xi_pos]⟩
    exact (abs_sourceOwnerPayoff_activePattern p.xi_pos p.xi_lt_one p.L_pos heta
      c p.z kind hg v _ hbact).trans (by linarith [p.U_pos])
  · have ht := abs_equalPayoff_le p.xi_pos p.xi_lt_one
      (activePatternTemplate c kind).residual₀ (0 : Fin (N+1)) v
      (activePhysicalBids kind (v,b,low,active))
    simp only [activePhysicalBids, Fin.cons_zero] at ht
    exact ht.trans (by linarith [p.U_pos])
  · have ht := abs_purePayoff_le (1-p.xi) v
      (activePhysicalBids kind (v,b,low,active))
      ((activePatternTemplate c kind).selection (1-p.xi)
        (activePhysicalBids kind (v,b,low,active))) (0 : Fin (N+1))
    simp only [activePhysicalBids, Fin.cons_zero] at ht
    have hk : |1-p.xi| ≤ 1 := by
      rw [abs_of_pos (sub_pos.mpr p.xi_lt_one)]
      linarith [p.xi_pos]
    exact ht.trans (by nlinarith [mul_le_mul_of_nonneg_right hk (abs_nonneg b)])

theorem compactSourceUtility_eq_physicalSourceUtility (p : PrimitiveInput)
    (N c : ℕ) (low : ProbabilityMeasure p.Low)
    (pi : Law (A := p.Bid) (p.activeValues : Measure p.Value)) (t : p.Value × p.Bid) :
    p.compactSourceUtility N c low pi t =
      FullContext.physicalSourceUtility N c p.xi p.z p.L p.U
        p.s p.a p.h p.s_pos.le p.a_pos.le p.h_pos.le p.mass
        (p.lowReal low) (p.bidReal pi) t.1.1 t.2.1 := by
  let μc : Measure (Fin N → p.Low) := (rowLaw N low : Measure (Fin N → p.Low))
  let Bc : Measure (Fin N → p.Bid) :=
    (rowLaw N (pi.1.map measurable_snd.aemeasurable) : Measure (Fin N → p.Bid))
  let lowMap : (Fin N → p.Low) → (Fin N → ℝ) := fun r j => (r j).1
  let bidMap : (Fin N → p.Bid) → (Fin N → ℝ) := fun r j => (r j).1
  have hmL : Measurable lowMap := measurable_pi_lambda _
    (fun j => measurable_subtype_coe.comp (measurable_pi_apply j))
  have hmB : Measurable bidMap := measurable_pi_lambda _
    (fun j => measurable_subtype_coe.comp (measurable_pi_apply j))
  have hmapL : μc.map lowMap = Measure.pi (fun _ : Fin N => p.lowReal low) := by
    dsimp only [μc, lowMap, lowReal]
    rw [rowLaw_eq_pi, Measure.pi_map_pi (fun _ => measurable_subtype_coe.aemeasurable)]
  have hmapB : Bc.map bidMap = Measure.pi (fun _ : Fin N => p.bidReal pi) := by
    dsimp only [Bc, bidMap, bidReal]
    rw [rowLaw_eq_pi, Measure.pi_map_pi (fun _ => measurable_subtype_coe.aemeasurable)]
    rfl
  have hmap : (μc.prod Bc).map (Prod.map lowMap bidMap) =
      (Measure.pi (fun _ : Fin N => p.lowReal low)).prod
        (Measure.pi (fun _ : Fin N => p.bidReal pi)) := by
    rw [← Measure.map_prod_map _ _ hmL hmB, hmapL, hmapB]
  have hB : ∀ᵐ b ∂p.bidReal pi, b ∈ Icc p.L p.U := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable measurableSet_Icc).mpr
    exact ae_of_all _ (fun b => b.property)
  have hBvec : ∀ᵐ active : Fin N → ℝ ∂Measure.pi (fun _ : Fin N => p.bidReal pi),
      ∀ j, active j ∈ Icc p.L p.U :=
    ae_all_iff.mpr (fun j =>
      (measurePreserving_eval (fun _ : Fin N => p.bidReal pi) j).quasiMeasurePreserving.ae hB)
  have hcat : categoryLaw p.s p.a p.h p.s_pos.le p.a_pos.le p.h_pos.le p.mass
      (p.lowReal low) = p.categories :=
    categoryLaw_eq_low_law p.s p.a p.h p.s_pos.le p.a_pos.le p.h_pos.le p.mass
      (p.lowReal low) (Measure.dirac (0 : ℝ))
  unfold compactSourceUtility FullContext.physicalSourceUtility
  rw [hcat]
  unfold FiniteLaw.expect
  apply Finset.sum_congr rfl
  intro kind _
  congr 1
  let F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ := fun rows =>
    activePhysicalPatternPayoff p.xi p.z p.L p.U c kind (t.1.1,t.2.1,rows)
  have hF : Measurable F :=
    (measurable_activePhysicalPatternPayoff p.xi_pos p.xi_lt_one p.z p.L p.U c kind).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hbound : ∀ᵐ rows ∂(Measure.pi (fun _ : Fin N => p.lowReal low)).prod
      (Measure.pi (fun _ : Fin N => p.bidReal pi)), ‖F rows‖ ≤ |t.1.1|+3*p.U := by
    have ha := (measurePreserving_snd
      (μ := Measure.pi (fun _ : Fin N => p.lowReal low))
      (ν := Measure.pi (fun _ : Fin N => p.bidReal pi))).quasiMeasurePreserving.ae hBvec
    filter_upwards [ha] with rows hr
    simpa only [F, Real.norm_eq_abs] using
      p.abs_source_physical_box c kind t.1.1 t.2.1 t.2.property rows.1 rows.2 hr
  have hInt : Integrable F ((Measure.pi (fun _ : Fin N => p.lowReal low)).prod
      (Measure.pi (fun _ : Fin N => p.bidReal pi))) :=
    Integrable.of_bound hF.aestronglyMeasurable (|t.1.1|+3*p.U) hbound
  calc
    _ = ∫ rows, F rows ∂((μc.prod Bc).map (Prod.map lowMap bidMap)) := by
      rw [integral_map (hmL.prodMap hmB).aemeasurable hF.aestronglyMeasurable]
      rfl
    _ = ∫ rows, F rows ∂(Measure.pi (fun _ : Fin N => p.lowReal low)).prod
        (Measure.pi (fun _ : Fin N => p.bidReal pi)) := by rw [hmap]
    _ = ∫ low : Fin N → ℝ, ∫ active : Fin N → ℝ, F (low,active)
        ∂Measure.pi (fun _ : Fin N => p.bidReal pi)
        ∂Measure.pi (fun _ : Fin N => p.lowReal low) := integral_prod F hInt
    _ = ∫ active : Fin N → ℝ, ∫ low : Fin N → ℝ, F (low,active)
        ∂Measure.pi (fun _ : Fin N => p.lowReal low)
        ∂Measure.pi (fun _ : Fin N => p.bidReal pi) := integral_integral_swap hInt

theorem compact_source_IC_to_physical (p : PrimitiveInput) (N c : ℕ)
    (low : ProbabilityMeasure p.Low)
    (pi : Law (A := p.Bid) (p.activeValues : Measure p.Value))
    (hIC : ∀ᵐ t ∂(pi.1 : Measure (p.Value × p.Bid)), ∀ b : p.Bid,
      p.compactSourceUtility N c low pi (t.1,b) ≤ p.compactSourceUtility N c low pi t) :
    ∀ᵐ t ∂(pi.1 : Measure (p.Value × p.Bid)), ∀ b : p.Bid,
      FullContext.physicalSourceUtility N c p.xi p.z p.L p.U
        p.s p.a p.h p.s_pos.le p.a_pos.le p.h_pos.le p.mass
        (p.lowReal low) (p.bidReal pi) t.1.1 b.1 ≤
      FullContext.physicalSourceUtility N c p.xi p.z p.L p.U
        p.s p.a p.h p.s_pos.le p.a_pos.le p.h_pos.le p.mass
        (p.lowReal low) (p.bidReal pi) t.1.1 t.2.1 := by
  filter_upwards [hIC] with t ht
  intro b
  simpa only [p.compactSourceUtility_eq_physicalSourceUtility N c low pi] using ht b

end PrimitiveInput

namespace FullContext

theorem native_source_boxed_IC {N c : ℕ} {xi d L U R : ℝ}
    (hxi : 0 < xi) (hxih : xi ≤ 1/2) (z : ℝ)
    (Γ : FiniteGame (N+1) 2 c unitInterval)
    (hA : Γ.A = Schedule.affine 2 (1-2*xi) (by linarith) (by linarith))
    (hg : Γ.g=0) (hseed : Γ.seedLaw=volume)
    (hd : 0 ≤ d) (hL : 0 < L) (hgap : d < (1-xi)*L) (hUR : U < R)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ closedProfiles (N+1) R)
    (hpopgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hμnull : ∀ b, μ {b}=0) (hBnull : ∀ b, B {b}=0)
    (hμ : ∀ᵐ b ∂μ, b ∈ Icc 0 d) (hB : ∀ᵐ b ∂B, b ∈ Icc L U)
    (hrow : (userLaw Γ).map (physicalRow d U)=physicalRivalLaw s a h μ B)
    (v : ℝ) (star : JointAction 2) (hstar : star.bid ∈ Icc L U) (hstar2 : star.routeCount=2)
    (hIC : ∀ b : ℝ, b ∈ Icc L U →
      physicalSourceUtility N c xi z L U s a h hs ha hh hsum μ B v b ≤
      physicalSourceUtility N c xi z L U s a h hs ha hh hsum μ B v star.bid) :
    ∀ (i : Fin (N+1)) (act : JointAction 2), act.bid ∈ Icc L U → act.routeCount=2 →
      (problem (ClosedPolicy.nativeGame (contextPolicy hxi (by linarith) d L U z c μ) Γ R) i).payoff v act ≤
      (problem (ClosedPolicy.nativeGame (contextPolicy hxi (by linarith) d L U z c μ) Γ R) i).payoff v star := by
  intro i act hb hk
  rw [closed_broadcast_payoff_sourceRows hxi hxih z Γ hA hg hseed hd hL hgap hUR
      hfull hpopgap s a h hs ha hh hsum μ B hμnull hBnull hμ hB hrow i v act hb hk,
    closed_broadcast_payoff_sourceRows hxi hxih z Γ hA hg hseed hd hL hgap hUR
      hfull hpopgap s a h hs ha hh hsum μ B hμnull hBnull hμ hB hrow i v star hstar hstar2]
  exact hIC act.bid hb

theorem native_source_boxed_IC_ae {N c : ℕ} {xi d L U R : ℝ}
    (hxi : 0 < xi) (hxih : xi ≤ 1/2) (z : ℝ)
    (Γ : FiniteGame (N+1) 2 c unitInterval)
    (hA : Γ.A = Schedule.affine 2 (1-2*xi) (by linarith) (by linarith))
    (hg : Γ.g=0) (hseed : Γ.seedLaw=volume)
    (hd : 0 ≤ d) (hL : 0 < L) (hgap : d < (1-xi)*L) (hUR : U < R)
    (hfull : ∀ᵐ x ∂userProfileLaw Γ, x ∈ closedProfiles (N+1) R)
    (hpopgap : ∀ᵐ x ∂Γ.F ⊗ₘ Γ.σ, x.2.bid ≤ U ∨ R ≤ x.2.bid)
    (s a h : ℝ) (hs : 0 ≤ s) (ha : 0 ≤ a) (hh : 0 ≤ h) (hsum : s+a+h=1)
    (μ B : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure B]
    (hμnull : ∀ b, μ {b}=0) (hBnull : ∀ b, B {b}=0)
    (hμ : ∀ᵐ b ∂μ, b ∈ Icc 0 d) (hB : ∀ᵐ b ∂B, b ∈ Icc L U)
    (hrow : (userLaw Γ).map (physicalRow d U)=physicalRivalLaw s a h μ B)
    (PA : Measure (ℝ × JointAction 2))
    (hshape : ∀ᵐ x ∂PA, x.2.bid ∈ Icc L U ∧ x.2.routeCount=2)
    (hIC : ∀ᵐ x ∂PA, ∀ b : ℝ, b ∈ Icc L U →
      physicalSourceUtility N c xi z L U s a h hs ha hh hsum μ B x.1 b ≤
      physicalSourceUtility N c xi z L U s a h hs ha hh hsum μ B x.1 x.2.bid) :
    ∀ᵐ x ∂PA, ∀ (i : Fin (N+1)) (act : JointAction 2),
      act.bid ∈ Icc L U → act.routeCount=2 →
      (problem (ClosedPolicy.nativeGame (contextPolicy hxi (by linarith) d L U z c μ) Γ R) i).payoff x.1 act ≤
      (problem (ClosedPolicy.nativeGame (contextPolicy hxi (by linarith) d L U z c μ) Γ R) i).payoff x.1 x.2 := by
  filter_upwards [hshape, hIC] with x hx hICx
  exact native_source_boxed_IC hxi hxih z Γ hA hg hseed hd hL hgap hUR hfull hpopgap
    s a h hs ha hh hsum μ B hμnull hBnull hμ hB hrow x.1 x.2 hx.1 hx.2 hICx

end FullContext
end FCAppendix.Affine.Hybrid.Native02
