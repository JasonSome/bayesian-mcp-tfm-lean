import FCAppendix.Affine.Tail04.SourceGlobalMargins
import FCAppendix.Affine.Tail04.UnusedFiniteCountError

noncomputable section
namespace FCAppendix.Affine.Tail04.CanonicalSourceGlobal
open MeasureTheory ProbabilityTheory Set Classical
open OriginalValues MenuError SourceMenuPopulation SourceMenuIdentity
open RouteMenuStatistics SourceGlobalMargins CanonicalFailure UnusedFocalCountError

def mixture (ω : FiniteLaw Bool) (ξ : ℝ) (lam : Bool→ℝ) (b : ℝ) : CountLaw 2 :=
  FiniteLaw.finiteMix ω (fun reg=> canonicalCount ξ (lam reg) b)

lemma mixture_expect (ω : FiniteLaw Bool) (ξ : ℝ) (lam : Bool→ℝ) (b : ℝ) (f : Fin 3→ℝ) :
    (mixture ω ξ lam b).expect f=ω.expect (fun reg=>(canonicalCount ξ (lam reg) b).expect f) :=
  FiniteLaw.expect_finiteMix ω _ f

lemma mixture_bound (ω : FiniteLaw Bool) (ξ : ℝ) (lam : Bool→ℝ) (b : ℝ)
    (f : Fin 3→ℝ) (C : ℝ) (h : ∀reg,(canonicalCount ξ (lam reg) b).expect f≤ C) :
    (mixture ω ξ lam b).expect f≤ C := by
  rw [mixture_expect]
  exact FiniteLaw.expect_le_const _ h

theorem active_all_routes (P : ValueParameters) {ξ : ℝ}
    (hξ : 0< ξ) (hξh : ξ<1/2) (hθ : P.theta≤ ξ/100)
    (hw : P.w≤ ξ/1000) (hvA : P.vA=11*ξ/(10*P.theta))
    (ω : FiniteLaw Bool) (lam : Bool→ℝ)
    (hnom : ∀reg,(1-ξ)*Central.B ξ≤ lam reg)
    (hlo : ∀reg,multiplierFloor ξ≤ lam reg)
    {v b : ℝ} (hv : P.vA-P.w≤ v) (hb : b∈Icc (0:ℝ) (Central.B ξ)) (k : Fin 3) :
    (mixture ω ξ lam b).expect (statistic (1-2*ξ) v b k)≤ v-Central.B ξ-ξ/40 := by
  have hv100 := (active_value_large P hξ hξh hθ hw hvA).trans hv
  have hv0 : 0< v := by linarith
  have hB : 0< Central.B ξ := by unfold Central.B;linarith
  apply mixture_bound
  intro reg
  fin_cases k
  · change (canonicalCount ξ (lam reg) b).expect (fun _ : Fin 3=>(0:ℝ))≤v-Central.B ξ-ξ/40
    rw [FiniteLaw.expect_const]
    unfold Central.B
    linarith
  · change (canonicalCount ξ (lam reg) b).expect (statistic (1-2*ξ) v b (1:Fin 3))≤v-Central.B ξ-ξ/40
    have hc := canonical_one_large hξ (by linarith : ξ<1) hB hb (hnom reg)
      (by linarith [(multiplierFloor_bounds hξ hξh.le).1]) (hlo reg)
      (large_value_threshold hξ hξh.le hv100)
    linarith [singleton_cost_gap hξ hξh.le]
  · change (canonicalCount ξ (lam reg) b).expect (statistic (1-2*ξ) v b (2:Fin 3))≤v-Central.B ξ-ξ/40
    have hc := canonical_two_all_prices hξ (by linarith : ξ<1) hB hb
      (hnom reg) (hlo reg) hv0
    linarith [broadcast_cost_gap hξ hξh.le hv100]

theorem partial_all_routes (P : ValueParameters) {ξ : ℝ}
    (hξ : 0< ξ) (hξh : ξ<1/2) (hθ : P.theta≤ ξ/100)
    (ω : FiniteLaw Bool) (lam : Bool→ℝ)
    (hnom : ∀reg,(1-ξ)*Central.B ξ≤ lam reg)
    (hlo : ∀reg,multiplierFloor ξ≤ lam reg)
    {b : ℝ} (hb : b∈Icc (0:ℝ) (Central.B ξ)) (k : Fin 3) :
    (mixture ω ξ lam b).expect (statistic (1-2*ξ) 2 b k)≤
      (2-Central.R ξ)*(1-P.theta)-ξ/2 := by
  have hB : 0< Central.B ξ := by unfold Central.B;linarith
  have hB1 : 1≤ Central.B ξ := by unfold Central.B;linarith
  have hbase := partial_singleton_margin P hξ hξh hθ
  apply mixture_bound
  intro reg
  fin_cases k
  · change (canonicalCount ξ (lam reg) b).expect (fun _ : Fin 3=>(0:ℝ))≤(2-Central.R ξ)*(1-P.theta)-ξ/2
    rw [FiniteLaw.expect_const]
    linarith
  · change (canonicalCount ξ (lam reg) b).expect (statistic (1-2*ξ) 2 b (1:Fin 3))≤(2-Central.R ξ)*(1-P.theta)-ξ/2
    have hc := canonical_one_at_partial hξ hξh.le hB1 hb (hnom reg)
    linarith
  · change (canonicalCount ξ (lam reg) b).expect (statistic (1-2*ξ) 2 b (2:Fin 3))≤(2-Central.R ξ)*(1-P.theta)-ξ/2
    have hc := canonical_two_all_prices hξ (by linarith : ξ<1) hB hb
      (hnom reg) (hlo reg) (by norm_num : (0:ℝ)<2)
    have hd := partial_broadcast_canonical_margin P hξ hξh hθ
    nlinarith

theorem failure (ω : FiniteLaw Bool) {ξ : ℝ} (hξ : 0< ξ) (hξ1 : ξ≤1)
    (lam : Bool→ℝ) (hlam : ∀reg,(1-ξ)*Central.B ξ+2*SourceMomentRectangle.γ ξ≤ lam reg)
    {b : ℝ} (hb : b∈Icc (0:ℝ) (Central.B ξ)) :
    (probabilityGap ξ)^2≤1-(mixture ω ξ lam b).success := by
  have he (reg : Bool) : (canonicalCount ξ (lam reg) b).success≤1-(probabilityGap ξ)^2 := by
    have h := canonical_failure (probabilityGap_pos hξ).le
      (source_canonical_probability_gap hξ hξ1 hb (hlam reg))
    linarith
  have h := mixture_bound ω ξ lam b (fun r : Fin 3=>successIndicator r.val) (1-(probabilityGap ξ)^2) he
  change (mixture ω ξ lam b).expect (fun r : Fin 3=>successIndicator r.val)≤1-(probabilityGap ξ)^2 at h
  change (probabilityGap ξ)^2≤1-(mixture ω ξ lam b).expect (fun r : Fin 3=>successIndicator r.val)
  linarith

lemma unused_mixture (Q : PublicScenario.Data) (lam : Bool→ℝ) (b : ℝ) :
    UnusedFiniteCountError.canonicalMixture Q lam b=
      mixture (IndependentCounts.bernoulli Q.θ Q.θ_nonneg Q.θ_le_one) Q.ξ lam b := rfl

end FCAppendix.Affine.Tail04.CanonicalSourceGlobal
