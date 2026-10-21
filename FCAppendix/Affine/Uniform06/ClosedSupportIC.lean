import FCAppendix.Affine.Uniform06.RankRent
import FCAppendix.Affine.Uniform06.SupportIntervalDomination
import Mathlib.MeasureTheory.Measure.Support

noncomputable section
namespace FCAppendix.Affine.Uniform06.Rank

open MeasureTheory Set Filter Topology

def closedUsedSupport (μ : Measure ℝ) : Set ℝ := μ.support

theorem closedUsedSupport_isClosed (μ : Measure ℝ) : IsClosed (closedUsedSupport μ) :=
  Measure.isClosed_support

theorem closedUsedSupport_full (μ : Measure ℝ) :
    ∀ᵐ b ∂μ, b ∈ closedUsedSupport μ := Measure.support_mem_ae

theorem rank_IC_pushforward
    {Ω : Type*} [MeasurableSpace Ω] (Γ : Measure Ω)
    (V B : Ω → ℝ) (hB : Measurable B) (μ : Measure ℝ)
    (hmap : Γ.map B=μ) (M ℓ cap S D : ℝ → ℝ) (η : ℝ)
    (hM : Continuous M) (hℓ : Continuous ℓ) (hcap : Continuous cap)
    (hS : ContinuousOn S (Ioi 0)) (hD : ContinuousOn D (Ioi 0))
    (hrank : ∀ᵐ ω ∂Γ, M (B ω)=V ω)
    (hIC : ∀ᵐ ω ∂Γ, ∀ a : ℝ, ℓ (V ω) ≤ a → a ≤ cap (V ω) →
      payoff η (V ω) a (S a) (D a) ≤
        payoff η (V ω) (B ω) (S (B ω)) (D (B ω))) :
    ∀ᵐ b ∂μ, 0 < b → ∀ a : ℝ, 0 < a → ℓ (M b) < a → a < cap (M b) →
      payoff η (M b) a (S a) (D a) ≤ payoff η (M b) b (S b) (D b) := by
  have hcommon : ∀ᵐ ω ∂Γ, 0 < B ω → ∀ a : ℝ, 0 < a →
      ℓ (M (B ω)) < a → a < cap (M (B ω)) →
      payoff η (M (B ω)) a (S a) (D a) ≤
        payoff η (M (B ω)) (B ω) (S (B ω)) (D (B ω)) := by
    filter_upwards [hrank,hIC] with ω hr hi
    intro _ a _ hl hu
    rw [hr] at hl hu ⊢
    exact hi a hl.le hu.le
  let Bad : Set ℝ := {b | 0 < b ∧ ∃ a : ℝ, 0 < a ∧ ℓ (M b) < a ∧ a < cap (M b) ∧
    payoff η (M b) b (S b) (D b) < payoff η (M b) a (S a) (D a)}
  have hBad : IsOpen Bad := by
    apply isOpen_iff_mem_nhds.mpr
    intro b hb
    obtain ⟨hb0,a,ha0,hlo,hhi,hgain⟩ := hb
    have hSb : ContinuousAt S b := (hS b hb0).continuousAt (Ioi_mem_nhds hb0)
    have hDb : ContinuousAt D b := (hD b hb0).continuousAt (Ioi_mem_nhds hb0)
    have hg : ContinuousAt (fun x => payoff η (M x) a (S a) (D a)-
        payoff η (M x) x (S x) (D x)) b := by
      unfold payoff
      fun_prop
    filter_upwards [Ioi_mem_nhds hb0,
      (hℓ.comp hM).continuousAt.eventually_lt_const hlo,
      (hcap.comp hM).continuousAt.eventually_const_lt hhi,
      hg.eventually_const_lt (sub_pos.mpr hgain)] with x hx hxl hxu hxg
    exact ⟨hx,a,ha0,hxl,hxu,sub_pos.mp hxg⟩
  have hgood : MeasurableSet {b | 0 < b → ∀ a : ℝ, 0 < a →
      ℓ (M b) < a → a < cap (M b) →
      payoff η (M b) a (S a) (D a) ≤ payoff η (M b) b (S b) (D b)} := by
    have he : {b | 0 < b → ∀ a : ℝ, 0 < a → ℓ (M b) < a → a < cap (M b) →
        payoff η (M b) a (S a) (D a) ≤ payoff η (M b) b (S b) (D b)} = Badᶜ := by
      ext b
      simp only [Bad,mem_setOf_eq,mem_compl_iff,not_exists,not_and,not_lt]
    rw [he]
    exact hBad.isClosed_compl.measurableSet
  rw [← hmap]
  exact (ae_map_iff hB.aemeasurable hgood).mpr hcommon

theorem IC_on_closed_used_support
    (μ : Measure ℝ) (M ℓ cap S D : ℝ → ℝ) (η : ℝ)
    (hM : Continuous M) (hℓ : Continuous ℓ) (hcap : Continuous cap)
    (hS : ContinuousOn S (Ioi 0)) (hD : ContinuousOn D (Ioi 0))
    (hIC : ∀ᵐ b ∂μ, 0 < b → ∀ a : ℝ, 0 < a → ℓ (M b) < a → a < cap (M b) →
      payoff η (M b) a (S a) (D a) ≤ payoff η (M b) b (S b) (D b)) :
    ∀ b ∈ closedUsedSupport μ, 0 < b → ∀ a : ℝ, 0 < a →
      ℓ (M b) < a → a < cap (M b) →
        payoff η (M b) a (S a) (D a) ≤ payoff η (M b) b (S b) (D b) := by
  intro b hb hb0 a ha0 hlo hhi
  by_contra hbad
  have hgain : 0 < payoff η (M b) a (S a) (D a)-
      payoff η (M b) b (S b) (D b) := sub_pos.mpr (lt_of_not_ge hbad)
  let A : Set ℝ := {x | 0 < x ∧ ℓ (M x) < a ∧ a < cap (M x) ∧
    0 < payoff η (M x) a (S a) (D a)-payoff η (M x) x (S x) (D x)}
  have hSb : ContinuousAt S b := (hS b hb0).continuousAt (Ioi_mem_nhds hb0)
  have hDb : ContinuousAt D b := (hD b hb0).continuousAt (Ioi_mem_nhds hb0)
  have hcGain : ContinuousAt (fun x => payoff η (M x) a (S a) (D a)-
      payoff η (M x) x (S x) (D x)) b := by
    unfold payoff
    fun_prop
  have hnear : A ∈ 𝓝 b := Filter.inter_mem (Ioi_mem_nhds hb0)
    (((hℓ.comp hM).continuousAt.eventually_lt_const hlo).and
      (((hcap.comp hM).continuousAt.eventually_const_lt hhi).and
        (hcGain.eventually_const_lt hgain)))
  have hmass : 0 < μ A := (Measure.mem_support_iff_forall b).mp hb A hnear
  have hz : μ A=0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hIC] with x hx
    rintro ⟨hx0,h₁,h₂,h₃⟩
    exact not_lt_of_ge (sub_nonpos.mpr (hx hx0 a ha0 h₁ h₂)) h₃
  rw [hz] at hmass
  exact (lt_irrefl 0) hmass

theorem strict_legal_bid_neighborhood {ℓ u b : ℝ} (hl : ℓ < b) (hu : b < u) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : ℝ, |a-b| < δ → ℓ < a ∧ a < u := by
  refine ⟨min (b-ℓ) (u-b),lt_min (sub_pos.mpr hl) (sub_pos.mpr hu),?_⟩
  intro a ha
  have hh := abs_lt.mp ha
  have h₁ := min_le_left (b-ℓ) (u-b)
  have h₂ := min_le_right (b-ℓ) (u-b)
  constructor <;> linarith

theorem closed_support_IC_increment
    (μ : Measure ℝ) (M ℓ cap S D : ℝ → ℝ) (η : ℝ)
    (hM : Continuous M) (hℓ : Continuous ℓ) (hcap : Continuous cap)
    (hS : ContinuousOn S (Ioi 0)) (hD : ContinuousOn D (Ioi 0))
    (hIC : ∀ᵐ b ∂μ, 0 < b → ∀ a : ℝ, 0 < a → ℓ (M b) < a → a < cap (M b) →
      payoff η (M b) a (S a) (D a) ≤ payoff η (M b) b (S b) (D b))
    {a : ℝ} (ha : a ∈ closedUsedSupport μ) (ha0 : 0 < a)
    (hl : ℓ (M a) < a) (hu : a < cap (M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ b : ℝ, a ≤ b → b-a < δ →
      (M a-b)*(S b-S a) ≤ (b-a)*(S a+η*D a)+η*b*(D b-D a) := by
  obtain ⟨δ,hδ,hlegal⟩ := strict_legal_bid_neighborhood hl hu
  refine ⟨δ,hδ,?_⟩
  intro b hab hsmall
  have hlegal' := hlegal b (by rwa [abs_of_nonneg (sub_nonneg.mpr hab)])
  exact IC_increment_upper (IC_on_closed_used_support μ M ℓ cap S D η
    hM hℓ hcap hS hD hIC a ha ha0 b (ha0.trans_le hab) hlegal'.1 hlegal'.2)

end FCAppendix.Affine.Uniform06.Rank
