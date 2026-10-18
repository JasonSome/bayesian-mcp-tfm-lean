import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace FCAppendix.Exclusive.Existence

open Set Filter Topology
open scoped NNReal BoundedContinuousFunction

theorem strongDecrease_inverse_bound {f : ℝ → ℝ} {lo hi m x y : ℝ}
    (_hm : 0 < m)
    (hdec : ∀ a ∈ Icc lo hi, ∀ b ∈ Icc lo hi, a ≤ b →
      m * (b-a) ≤ f a-f b)
    (hx : x ∈ Icc lo hi) (hy : y ∈ Icc lo hi) :
    m * |x-y| ≤ |f x-f y| := by
  rcases le_total x y with hxy | hyx
  · have h := hdec x hx y hy hxy
    rw [abs_of_nonpos (sub_nonpos.mpr hxy)]
    have habs := le_abs_self (f x-f y)
    nlinarith
  · have h := hdec y hy x hx hyx
    rw [abs_of_nonneg (sub_nonneg.mpr hyx)]
    have habs := neg_le_abs (f x-f y)
    nlinarith

structure ScoreData (Θ V : Type*) [PseudoMetricSpace Θ] [PseudoMetricSpace V]
    (lo hi m : ℝ) where
  score : Θ → V → ℝ → ℝ
  band_nonempty : lo ≤ hi
  curvature_pos : 0 < m
  continuous_bid : ∀ θ v, ContinuousOn (score θ v) (Icc lo hi)
  inward_left : ∀ θ v, 0 < score θ v lo
  inward_right : ∀ θ v, score θ v hi < 0
  decrease : ∀ θ v x, x ∈ Icc lo hi → ∀ y, y ∈ Icc lo hi → x ≤ y →
    m*(y-x) ≤ score θ v x-score θ v y

namespace ScoreData

variable {Θ V : Type*} [PseudoMetricSpace Θ] [PseudoMetricSpace V]
  {lo hi m : ℝ} (D : ScoreData Θ V lo hi m)

theorem exists_root (θ : Θ) (v : V) :
    ∃ z ∈ Ioo lo hi, D.score θ v z = 0 := by
  obtain ⟨z, hz, hzero⟩ := intermediate_value_Icc' D.band_nonempty
    (D.continuous_bid θ v) ⟨(D.inward_right θ v).le, (D.inward_left θ v).le⟩
  have hl : lo < z := by
    by_contra h
    have he : z = lo := le_antisymm (not_lt.mp h) hz.1
    have hzero' : D.score θ v lo = 0 := by simpa only [he] using hzero
    linarith [D.inward_left θ v]
  have hh : z < hi := by
    by_contra h
    have he : z = hi := le_antisymm hz.2 (not_lt.mp h)
    have hzero' : D.score θ v hi = 0 := by simpa only [he] using hzero
    linarith [D.inward_right θ v]
  exact ⟨z, ⟨hl, hh⟩, hzero⟩

noncomputable def reply (θ : Θ) (v : V) : ℝ := (D.exists_root θ v).choose

theorem reply_mem (θ : Θ) (v : V) : D.reply θ v ∈ Ioo lo hi :=
  (D.exists_root θ v).choose_spec.1

theorem score_reply (θ : Θ) (v : V) : D.score θ v (D.reply θ v) = 0 :=
  (D.exists_root θ v).choose_spec.2

theorem root_unique (θ : Θ) (v : V) {z : ℝ}
    (hz : z ∈ Icc lo hi) (hzero : D.score θ v z = 0) : z = D.reply θ v := by
  have h := strongDecrease_inverse_bound D.curvature_pos (D.decrease θ v)
    hz (Ioo_subset_Icc_self (D.reply_mem θ v))
  rw [hzero, D.score_reply, sub_self, abs_zero] at h
  have hdist : |z-D.reply θ v| = 0 := by
    have := abs_nonneg (z-D.reply θ v)
    nlinarith [D.curvature_pos]
  exact sub_eq_zero.mp (abs_eq_zero.mp hdist)

theorem reply_stability (θ η : Θ) (v w : V) :
    m * |D.reply θ v-D.reply η w| ≤
      |D.score θ v (D.reply η w)-D.score η w (D.reply η w)| := by
  have h := strongDecrease_inverse_bound D.curvature_pos (D.decrease θ v)
    (Ioo_subset_Icc_self (D.reply_mem θ v))
    (Ioo_subset_Icc_self (D.reply_mem η w))
  simpa only [D.score_reply, zero_sub, abs_neg, sub_zero] using h

theorem reply_lipschitz_type (θ : Θ) (L : ℝ≥0)
    (hL : ∀ v w z, z ∈ Icc lo hi →
      |D.score θ v z-D.score θ w z| ≤ m*(L:ℝ)*dist v w) :
    LipschitzWith L (D.reply θ) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  have h := (D.reply_stability θ θ v w).trans
    (hL v w _ (Ioo_subset_Icc_self (D.reply_mem θ w)))
  rw [Real.dist_eq]
  nlinarith [D.curvature_pos]

theorem reply_strictMono [Preorder V] (θ : Θ)
    (hinc : ∀ v w, v < w → ∀ z ∈ Icc lo hi,
      D.score θ v z < D.score θ w z) : StrictMono (D.reply θ) := by
  intro v w hvw
  have hi := hinc v w hvw _ (Ioo_subset_Icc_self (D.reply_mem θ v))
  rw [D.score_reply] at hi
  by_contra hnot
  have hle : D.reply θ w ≤ D.reply θ v := not_lt.mp hnot
  have hd := D.decrease θ w _ (Ioo_subset_Icc_self (D.reply_mem θ w))
    _ (Ioo_subset_Icc_self (D.reply_mem θ v)) hle
  rw [D.score_reply] at hd
  have hp := mul_nonneg D.curvature_pos.le (sub_nonneg.mpr hle)
  linarith

theorem reply_maximizes (θ : Θ) (v : V) (U : ℝ → ℝ)
    (hU : ∀ z ∈ Icc lo hi, HasDerivAt U (D.score θ v z) z)
    (z : ℝ) (hz : z ∈ Icc lo hi) : U z ≤ U (D.reply θ v) := by
  let b := D.reply θ v
  have hb : b ∈ Icc lo hi := Ioo_subset_Icc_self (D.reply_mem θ v)
  have hc : ContinuousOn U (Icc lo hi) := fun x hx => (hU x hx).continuousAt.continuousWithinAt
  rcases le_total z b with hzb | hbz
  · have hsub : Icc lo b ⊆ Icc lo hi := Icc_subset_Icc_right hb.2
    have hmono := monotoneOn_of_deriv_nonneg (convex_Icc lo b) (hc.mono hsub)
      (fun x hx => (hU x (hsub (interior_subset hx))).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        have hx' := interior_subset hx
        rw [(hU x (hsub hx')).deriv]
        have hh := D.decrease θ v x (hsub hx') b hb hx'.2
        have hm := mul_nonneg D.curvature_pos.le (sub_nonneg.mpr hx'.2)
        have hzero : D.score θ v b = 0 := D.score_reply θ v
        linarith)
    exact hmono ⟨hz.1, hzb⟩ ⟨hb.1, le_rfl⟩ hzb
  · have hsub : Icc b hi ⊆ Icc lo hi := Icc_subset_Icc_left hb.1
    have hanti := antitoneOn_of_deriv_nonpos (convex_Icc b hi) (hc.mono hsub)
      (fun x hx => (hU x (hsub (interior_subset hx))).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        have hx' := interior_subset hx
        rw [(hU x (hsub hx')).deriv]
        have hh := D.decrease θ v b hb x (hsub hx') hx'.1
        have hm := mul_nonneg D.curvature_pos.le (sub_nonneg.mpr hx'.1)
        have hzero : D.score θ v b = 0 := D.score_reply θ v
        linarith)
    exact hanti ⟨le_rfl, hb.2⟩ ⟨hbz, hz.2⟩ hbz

end ScoreData

def bidBand (V : Type*) [TopologicalSpace V] (lo hi : ℝ) : Set (V →ᵇ ℝ) :=
  {f | ∀ v, f v ∈ Icc lo hi}

theorem isClosed_bidBand (V : Type*) [TopologicalSpace V] (lo hi : ℝ) :
    IsClosed (bidBand V lo hi) := by
  have he : bidBand V lo hi = ⋂ v : V, {f : V →ᵇ ℝ | f v ∈ Icc lo hi} := by
    ext f
    simp only [bidBand, mem_setOf_eq, mem_iInter]
  rw [he]
  exact isClosed_iInter fun v => isClosed_Icc.preimage
    (BoundedContinuousFunction.lipschitz_eval_const v).continuous

section FixedPoint

variable {V : Type*} [PseudoMetricSpace V] {lo hi m : ℝ}

instance : CompleteSpace (bidBand V lo hi) :=
  (isClosed_bidBand V lo hi).completeSpace_coe

theorem bidBand_nonempty (h : lo ≤ hi) : Nonempty (bidBand V lo hi) :=
  ⟨⟨BoundedContinuousFunction.const V lo, fun _ => ⟨le_rfl, h⟩⟩⟩

variable (D : ScoreData (bidBand V lo hi) V lo hi m)
  (L : ℝ≥0)
  (hL : ∀ θ v w z, z ∈ Icc lo hi →
    |D.score θ v z-D.score θ w z| ≤ m*(L:ℝ)*dist v w)

noncomputable def response (θ : bidBand V lo hi) : bidBand V lo hi :=
  ⟨BoundedContinuousFunction.mkOfBound
    ⟨D.reply θ, (D.reply_lipschitz_type θ L (hL θ)).continuous⟩
    (hi-lo) (fun v w => by
      change dist (D.reply θ v) (D.reply θ w) ≤ hi-lo
      rw [Real.dist_eq, abs_le]
      have hv := D.reply_mem θ v
      have hw := D.reply_mem θ w
      constructor <;> linarith only [hv.1, hv.2, hw.1, hw.2]),
    fun v => Ioo_subset_Icc_self (D.reply_mem θ v)⟩

theorem response_apply (θ : bidBand V lo hi) (v : V) :
    (response D L hL θ).val v = D.reply θ v := rfl

theorem response_contracts (q : ℝ≥0) (hq : q < 1)
    (hparam : ∀ θ η v z, z ∈ Icc lo hi →
      |D.score θ v z-D.score η v z| ≤ m*(q:ℝ)*dist θ η) :
    ContractingWith q (response D L hL) := by
  refine ⟨hq, LipschitzWith.of_dist_le_mul fun θ η => ?_⟩
  change dist (response D L hL θ).val (response D L hL η).val ≤ _
  apply (BoundedContinuousFunction.dist_le (mul_nonneg q.2 dist_nonneg)).mpr
  intro v
  rw [response_apply, response_apply, Real.dist_eq]
  have h := (D.reply_stability θ η v v).trans
    (hparam θ η v _ (Ioo_subset_Icc_self (D.reply_mem η v)))
  rw [mul_assoc] at h
  exact (mul_le_mul_iff_right₀ D.curvature_pos).mp h

include L hL

theorem exists_unique_pure_stationary (q : ℝ≥0) (hq : q < 1)
    (hparam : ∀ θ η v z, z ∈ Icc lo hi →
      |D.score θ v z-D.score η v z| ≤ m*(q:ℝ)*dist θ η) :
    ∃! β : bidBand V lo hi, ∀ v, D.score β v (β.val v) = 0 := by
  letI := bidBand_nonempty (V := V) D.band_nonempty
  let T := response D L hL
  have hc : ContractingWith q T := response_contracts D L hL q hq hparam
  let β := hc.fixedPoint T
  have hfix : T β = β := hc.fixedPoint_isFixedPt
  have hβ (v : V) : D.score β v (β.val v) = 0 := by
    have he := congrArg (fun f : bidBand V lo hi => f.val v) hfix
    change D.reply β v = β.val v at he
    rw [← he]
    exact D.score_reply β v
  refine ⟨β, hβ, ?_⟩
  intro γ hγ
  have hγfix : T γ = γ := by
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro v
    exact (D.root_unique γ v (γ.property v) (hγ v)).symm
  exact hc.fixedPoint_unique hγfix

end FixedPoint

end FCAppendix.Exclusive.Existence
