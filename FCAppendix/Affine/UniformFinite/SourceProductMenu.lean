import FCAppendix.Affine.UniformFinite.EqualIdentification
import FCAppendix.Affine.UniformFinite.GuardedPayoffContinuity
import FCAppendix.Affine.UniformFinite.WeightedTargetBounds
import FCAppendix.Affine.UniformFinite.ObservationTransport
import FCAppendix.Affine.UniformFinite.NumericInterims

noncomputable section
namespace FCAppendix.Affine.UniformFinite
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

namespace Source
open Uniform05 ClippedResidual
open WeightedSampling (Path pathLaw finalSet totalWeight)

theorem residual_fraction_tolerance {M : ℕ} (i : Row) (row : CountRow M)
    (hM : 0 < M) {δ : ℝ} (_hδ0 : 0 ≤ δ) (hδ : δ ≤ commonGuardMargin i)
    (hc : |(Uniform07.capacity M : ℝ)/M-rho| ≤ δ)
    (hN : |(row.lower.card : ℝ)/M-t i| ≤ δ)
    (j : Fin 2) (hH : |(upperCount row j : ℝ)/M-(1-t i)/2| ≤ δ) :
    |(residual row j : ℝ)/M-meanResidual i| ≤ 2*δ := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have heq := (residual_fraction_control i row hM (hc.trans hδ) (hN.trans hδ)
    j (hH.trans hδ)).1
  have hmean : rho-(1-t i)/2 = meanResidual i := residual_mean_identity i
  have hHc : upperCount row j ≤ Uniform07.capacity M := by
    have hq := meanResidual_pos i
    have he := commonGuardMargin_bounds i
    obtain ⟨hcL,hcR⟩ := abs_le.mp hc
    obtain ⟨hhL,hhR⟩ := abs_le.mp hH
    have hdiff : (upperCount row j : ℝ)/M ≤ (Uniform07.capacity M : ℝ)/M := by
      linarith
    exact_mod_cast ((div_le_div_iff_of_pos_right hMr).mp hdiff)
  rw [heq, Nat.cast_sub hHc, sub_div]
  obtain ⟨hcL,hcR⟩ := abs_le.mp hc
  obtain ⟨hhL,hhR⟩ := abs_le.mp hH
  rw [abs_le]
  constructor <;> linarith

theorem count_tolerance {M : ℕ} (i : Row) (row : CountRow M)
    (hM : 0 < M) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ commonGuardMargin i)
    (hc : |(Uniform07.capacity M : ℝ)/M-rho| ≤ δ)
    (hN : |(row.lower.card : ℝ)/M-t i| ≤ δ)
    (h0 : |(row.upper0 : ℝ)/M-(1-t i)/2| ≤ δ)
    (h1 : |(row.upper1 : ℝ)/M-(1-t i)/2| ≤ δ) :
    |(small row : ℝ)/M-meanResidual i| ≤ 2*δ ∧ (imbalance row : ℝ)/M ≤ 4*δ := by
  have hr0 := residual_fraction_tolerance i row hM hδ0 hδ hc hN 0
    (by simpa [upperCount] using h0)
  have hr1 := residual_fraction_tolerance i row hM hδ0 hδ hc hN 1
    (by simpa [upperCount] using h1)
  have hs : |(small row : ℝ)/M-meanResidual i| ≤ 2*δ := by
    by_cases h : residual row 0 ≤ residual row 1
    · simpa [small, Nat.min_eq_left h] using hr0
    · simpa [small, Nat.min_eq_right (le_of_not_ge h)] using hr1
  refine ⟨hs, ?_⟩
  have hlarge : |(large row : ℝ)/M-meanResidual i| ≤ 2*δ := by
    by_cases h : residual row 0 ≤ residual row 1
    · simpa [large, Nat.max_eq_right h] using hr1
    · simpa [large, Nat.max_eq_left (le_of_not_ge h)] using hr0
  have hsl : small row ≤ large row := by unfold small large; omega
  rw [imbalance, Nat.cast_sub hsl, sub_div]
  linarith [(abs_le.mp hs).1, (abs_le.mp hlarge).2]

def centralDemand {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (row : CountRow M) (b : Fin M → ℝ) : ℝ :=
  ∑ a, exposure (xi i) G.multiplier (lowerBids row b a)

theorem finite_root_distance {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ξ U lo L z d Q : ℝ} (b : ι → ℝ) (E : Finset ι)
    (hξ : 0 < ξ) (hξ1 : ξ < 1) (hU : 0 < U) (hlo : 0 < lo)
    (hg : (1-ξ)*U ≤ lo) (hb : ∀ a, b a ≤ U)
    (hL : lo ≤ L) (hz : lo ≤ z)
    (hroot : remainingDemand ξ b E z = d)
    (hQ : 0 < Q) (hd : Q ≤ d) (hF : Q ≤ remainingDemand ξ b E L) :
    |z-L| ≤ ξ*U/Q*|remainingDemand ξ b E L-d| := by
  have hξU : 0 < ξ*U := mul_pos hξ hU
  by_cases h : L ≤ z
  · have hh := remainingDemand_drop b E hξ hξ1 hU hlo hg hL h hb
    rw [hroot] at hh
    have hdQ := mul_le_mul_of_nonneg_left hd (div_nonneg (sub_nonneg.mpr h) hξU.le)
    have herr := le_abs_self (remainingDemand ξ b E L-d)
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hmul := mul_le_mul_of_nonneg_right (hdQ.trans hh |>.trans herr) hξU.le
    have hc : ((z-L)/(ξ*U)*Q)*(ξ*U) = (z-L)*Q := by field_simp [hξU.ne']
    rw [hc] at hmul
    have he : z-L ≤ (ξ*U*|remainingDemand ξ b E L-d|)/Q :=
      (le_div_iff₀ hQ).mpr (by simpa only [mul_comm] using hmul)
    convert! he using 1; ring
  · have h' := le_of_not_ge h
    have hh := remainingDemand_drop b E hξ hξ1 hU hlo hg hz h' hb
    rw [hroot] at hh
    have hFQ := mul_le_mul_of_nonneg_left hF (div_nonneg (sub_nonneg.mpr h') hξU.le)
    have herr := neg_le_abs (remainingDemand ξ b E L-d)
    rw [abs_of_nonpos (sub_nonpos.mpr h'), neg_sub]
    have hmul := mul_le_mul_of_nonneg_right (hFQ.trans hh) hξU.le
    have hc : ((L-z)/(ξ*U)*Q)*(ξ*U) = (L-z)*Q := by field_simp [hξU.ne']
    rw [hc] at hmul
    have he : (L-z)*Q ≤ (ξ*U)*|remainingDemand ξ b E L-d| := by
      have ha := mul_le_mul_of_nonneg_left herr hξU.le
      nlinarith
    have he' := (le_div_iff₀ hQ).mpr he
    convert! he' using 1; ring

theorem guarded_path_root_distance {M : ℕ} [NeZero M]
    (i : Row) (G : RestrictedLaw i) (row : CountRow M) (b : Fin M → ℝ)
    (hb : ∀ a ∈ row.lower, b a ≤ cap i) (ha : 0 < guardAlpha i G row b)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ commonGuardMargin i)
    (hd : |(small row : ℝ)/M-meanResidual i| ≤ 2*δ)
    (hΔ : (imbalance row : ℝ)/M ≤ 4*δ)
    (hC : |centralDemand i G row b/M-meanResidual i| ≤ δ)
    (p : Path (Fin M) (imbalance row))
    (hp : 0 < (pathLaw (sourceWeights i G row b) (imbalance row) ∅).mass p) :
    |Literal.root (xi i) (rootLo i G) (rootHi i G) (lowerBids row b)
        (finalSet (imbalance row) ∅ p) (small row)-G.multiplier| ≤
      (14*xi i*cap i/meanResidual i)*δ := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hr := rootBounds i G
  have hg := guardAlpha_pos i G row b hM hb ha
  obtain ⟨hcard,hz,hclear,hselected⟩ := guarded_weighted_path_root i G row b hb ha p hp
  let E := finalSet (imbalance row) ∅ p
  let z := Literal.root (xi i) (rootLo i G) (rootHi i G) (lowerBids row b) E (small row)
  let F := remainingDemand (xi i) (lowerBids row b) E G.multiplier
  have hL : rootLo i G ≤ G.multiplier := by dsimp [rootLo]; linarith [guardRadius_pos i]
  have hL0 := hr.1.trans_le hL
  have hrem := removal_changes_demand_by_at_most_card (xi i) G.multiplier
    (lowerBids row b) (xi_range i).1 hL0 E
  change centralDemand i G row b-(E.card : ℝ) ≤ F ∧ F ≤ centralDemand i G row b at hrem
  change E.card = imbalance row at hcard
  rw [hcard] at hrem
  have hremL := div_le_div_of_nonneg_right hrem.1 hMr.le
  have hremR := div_le_div_of_nonneg_right hrem.2 hMr.le
  rw [sub_div] at hremL
  have he := (commonGuardMargin_bounds i).2.2
  have hq := meanResidual_pos i
  obtain ⟨hdL,hdR⟩ := abs_le.mp hd
  obtain ⟨hcL,hcR⟩ := abs_le.mp hC
  have hsmall : meanResidual i/2 ≤ (small row : ℝ)/M := by linarith
  have hF : meanResidual i/2 ≤ F/M := by linarith
  have herr : |F/M-(small row : ℝ)/M| ≤ 7*δ := by
    apply abs_le.mpr
    constructor <;> linarith
  have hFd : meanResidual i*(M : ℝ)/2 ≤ (small row : ℝ) := by
    have h := (le_div_iff₀ hMr).mp hsmall
    nlinarith
  have hFF : meanResidual i*(M : ℝ)/2 ≤ F := by
    have h := (le_div_iff₀ hMr).mp hF
    nlinarith
  have hQ : 0 < meanResidual i*(M : ℝ)/2 := by positivity
  have hdist := finite_root_distance (lowerBids row b) E (xi_range i).1 (xi_range i).2
    (cap_pos i) hr.1 hr.2.2 hg.1.1 hL hz.1 hclear hQ hFd hFF
  have herr' : |F-(small row : ℝ)| ≤ 7*δ*M := by
    rw [← sub_div, abs_div, abs_of_pos hMr] at herr
    exact (div_le_iff₀ hMr).mp herr
  have hfac : 0 ≤ xi i*cap i/(meanResidual i*(M : ℝ)/2) :=
    div_nonneg (mul_pos (xi_range i).1 (cap_pos i)).le hQ.le
  have hm := mul_le_mul_of_nonneg_left herr' hfac
  calc
    _ ≤ xi i*cap i/(meanResidual i*(M : ℝ)/2)*|F-(small row : ℝ)| := hdist
    _ ≤ xi i*cap i/(meanResidual i*(M : ℝ)/2)*(7*δ*M) := hm
    _ = (14*xi i*cap i/meanResidual i)*δ := by field_simp [hq.ne', hMr.ne']; ring

def marginalPayoff (η v b p : ℝ) : ℝ := (v-b)*(2*p-p^2)-η*b*p^2

theorem productPayoff_eq_marginal (i : Row) (v L b : ℝ) :
    productPayoff (xi i) v L b = marginalPayoff (eta i) v b (exposure (xi i) L b) := by
  unfold productPayoff marginalPayoff xi
  ring

theorem marginalPayoff_bound (i : Row) {v b p : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (t i)) (hb : b ∈ Icc (0 : ℝ) (cap i))
    (hp : p ∈ Icc (0 : ℝ) 1) : |marginalPayoff (eta i) v b p| ≤ 3*t i := by
  have hη := eta_range i
  have hbT := hb.2.trans (cap_lt_t i).le
  have hvb : |v-b| ≤ t i := abs_le.mpr
    ⟨by linarith [hv.1,hbT],by linarith [hv.2,hb.1]⟩
  have hq : 0 ≤ 2*p-p^2 ∧ 2*p-p^2 ≤ 1 := by
    constructor <;> nlinarith [hp.1,hp.2,sq_nonneg (1-p)]
  have hp2 : 0 ≤ p^2 ∧ p^2 ≤ 1 := ⟨sq_nonneg _,by nlinarith [hp.1,hp.2]⟩
  unfold marginalPayoff
  calc
    _ ≤ |(v-b)*(2*p-p^2)|+|eta i*b*p^2| := abs_sub _ _
    _ = |v-b| *(2*p-p^2)+eta i*b*p^2 := by
      rw [abs_mul,abs_of_nonneg hq.1,
        abs_of_nonneg (mul_nonneg (mul_nonneg hη.1.le hb.1) hp2.1)]
    _ ≤ 3*t i := by
      have hfirst := mul_le_mul_of_nonneg_left hq.2 (abs_nonneg (v-b))
      have hsecond := mul_le_mul_of_nonneg_left hp2.2 (mul_nonneg hη.1.le hb.1)
      have hηb : eta i*b ≤ b := mul_le_of_le_one_left hb.1 hη.2.le
      nlinarith [t_pos i]

theorem productPayoff_bound (i : Row) {v b L : ℝ} (hL : 0 < L)
    (hv : v ∈ Icc (0 : ℝ) (t i)) (hb : b ∈ Icc (0 : ℝ) (cap i)) :
    |productPayoff (xi i) v L b| ≤ 3*t i := by
  rw [productPayoff_eq_marginal]
  exact marginalPayoff_bound i hv hb ⟨exposure_nonneg (xi_range i).1 hL,exposure_le_one _ _ _⟩

theorem marginalPayoff_lipschitz (i : Row) {v b p q : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (t i)) (hb : b ∈ Icc (0 : ℝ) (cap i))
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    |marginalPayoff (eta i) v b p-marginalPayoff (eta i) v b q| ≤ 4*t i*|p-q| := by
  have hη := eta_range i
  have hbT := hb.2.trans (cap_lt_t i).le
  have hvb : |v-b| ≤ t i := abs_le.mpr
    ⟨by linarith [hv.1,hbT],by linarith [hv.2,hb.1]⟩
  have hsum : |p+q| ≤ 2 := by
    rw [abs_of_nonneg (by linarith [hp.1,hq.1])]
    linarith [hp.2,hq.2]
  have hcomp : |2-p-q| ≤ 2 := by
    rw [abs_of_nonneg (by linarith [hp.2,hq.2])]
    linarith [hp.1,hq.1]
  have he : marginalPayoff (eta i) v b p-marginalPayoff (eta i) v b q =
      (v-b)*(p-q)*(2-p-q)-eta i*b*(p-q)*(p+q) := by unfold marginalPayoff; ring
  rw [he]
  calc
    _ ≤ |(v-b)*(p-q)*(2-p-q)|+|eta i*b*(p-q)*(p+q)| := abs_sub _ _
    _ = |v-b| *|p-q| *|2-p-q|+eta i*b*|p-q| *|p+q| := by
      simp only [abs_mul,abs_of_nonneg hη.1.le,abs_of_nonneg hb.1]
    _ ≤ t i*|p-q| *2+t i*|p-q| *2 := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_right hvb (abs_nonneg _)) hcomp
          (abs_nonneg _) (mul_nonneg (t_pos i).le (abs_nonneg _))
      · have hηb : eta i*b ≤ t i :=
          (mul_le_of_le_one_left hb.1 hη.2.le).trans hbT
        exact mul_le_mul (mul_le_mul_of_nonneg_right hηb (abs_nonneg _)) hsum
          (abs_nonneg _) (mul_nonneg (t_pos i).le (abs_nonneg _))
    _ = _ := by ring

def menuRootConstant (i : Row) : ℝ := 112*cap i/meanResidual i
def menuSamplingConstant (i : Row) : ℝ := 32*t i/weightMargin i
def menuConstant (i : Row) : ℝ := menuRootConstant i+menuSamplingConstant i

theorem menuConstant_pos (i : Row) : 0 < menuConstant i := by
  have hU := cap_pos i
  have hq := meanResidual_pos i
  have ht := t_pos i
  have hw := weightMargin_pos i
  unfold menuConstant menuRootConstant menuSamplingConstant
  positivity

theorem productPayoff_root_error (i : Row) (G : RestrictedLaw i)
    {v b z δ : ℝ} (hv : v ∈ Icc (0 : ℝ) (t i))
    (hb : b ∈ Icc (0 : ℝ) (cap i)) (hz : rootLo i G ≤ z)
    (hδ : 0 ≤ δ)
    (hdist : |z-G.multiplier| ≤ (14*xi i*cap i/meanResidual i)*δ) :
    |productPayoff (xi i) v z b-productPayoff (xi i) v G.multiplier b| ≤
      menuRootConstant i*δ := by
  have hr := rootBounds i G
  have hlo : t i/2 ≤ rootLo i G := by
    have hh := (le_max_right _ _).trans_lt (shifted_multiplier_guards i G)
    dsimp [rootLo]
    linarith [t_pos i]
  have ht := t_pos i
  have hξ := (xi_range i).1
  have hU := cap_pos i
  have hq := meanResidual_pos i
  have hhalf : 0 < t i/2 := by positivity
  have hL : rootLo i G ≤ G.multiplier := by dsimp [rootLo]; linarith [guardRadius_pos i]
  have hp := exposure_abs_sub_z (xi_range i).1 (xi_range i).2 hr.1 hr.2.2 hb.2 hz hL
  have hden : 0 < xi i*(t i/2) := mul_pos (xi_range i).1 hhalf
  have hdenlo : 0 < xi i*rootLo i G := mul_pos (xi_range i).1 hr.1
  have hp' : |exposure (xi i) z b-exposure (xi i) G.multiplier b| ≤
      ((14*xi i*cap i/meanResidual i)*δ)/(xi i*(t i/2)) := by
    calc
      _ ≤ |z-G.multiplier| /(xi i*rootLo i G) := hp
      _ ≤ ((14*xi i*cap i/meanResidual i)*δ)/(xi i*rootLo i G) :=
        div_le_div_of_nonneg_right hdist hdenlo.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
        hden (mul_le_mul_of_nonneg_left hlo (xi_range i).1.le)
  have hu := marginalPayoff_lipschitz i (p := exposure (xi i) z b)
    (q := exposure (xi i) G.multiplier b) hv hb
    ⟨exposure_nonneg (xi_range i).1 (hr.1.trans_le hz),exposure_le_one _ _ _⟩
    ⟨exposure_nonneg (xi_range i).1 (hr.1.trans_le hL),exposure_le_one _ _ _⟩
  rw [productPayoff_eq_marginal,productPayoff_eq_marginal]
  have hh := mul_le_mul_of_nonneg_left hp' (by positivity : 0 ≤ 4*t i)
  apply hu.trans
  convert! hh using 1
  unfold menuRootConstant
  field_simp [(xi_range i).1.ne',(t_pos i).ne',(meanResidual_pos i).ne']
  ring

theorem controlled_target_probability {M : ℕ} [NeZero M]
    (i : Row) (G : RestrictedLaw i) (row : CountRow M) (b : Fin M → ℝ)
    (focal : Fin M) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ commonGuardMargin i)
    (hΔ : (imbalance row : ℝ)/M ≤ 4*δ)
    (hW : weightMargin i-δ ≤ totalWeight (sourceWeights i G row b)/M) :
    (pathLaw (sourceWeights i G row b) (imbalance row) ∅).prob
      (fun p => focal ∈ finalSet (imbalance row) ∅ p) ≤ 8*δ/weightMargin i := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne M))
  have hw := weightMargin_pos i
  have he := (commonGuardMargin_bounds i).2.1
  have hD : weightMargin i/2 ≤
      (totalWeight (sourceWeights i G row b)-(imbalance row : ℝ))/M := by
    rw [sub_div]
    linarith
  have hdenF : 0 < (totalWeight (sourceWeights i G row b)-(imbalance row : ℝ))/M :=
    (half_pos hw).trans_le hD
  have hden : 0 < totalWeight (sourceWeights i G row b)-(imbalance row : ℝ) :=
    (div_pos_iff_of_pos_right hMr).mp hdenF
  have hp := Literal.weighted_target_hit_empty (sourceWeights i G row b)
    (imbalance row) focal (by linarith)
  apply hp.trans
  calc
    (imbalance row : ℝ)/(totalWeight (sourceWeights i G row b)-(imbalance row : ℝ)) =
        ((imbalance row : ℝ)/M)/
          ((totalWeight (sourceWeights i G row b)-(imbalance row : ℝ))/M) := by
      field_simp [hMr.ne',hden.ne']
    _ ≤ (4*δ)/((totalWeight (sourceWeights i G row b)-(imbalance row : ℝ))/M) :=
      div_le_div_of_nonneg_right hΔ hdenF.le
    _ ≤ (4*δ)/(weightMargin i/2) :=
      div_le_div_of_nonneg_left (by positivity) (half_pos hw) hD
    _ = 8*δ/weightMargin i := by ring

theorem canonical_menu_error {M : ℕ} [NeZero M]
    (i : Row) (G : RestrictedLaw i) (row : CountRow M) (b : Fin M → ℝ)
    (focal : Fin M) (hfocal : focal ∈ row.lower) {v δ : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (t i))
    (hb : ∀ a ∈ row.lower, b a ∈ Icc (0 : ℝ) (cap i))
    (ha : 0 < guardAlpha i G row b) (hδ0 : 0 ≤ δ) (hδ : δ ≤ commonGuardMargin i)
    (hd : |(small row : ℝ)/M-meanResidual i| ≤ 2*δ)
    (hΔ : (imbalance row : ℝ)/M ≤ 4*δ)
    (hC : |centralDemand i G row b/M-meanResidual i| ≤ δ)
    (hW : weightMargin i-δ ≤ totalWeight (sourceWeights i G row b)/M) :
    |(canonicalLaw i G row b).expect (pairPayoff (eta i) v (b focal) focal)-
      productPayoff (xi i) v G.multiplier (b focal)| ≤ menuConstant i*δ := by
  let P := pathLaw (sourceWeights i G row b) (imbalance row) ∅
  let f := Literal.pathPayoff (xi i) (rootLo i G) (rootHi i G) (eta i) v
    (lowerBids row b) (small row) (imbalance row) focal
  let u := productPayoff (xi i) v G.multiplier (b focal)
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hg := guardAlpha_pos i G row b hM (fun a ha => (hb a ha).2) ha
  have hr := rootBounds i G
  have hL : 0 < G.multiplier := (demandLo_pos i).trans G.multiplier_guards.1
  have hU := productPayoff_bound i hL hv (hb focal hfocal)
  have hfirst : |v-b focal| ≤ t i := by
    have hbT := (hb focal hfocal).2.trans (cap_lt_t i).le
    exact abs_le.mpr ⟨by linarith [(hb focal hfocal).1,hv.1,hv.2],
      by linarith [(hb focal hfocal).1,hv.1,hv.2]⟩
  have hrootC : 0 ≤ menuRootConstant i*δ := by
    have hq := meanResidual_pos i
    have hcap := cap_pos i
    unfold menuRootConstant
    positivity
  have he : (canonicalLaw i G row b).expect (pairPayoff (eta i) v (b focal) focal) = P.expect f := by
    rw [canonicalLaw, FiniteLaw.expect_map]
    have horient (out : Path (Fin M) (imbalance row) × Allocation M) :
        pairPayoff (eta i) v (b focal) focal (orient row out.2) =
          Literal.countPayoff (eta i) v (lowerBids row b focal) focal out.2 := by
      unfold pairPayoff Literal.countPayoff
      rw [orient_success, orient_duplicate, lowerBids_of_mem row b hfocal]
    simp_rw [horient]
    exact Literal.weighted_payoff (lowerBids row b) (sourceWeights i G row b)
      (small row) (imbalance row) (xi_range i).1 (xi_range i).2 (cap_pos i)
      hr.1 hr.2.1 hr.2.2 hg.2.1 hg.2.2 hg.1 focal
  have hpoint : ∀ p, 0 < P.mass p → |f p-u| ≤
      4*t i*(if focal ∈ finalSet (imbalance row) ∅ p then 1 else 0)+menuRootConstant i*δ := by
    intro p hp
    obtain ⟨hc,hz,hclear,hselected⟩ := guarded_weighted_path_root i G row b
      (fun a ha => (hb a ha).2) ha p hp
    have hdist := guarded_path_root_distance i G row b (fun a ha => (hb a ha).2) ha
      hδ0 hδ hd hΔ hC p hp
    by_cases hmem : focal ∈ finalSet (imbalance row) ∅ p
    · have hdiff : |v-b focal-u| ≤ 4*t i :=
        (abs_sub _ _).trans (by dsimp [u]; linarith)
      simpa [f,Literal.pathPayoff,hmem,lowerBids_of_mem row b hfocal] using
        (hdiff.trans (by linarith : 4*t i ≤ 4*t i+menuRootConstant i*δ))
    · have herr := productPayoff_root_error i G hv (hb focal hfocal) hz.1 hδ0 hdist
      simpa only [f,Literal.pathPayoff,if_neg hmem,lowerBids_of_mem row b hfocal,
        u,productPayoff_eq_marginal,marginalPayoff,mul_zero,zero_add] using herr
  rw [he]
  change |P.expect f-u| ≤ _
  have hmean : P.expect (fun p => f p-u) = P.expect f-u := by
    rw [FiniteLaw.expect_sub,FiniteLaw.expect_const]
  rw [← hmean]
  have hbound := WeightedSampling.expect_le_of_support P
    (fun p => |f p-u|)
    (fun p => 4*t i*(if focal ∈ finalSet (imbalance row) ∅ p then 1 else 0)+menuRootConstant i*δ)
    hpoint
  apply (WeightedSampling.abs_expect_le P _).trans (hbound.trans ?_)
  rw [FiniteLaw.expect_add,FiniteLaw.expect_const_mul,FiniteLaw.expect_const]
  have hevent : P.expect (fun p=>if focal∈finalSet (imbalance row) ∅ p then (1:ℝ) else 0)=
      P.prob (fun p=>focal∈finalSet (imbalance row) ∅ p) := by
    rw [FiniteLaw.prob_eq_expect]
  rw [hevent]
  have hp := controlled_target_probability i G row b focal hδ0 hδ hΔ hW
  have ht := t_pos i
  have hmul := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ 4*t i)
  unfold menuConstant menuSamplingConstant
  nlinarith [show 4*t i*(8*δ/weightMargin i) = (32*t i/weightMargin i)*δ by ring]

theorem row_menu_error {M : ℕ} [NeZero M]
    (i : Row) (G : RestrictedLaw i) (row : CountRow M) (b : Fin M → ℝ)
    (focal : Fin M) (hfocal : focal ∈ row.lower) {v δ : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (t i))
    (hb : ∀ a ∈ row.lower, b a ∈ Icc (0 : ℝ) (cap i))
    (ha : guardAlpha i G row b = 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ commonGuardMargin i)
    (hd : |(small row : ℝ)/M-meanResidual i| ≤ 2*δ)
    (hΔ : (imbalance row : ℝ)/M ≤ 4*δ)
    (hC : |centralDemand i G row b/M-meanResidual i| ≤ δ)
    (hW : weightMargin i-δ ≤ totalWeight (sourceWeights i G row b)/M) :
    |rowPayoff i G row v b focal-productPayoff (xi i) v G.multiplier (b focal)| ≤
      menuConstant i*δ := by
  have hapos : 0 < guardAlpha i G row b := by rw [ha]; norm_num
  by_cases heq : residual row 0 = residual row 1
  · let P := pathLaw (sourceWeights i G row b) (imbalance row) ∅
    obtain ⟨p,hp⟩ : ∃ p, 0 < P.mass p := by
      by_contra hn
      push Not at hn
      have hh : (∑ p, P.mass p) ≤ 0 := Finset.sum_nonpos (fun p _ => hn p)
      rw [P.total] at hh
      norm_num at hh
    obtain ⟨hc,hz,hclear,hselected⟩ := guarded_weighted_path_root i G row b
      (fun a ha => (hb a ha).2) hapos p hp
    have hΔ0 : imbalance row = 0 := by simp [imbalance,large,small,heq]
    have hE : finalSet (imbalance row) ∅ p = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa only [hΔ0] using hc
    let z := Literal.root (xi i) (rootLo i G) (rootHi i G) (lowerBids row b)
      (finalSet (imbalance row) ∅ p) (small row)
    change remainingDemand (xi i) (lowerBids row b) (finalSet (imbalance row) ∅ p) z =
      (small row : ℝ) at hclear
    have hz0 : 0 < z := (rootBounds i G).1.trans_le hz.1
    have hclear' : (∑ a, exposure (xi i) z (lowerBids row b a)) = (small row : ℝ) := by
      simpa only [hE,remainingDemand,Finset.notMem_empty,if_false] using hclear
    rw [rowPayoff_equal_of_clearing i G row v b focal hfocal heq hz0
      ((rootBounds i G).2.2.trans hz.1) (fun a ha => (hb a ha).1)
      (fun a ha => (hb a ha).2) hclear']
    have hdist := guarded_path_root_distance i G row b (fun a ha => (hb a ha).2) hapos
      hδ0 hδ hd hΔ hC p hp
    have herr := productPayoff_root_error i G hv (hb focal hfocal) hz.1 hδ0 hdist
    apply herr.trans
    have hs : 0 ≤ menuSamplingConstant i*δ := by
      have ht := t_pos i
      have hw := weightMargin_pos i
      unfold menuSamplingConstant
      positivity
    unfold menuConstant
    nlinarith
  · rw [rowPayoff_unequal i G row v b focal heq,ha]
    simp only [one_mul,sub_self,zero_mul,add_zero]
    exact canonical_menu_error i G row b focal hfocal hv hb hapos hδ0 hδ hd hΔ hC hW

private theorem prefix_error_imp {A S μ N K δ : ℝ}
    (hN : 0 < N) (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hroom : K ≤ N*δ/2)
    (hp : |A-K*μ| ≤ K)
    (htotal : δ ≤ |(A+S)/(N+K)-μ|) : δ/2 ≤ |S/N-μ| := by
  have hNK : 0 < N+K := by linarith
  have he : |(A+S)/(N+K)-μ| = |A+S-(N+K)*μ| /(N+K) := by
    calc
      _ = |(A+S-(N+K)*μ)/(N+K)| := by congr 1; field_simp [hNK.ne']
      _ = _ := by rw [abs_div,abs_of_pos hNK]
  rw [he] at htotal
  have ht := (le_div_iff₀ hNK).mp htotal
  have hab := abs_add_le (S-N*μ) (A-K*μ)
  have hr : S-N*μ+(A-K*μ) = A+S-(N+K)*μ := by ring
  rw [hr] at hab
  have heS : |S-N*μ| = N*|S/N-μ| := by
    calc
      _ = |N*(S/N-μ)| := by congr 1; field_simp [hN.ne']
      _ = _ := by rw [abs_mul,abs_of_pos hN]
  rw [heS] at hab
  nlinarith [mul_nonneg hK hδ]

theorem fixed_scalar_deviation_le {α : Type*} [MeasurableSpace α] {K : ℕ}
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ)
    (hf : Measurable f) (hb : ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (p : Fin K → α) (N : ℕ) (hN : 0 < N) {δ : ℝ} (hδ : 0 ≤ δ)
    (hroom : (K : ℝ) ≤ N*δ/2) :
    (Measure.pi (fun _ : Fin N => μ)).real
      {x | δ ≤ |(∑ a, f (prepend p x a))/(N+K : ℕ)-∫ y, f y ∂μ|} ≤
        2*Real.exp (-(N : ℝ)*δ^2/2) := by
  have hi := integrable_of_unit_bounds μ hf (fun x => (hb x).1) (fun x => (hb x).2)
  have hμ0 : 0 ≤ ∫ y, f y ∂μ := integral_nonneg (fun x => (hb x).1)
  have hμ1 : (∫ y, f y ∂μ) ≤ 1 := by
    have h := integral_mono hi (integrable_const (1 : ℝ)) (fun x => (hb x).2)
    simpa using h
  have hA0 : 0 ≤ ∑ a, f (p a) := Finset.sum_nonneg (fun a _ => (hb (p a)).1)
  have hA1 : (∑ a, f (p a)) ≤ (K : ℝ) := by
    calc
      _ ≤ ∑ _a : Fin K, (1 : ℝ) := Finset.sum_le_sum (fun a _ => (hb (p a)).2)
      _ = K := by simp
  have hKμ0 : 0 ≤ (K : ℝ)*(∫ y, f y ∂μ) :=
    mul_nonneg (Nat.cast_nonneg K) hμ0
  have hKμ1 : (K : ℝ)*(∫ y, f y ∂μ) ≤ K := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hμ1 (Nat.cast_nonneg K)
  have hp : |(∑ a, f (p a))-(K : ℝ)*(∫ y, f y ∂μ)| ≤ K := by
    rw [abs_le]
    constructor <;> linarith
  have hiid := Probability.iid_empiricalMean_two_sided_le μ hf.aemeasurable
    (Eventually.of_forall hb) N hN (show 0 ≤ δ/2 by positivity)
  have hsub : {x : Fin N → α | δ ≤
      |(∑ a, f (prepend p x a))/(N+K : ℕ)-∫ y, f y ∂μ|} ⊆
      {x | δ/2 ≤ |(∑ a, f (x a))/(N : ℝ)-∫ y, f y ∂μ|} := by
    intro x hx
    change δ≤|(∑ a,f (prepend p x a))/(N+K:ℕ)-∫ y,f y ∂μ| at hx
    change δ/2≤|(∑ a,f (x a))/(N:ℝ)-∫ y,f y ∂μ|
    rw [sum_prepend f p x] at hx
    push_cast at hx
    exact prefix_error_imp (by exact_mod_cast hN) (Nat.cast_nonneg K) hδ hroom hp hx
  have hm := measureReal_mono (μ := Measure.pi (fun _ : Fin N=>μ)) hsub
  have he : -2*(N : ℝ)*(δ/2)^2 = -(N : ℝ)*δ^2/2 := by ring
  rw [he] at hiid
  exact hm.trans hiid

def centralStatistic (i : Row) (G : RestrictedLaw i) : Observation i → ℝ :=
  lowerExtension i (fun b => exposure (xi i) G.multiplier b)

theorem measurable_centralStatistic (i : Row) (G : RestrictedLaw i) :
    Measurable (centralStatistic i G) :=
  measurable_lowerExtension i ((continuous_exposure (xi_range i).1
    ((demandLo_pos i).trans G.multiplier_guards.1)).comp continuous_subtype_val).measurable

theorem centralStatistic_bounds (i : Row) (G : RestrictedLaw i) :
    ∀ x, centralStatistic i G x ∈ Icc (0 : ℝ) 1 :=
  lowerExtension_bounds i (fun _b =>
    ⟨exposure_nonneg (xi_range i).1 ((demandLo_pos i).trans G.multiplier_guards.1),
      exposure_le_one _ _ _⟩)

theorem centralStatistic_mean (i : Row) (G : RestrictedLaw i) :
    (∫ x, centralStatistic i G x ∂observationLaw i G) = meanResidual i := by
  have h := integral_lowerExtension i G
    ((continuous_exposure (xi_range i).1
      ((demandLo_pos i).trans G.multiplier_guards.1)).comp continuous_subtype_val).measurable
    (fun _ => ⟨exposure_nonneg (xi_range i).1
      ((demandLo_pos i).trans G.multiplier_guards.1),exposure_le_one _ _ _⟩)
  change (∫ x, centralStatistic i G x ∂observationLaw i G) =
    t i*lawDemand i G.bidLaw G.multiplier at h
  simpa only [G.multiplier_equation,meanResidual] using h

theorem centralStatistic_sum {M : ℕ} (i : Row) (G : RestrictedLaw i)
    (x : Fin M → Observation i) :
    (∑ a, centralStatistic i G (x a)) =
      centralDemand i G (observationCountRow i x) (fun a => observationBid i (x a)) := by
  have hz := (demandLo_pos i).trans G.multiplier_guards.1
  rw [centralDemand,lowerBids_observation]
  apply Finset.sum_congr rfl
  intro a _
  rcases h : x a with p | j
  · simp only [centralStatistic,lowerExtension,h,observationBid,Sum.elim_inl]
  · simp [centralStatistic,lowerExtension,observationBid,exposure_zero hz.le,h]

def MenuGood {M : ℕ} (i : Row) (G : RestrictedLaw i) (δ : ℝ)
    (x : Fin M → Observation i) : Prop :=
  (∀ k : Fin 8, |(∑ a, sourceStatistic i G k (x a))/(M : ℝ)-sourceMean i G k| < δ) ∧
    |(∑ a, centralStatistic i G (x a))/(M : ℝ)-meanResidual i| < δ

theorem measurableSet_menuGood {M : ℕ} (i : Row) (G : RestrictedLaw i) (δ : ℝ) :
    MeasurableSet {x : Fin M → Observation i | MenuGood i G δ x} := by
  have hs (k : Fin 8) : Measurable (fun x : Fin M → Observation i =>
      (∑ a, sourceStatistic i G k (x a))/(M : ℝ)-sourceMean i G k) := by
    exact ((Finset.measurable_sum _ (fun a _ =>
      (measurable_sourceStatistic i G k).comp (measurable_pi_apply a))).div_const _).sub_const _
  have hc : Measurable (fun x : Fin M → Observation i =>
      (∑ a, centralStatistic i G (x a))/(M : ℝ)-meanResidual i) := by
    exact ((Finset.measurable_sum _ (fun a _ =>
      (measurable_centralStatistic i G).comp (measurable_pi_apply a))).div_const _).sub_const _
  have he : {x : Fin M→Observation i | MenuGood i G δ x}=
      (⋂ k : Fin 8,{x | |(∑ a,sourceStatistic i G k (x a))/(M:ℝ)-sourceMean i G k|<δ}) ∩
      {x | |(∑ a,centralStatistic i G (x a))/(M:ℝ)-meanResidual i|<δ} := by
    ext x; simp only [MenuGood,mem_setOf_eq,mem_inter_iff,mem_iInter]
  rw [he]
  exact (MeasurableSet.iInter (fun k => measurableSet_lt (hs k).abs measurable_const)).inter
    (measurableSet_lt hc.abs measurable_const)

theorem fixed_menu_bad_le {K : ℕ} (i : Row) (G : RestrictedLaw i)
    (p : Fin K → Observation i) (N : ℕ) (hN : 0 < N) {δ : ℝ}
    (hδ : 0 ≤ δ) (hroom : (K : ℝ) ≤ N*δ/2) :
    (Measure.pi (fun _ : Fin N => observationLaw i G)).real
      {x | ¬MenuGood i G δ (prepend p x)} ≤ 18*Real.exp (-(N : ℝ)*δ^2/2) := by
  let E := {x : Fin N → Observation i | ∃ k : Fin 8,
    δ ≤ |(∑ a, sourceStatistic i G k (prepend p x a))/(N+K : ℕ)-sourceMean i G k|}
  let F := {x : Fin N → Observation i |
    δ ≤ |(∑ a, centralStatistic i G (prepend p x a))/(N+K : ℕ)-meanResidual i|}
  have heq : {x : Fin N → Observation i | ¬MenuGood i G δ (prepend p x)} = E ∪ F := by
    ext x
    simp only [MenuGood,mem_setOf_eq,mem_union,E,F,not_and_or,not_forall,not_lt]
  rw [heq]
  have hE := fixed_sourceStatistic_deviation_le i G p N hN hδ hroom
  have hF := fixed_scalar_deviation_le (observationLaw i G) (centralStatistic i G)
    (measurable_centralStatistic i G) (centralStatistic_bounds i G) p N hN hδ hroom
  rw [centralStatistic_mean] at hF
  have hu := measureReal_union_le (μ := Measure.pi (fun _ : Fin N => observationLaw i G)) E F
  change _ ≤ 16*Real.exp (-(N : ℝ)*δ^2/2) at hE
  change _ ≤ 2*Real.exp (-(N : ℝ)*δ^2/2) at hF
  linarith

theorem observed_menu_error {M : ℕ} [NeZero M]
    (i : Row) (G : RestrictedLaw i) (x : Fin M → Observation i)
    (focal : Fin M) (hfocal : focal ∈ (observationCountRow i x).lower) {v δ : ℝ}
    (hv : v ∈ Icc (0 : ℝ) (t i)) (hδ0 : 0 ≤ δ) (hδ : δ ≤ commonGuardMargin i)
    (hc : |(Uniform07.capacity M : ℝ)/M-rho| ≤ δ) (hx : MenuGood i G δ x) :
    |rowPayoff i G (observationCountRow i x) v (fun a => observationBid i (x a)) focal-
      productPayoff (xi i) v G.multiplier (observationBid i (x focal))| ≤ menuConstant i*δ := by
  let row := observationCountRow i x
  let b := fun a => observationBid i (x a)
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have halpha := sourceStatistic_control_guardAlpha_one i G x hM (hc.trans hδ)
    (fun k => (hx.1 k).le.trans hδ)
  have hs := sourceStatistic_sum i G x
  have hN := (hx.1 4).le
  have h0 := (hx.1 5).le
  have h1 := (hx.1 6).le
  have hW := (hx.1 2).le
  rw [congrFun hs 4] at hN
  rw [congrFun hs 5] at h0
  rw [congrFun hs 6] at h1
  rw [congrFun hs 2] at hW
  have hcounts := count_tolerance i row hM hδ0 hδ hc hN h0 h1
  have hC : |centralDemand i G row b/M-meanResidual i| ≤ δ := by
    simpa only [centralStatistic_sum] using hx.2.le
  have hweight : weightMargin i-δ ≤ totalWeight (sourceWeights i G row b)/M := by
    have hpop := (sourceMean_guard_bounds i G).2.2.1
    have hh := (abs_le.mp hW).1
    change -δ ≤ totalWeight (sourceWeights i G row b)/M-sourceMean i G 2 at hh
    linarith
  apply row_menu_error i G row b focal hfocal hv _ halpha hδ0 hδ
    hcounts.1 hcounts.2 hC hweight
  intro a _
  change observationBid i (x a)∈Icc (0:ℝ) (cap i)
  rcases h : x a with p | j
  · exact p.2.property
  · exact ⟨le_rfl,(cap_pos i).le⟩

private theorem integral_menu_error {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f Q : α → ℝ) (u C D : ℝ)
    (hf : AEStronglyMeasurable f μ) (hQ : Integrable Q μ)
    (h : ∀ᵐ x ∂μ, |f x-u| ≤ C*Q x+D) :
    |(∫ x, f x ∂μ)-u| ≤ C*(∫ x, Q x ∂μ)+D := by
  have hdom : Integrable (fun x => C*Q x+D) μ := (hQ.const_mul C).add (integrable_const D)
  have hdiff : Integrable (fun x => f x-u) μ := hdom.mono'
    (hf.sub aestronglyMeasurable_const) (by simpa only [Real.norm_eq_abs] using h)
  have hfi : Integrable f μ := by
    have he : (fun x => f x-u+u) = f := by funext x; ring
    exact he ▸ hdiff.add (integrable_const u)
  have he : (∫ x, f x-u ∂μ) = (∫ x, f x ∂μ)-u := by
    rw [integral_sub hfi (integrable_const u),integral_const,probReal_univ,one_smul]
  rw [← he]
  apply abs_integral_le_integral_abs.trans
  have hh := integral_mono_ae hdiff.abs hdom h
  rwa [integral_add (hQ.const_mul C) (integrable_const D),integral_const_mul,
    integral_const,probReal_univ,one_smul] at hh

theorem original_focalPayoff_eq (i : Row) (N : ℕ) (G : RestrictedLaw i)
    (v : ℝ) (own : Bid i) (x : Fin N → Observation i) :
    numericFocalPayoff i N G v own (fun a => dropValue i (x a)) =
      rowPayoff i G (observationCountRow i (prepend (fun _ : Fin 1 => Sum.inl (v,own)) x))
        v (fun a => observationBid i (prepend (fun _ : Fin 1 => Sum.inl (v,own)) x a)) 0 := by
  have hk (y : Observation i) : numericKind i (dropValue i y) = observationKind i y := by
    cases y <;> rfl
  have hb (y : Observation i) : numericBid i (dropValue i y) = observationBid i y := by
    cases y <;> rfl
  simp only [numericFocalPayoff,observationCountRow,prepend]
  have hkind : Fin.cons (0 : Fin 3) (fun a => numericKind i (dropValue i (x a))) =
      fun a => observationKind i ((Fin.cons (Sum.inl (v,own)) x : Fin (N+1)→Observation i) a) := by
    funext a
    refine Fin.cases ?_ (fun a => ?_) a
    · rfl
    · exact hk (x a)
  have hbids : Fin.cons (own : ℝ) (fun a => numericBid i (dropValue i (x a))) =
      fun a => observationBid i ((Fin.cons (Sum.inl (v,own)) x : Fin (N+1)→Observation i) a) := by
    funext a
    refine Fin.cases ?_ (fun a => ?_) a
    · rfl
    · exact hb (x a)
  rw [hkind,hbids]

theorem rawUtility_product_error (i : Row) (N : ℕ) (G : RestrictedLaw i)
    {v δ : ℝ} (own : Bid i) (hv : v ∈ Icc (0 : ℝ) (t i)) (hN : 0 < N)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ commonGuardMargin i)
    (hsize : 1/((N+1 : ℕ) : ℝ) ≤ δ) (hroom : (1 : ℝ) ≤ N*δ/2) :
    |rawUtility i N G v own-productPayoff (xi i) v G.multiplier own| ≤
      menuConstant i*δ+108*t i*Real.exp (-(N : ℝ)*δ^2/2) := by
  let μ := Measure.pi (fun _ : Fin N => observationLaw i G)
  let p : Fin 1 → Observation i := fun _ => Sum.inl (v,own)
  let f : (Fin N → Observation i) → ℝ := fun x =>
    numericFocalPayoff i N G v own (fun a => dropValue i (x a))
  let u := productPayoff (xi i) v G.multiplier own
  let E : Set (Fin N → Observation i) := {x | ¬MenuGood i G δ (prepend p x)}
  let Q := E.indicator (fun _ => (1 : ℝ))
  have hE : MeasurableSet E :=
    ((measurableSet_menuGood i G δ).preimage (measurable_prepend p)).compl
  have hQ : Integrable Q μ := (integrable_const (1 : ℝ)).indicator hE
  have hQmean : (∫ x, Q x ∂μ) = μ.real E := integral_indicator_one hE
  have hf : Measurable f :=
    (measurable_numericFocalPayoff i N G v own).comp
      (measurable_pi_lambda _ (fun a => (measurable_dropValue i).comp (measurable_pi_apply a)))
  have hη := eta_range i
  have ht := t_pos i
  have hownT := own.property.2.trans (cap_lt_t i).le
  have hfun (x : Fin N → Observation i) : |f x| ≤ 3*t i := by
    have h := numericFocalPayoff_bound i N G v own (fun a => dropValue i (x a))
    rw [abs_of_nonneg hv.1,abs_of_nonneg own.property.1,abs_of_nonneg hη.1.le] at h
    have hmul := mul_le_mul_of_nonneg_right (show 1+eta i ≤ 2 by linarith [hη.2])
      own.property.1
    dsimp [f]
    nlinarith [hv.2]
  have hu : |u| ≤ 3*t i := productPayoff_bound i
    ((demandLo_pos i).trans G.multiplier_guards.1) hv own.property
  have hD : 0 ≤ menuConstant i*δ := mul_nonneg (menuConstant_pos i).le hδ0
  have hpoint : ∀ x, |f x-u| ≤ 6*t i*Q x+menuConstant i*δ := by
    intro x
    by_cases hx : MenuGood i G δ (prepend p x)
    · have hmem : (0 : Fin (N+1)) ∈ (observationCountRow i (prepend p x)).lower := by
        simp [observationCountRow,countRowOfKind,prepend,p,observationKind]
      have herr := observed_menu_error i G (prepend p x) 0 hmem hv hδ0 hδ
        ((capacity_error_le (N+1) (by omega)).trans hsize) hx
      have hfe := original_focalPayoff_eq i N G v own x
      have hobs : observationBid i (prepend p x 0) = (own : ℝ) := rfl
      change f x = _ at hfe
      rw [← hfe,hobs] at herr
      have hnot : x ∉ E := fun hn => hn hx
      simpa only [Q,Set.indicator_of_notMem hnot,mul_zero,zero_add,u] using herr
    · have hfull := (abs_sub (f x) u).trans (add_le_add (hfun x) hu)
      have hmem : x ∈ E := hx
      simp only [Q,Set.indicator_of_mem hmem]
      simp only [mul_one]
      linarith
  have hb := integral_menu_error μ f Q u (6*t i) (menuConstant i*δ)
    hf.aestronglyMeasurable hQ (Eventually.of_forall hpoint)
  rw [hQmean] at hb
  have hfail := fixed_menu_bad_le i G p N hN hδ0 (by simpa using hroom)
  have hmul := mul_le_mul_of_nonneg_left hfail (by positivity : 0 ≤ 6*t i)
  rw [rawUtility_eq_original_observation_integral]
  change |(∫ x, f x ∂μ)-u| ≤ _
  have hlast : 6*t i*(18*Real.exp (-(N : ℝ)*δ^2/2))+menuConstant i*δ =
      menuConstant i*δ+108*t i*Real.exp (-(N : ℝ)*δ^2/2) := by ring
  apply hb.trans
  calc
    6*t i*μ.real E+menuConstant i*δ ≤
        6*t i*(18*Real.exp (-(N : ℝ)*δ^2/2))+menuConstant i*δ :=
      by
        have hmul' : 6*t i*μ.real E ≤ 6*t i*(18*Real.exp (-(N:ℝ)*δ^2/2)) := hmul
        linarith
    _ = _ := hlast

theorem uniform_product_menu (i : Row) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ (G : RestrictedLaw i) (v : ℝ) (own : Bid i),
      v ∈ Icc (0 : ℝ) (t i) →
      |rawUtility i N G v own-productPayoff (xi i) v G.multiplier own| < ε := by
  let δ := min (commonGuardMargin i) (ε/(2*menuConstant i))
  have hC := menuConstant_pos i
  have hδ : 0 < δ := lt_min (common_guard_margin i) (div_pos hε (by positivity))
  have hδle : δ ≤ commonGuardMargin i := min_le_left _ _
  have hδsmall : menuConstant i*δ ≤ ε/2 := by
    have h := (le_div_iff₀ (show 0 < 2*menuConstant i by positivity)).mp
      (min_le_right (commonGuardMargin i) (ε/(2*menuConstant i)))
    dsimp [δ]
    nlinarith
  have hNat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hroom : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ N*δ/2 := by
    have h := (hNat.const_mul_atTop (half_pos hδ)).eventually_ge_atTop (1 : ℝ)
    simpa only [mul_comm (δ/2),mul_div_assoc] using h
  have hsize : ∀ᶠ N : ℕ in atTop, 1/((N+1 : ℕ) : ℝ) ≤ δ := by
    have hsmall := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).eventually
      (Iio_mem_nhds hδ)
    filter_upwards [hsmall,eventually_gt_atTop (0 : ℕ)] with N hN hN0
    exact (div_le_div_of_nonneg_left zero_le_one (by exact_mod_cast hN0)
      (by exact_mod_cast (show N ≤ N+1 by omega))).trans hN.le
  have hexp : Tendsto (fun N : ℕ => Real.exp (-(N : ℝ)*δ^2/2)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (hNat.const_mul_atTop (show 0 < δ^2/2 by positivity))
    convert! h using 1; funext N; congr 1; ring
  have htail : ∀ᶠ N : ℕ in atTop,
      108*t i*Real.exp (-(N : ℝ)*δ^2/2) < ε/2 := by
    have h := hexp.const_mul (108*t i)
    simp only [mul_zero] at h
    exact h.eventually (Iio_mem_nhds (half_pos hε))
  filter_upwards [hroom,hsize,htail,eventually_gt_atTop (0 : ℕ)] with N hR hS hT hN
  intro G v own hv
  have hh := rawUtility_product_error i N G own hv hN hδ.le hδle hS hR
  linarith

end Source
end FCAppendix.Affine.UniformFinite
