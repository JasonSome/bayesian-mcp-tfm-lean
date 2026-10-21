import FCAppendix.Affine.Uniform06.EntryRenewal
import FCAppendix.Affine.Uniform06.EntryParity

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryParityRenewal
open Set Filter Topology
open FCAppendix.PiBinomial
open FCAppendix.Affine.WeightedSampling
open FCAppendix.Affine.Uniform06.EntryUntilting
open FCAppendix.Affine.Uniform06.EntryRenewal
open FCAppendix.Affine.Uniform06.EntryParity
open FCAppendix.Affine.Uniform06.WeightedMoments
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def imbalance (H c : ℕ) : ℕ := if H ≤ 2*c then 2*c-H else H-2*c

lemma imbalance_reflect (H c : ℕ) (hc : c ≤ H) :
    imbalance H (H-c)=imbalance H c := by
  unfold imbalance
  split_ifs <;> omega

lemma imbalance_upper (n e r : ℕ) : imbalance (2*n+e) (n+e+r)=2*r+e := by
  rw [imbalance,if_pos (by omega)]
  omega

lemma half_pmf_nonneg (H c : ℕ) : 0 ≤ pmf H (1/2) c := by
  rw [pmf_half_eq_choose_div]
  positivity

lemma half_pmf_reflect (H c : ℕ) (hc : c ≤ H) :
    pmf H (1/2) (H-c)=pmf H (1/2) c := by
  simp only [pmf_half_eq_choose_div]
  rw [Nat.choose_symm hc]

lemma sum_range_reflection (L : ℕ) (g : ℕ → ℝ) :
    (∑ c ∈ Finset.range L, g c)=∑ r ∈ Finset.range L, g (L-1-r) := by
  apply Finset.sum_bij (fun c _ => L-1-c)
  · intro c hc
    simp only [Finset.mem_range] at hc ⊢
    omega
  · intro c hc d hd hcd
    simp only [Finset.mem_range] at hc hd
    omega
  · intro r hr
    simp only [Finset.mem_range] at hr
    exact ⟨L-1-r,by simp only [Finset.mem_range]; omega,by omega⟩
  · intro c hc
    simp only [Finset.mem_range] at hc
    congr 1
    omega

lemma sum_even_reflection (n : ℕ) (g : ℕ → ℝ)
    (hsym : ∀ c, c ≤ 2*n → g (2*n-c)=g c) :
    (∑ c ∈ Finset.range (2*n+1), g c)=
      2*(∑ r ∈ Finset.range (n+1), g (n+r))-g n := by
  have hl : (∑ c ∈ Finset.range n, g c)=∑ r ∈ Finset.range n, g (n+(r+1)) := by
    rw [sum_range_reflection n g]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < n := Finset.mem_range.mp hr
    rw [← hsym (n-1-r) (by omega)]
    congr 1
    omega
  have hu : (∑ r ∈ Finset.range (n+1), g (n+r))=
      g n+∑ r ∈ Finset.range n, g (n+(r+1)) := by
    rw [Finset.sum_range_succ']
    simp only [add_zero]
    ring
  rw [show 2*n+1=n+(n+1) by omega,Finset.sum_range_add,hl]
  linarith [hu]

lemma sum_odd_reflection (n : ℕ) (g : ℕ → ℝ)
    (hsym : ∀ c, c ≤ 2*n+1 → g (2*n+1-c)=g c) :
    (∑ c ∈ Finset.range (2*n+2), g c)=
      2*(∑ r ∈ Finset.range (n+1), g (n+1+r)) := by
  have hl : (∑ c ∈ Finset.range (n+1), g c)=∑ r ∈ Finset.range (n+1), g (n+1+r) := by
    rw [sum_range_reflection (n+1) g]
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < n+1 := Finset.mem_range.mp hr
    rw [← hsym (n+1-1-r) (by omega)]
    congr 1
    omega
  rw [show 2*n+2=(n+1)+(n+1) by omega,Finset.sum_range_add,hl]
  ring

def fairMoment (w : Weights ι) (h : ι → ℝ) (H k : ℕ) (s : ℝ) : ℝ :=
  ∑ c ∈ Finset.range (H+1), pmf H (1/2) c*pathMoment w h k (imbalance H c) ∅ s

lemma fairMoment_nonneg (w : Weights ι) (h : ι → ℝ) (H k : ℕ) (s : ℝ) :
    0 ≤ fairMoment w h H k s :=
  Finset.sum_nonneg fun c _ => mul_nonneg (half_pmf_nonneg H c) (pathMoment_nonneg _ _ _ _ _ _)

theorem fairMoment_parity_sum (w : Weights ι) (h : ι → ℝ) (n k : ℕ)
    {e : ℕ} (he : e ≤ 1) (s : ℝ) :
    fairMoment w h (2*n+e) k s=
      2*(∑ r ∈ Finset.range (n+1), pmf (2*n+e) (1/2) (n+e+r)*pathMoment w h k (2*r+e) ∅ s)-
        if e=0 then pmf (2*n+e) (1/2) (n+e)*deficitMoment k s else 0 := by
  let g : ℕ → ℝ := fun c => pmf (2*n+e) (1/2) c*pathMoment w h k (imbalance (2*n+e) c) ∅ s
  have hsym : ∀ c, c ≤ 2*n+e → g (2*n+e-c)=g c := by
    intro c hc
    dsimp [g]
    rw [half_pmf_reflect _ _ hc,imbalance_reflect _ _ hc]
  have hup (r : ℕ) : g (n+e+r)=pmf (2*n+e) (1/2) (n+e+r)*pathMoment w h k (2*r+e) ∅ s := by
    simp only [g,imbalance_upper]
  rcases (show e=0 ∨ e=1 by omega) with rfl | rfl
  · have ht := sum_even_reflection n g (by simpa using hsym)
    change (∑ c ∈ Finset.range (2*n+0+1), g c)=_
    simp only [add_zero] at hup ⊢
    simp_rw [← hup]
    have hz : g n=pmf (2*n) (1/2) n*deficitMoment k s := by
      simpa using hup 0
    simpa only [if_true,hz] using ht
  · have ht := sum_odd_reflection n g (by simpa using hsym)
    change (∑ c ∈ Finset.range (2*n+1+1), g c)=_
    simp_rw [← hup]
    simpa only [if_neg (by decide : ¬(1:ℕ)=0),sub_zero,show 2*n+1+1=2*n+2 by omega] using ht

lemma parity_sum_truncate (w : Weights ι) (h : ι → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hh : ∀ i, a ≤ h i) (n J k e : ℕ)
    (hJn : J ≤ n+1) {s : ℝ} (hs : s ≤ 2*a*J) :
    (∑ r ∈ Finset.range (n+1), pmf (2*n+e) (1/2) (n+e+r)*pathMoment w h k (2*r+e) ∅ s)=
      ∑ r ∈ Finset.range J, pmf (2*n+e) (1/2) (n+e+r)*pathMoment w h k (2*r+e) ∅ s := by
  symm
  apply Finset.sum_subset (Finset.range_mono hJn)
  intro r _ hr
  have hrJ : J ≤ r := by simpa only [Finset.mem_range,not_lt] using hr
  have hdr : (2*J : ℝ) ≤ (2*r+e : ℕ) := by exact_mod_cast (show 2*J ≤ 2*r+e by omega)
  rw [pathMoment_zero_of_stopped w h hh k (2*r+e) ∅
    (by nlinarith [mul_le_mul_of_nonneg_left hdr ha]),mul_zero]

theorem fairMoment_vs_occupation (w : Weights ι) (h : ι → ℝ)
    {a : ℝ} (ha : 0 ≤ a) (hh : ∀ i, a ≤ h i)
    {n J k e : ℕ} (hn : 0 < n) (he : e ≤ 1) (hJn : J ≤ n+1)
    {s : ℝ} (hs : s ≤ 2*a*J) :
    2*pmf (2*n+e) (1/2) (n+e)*(1-(J : ℝ)*((J : ℝ)+e)/n)*
        parityOccupation w h k J e s-pmf (2*n+e) (1/2) (n+e)*deficitMoment k s ≤
      fairMoment w h (2*n+e) k s ∧
    fairMoment w h (2*n+e) k s ≤
      2*pmf (2*n+e) (1/2) (n+e)*parityOccupation w h k J e s := by
  let P : ℝ := pmf (2*n+e) (1/2) (n+e)
  let E : ℝ := (J : ℝ)*((J : ℝ)+e)/n
  have hP : 0 ≤ P := half_pmf_nonneg _ _
  have hc : ∀ r ∈ Finset.range J,
      (1-E)*P*pathMoment w h k (2*r+e) ∅ s ≤
          pmf (2*n+e) (1/2) (n+e+r)*pathMoment w h k (2*r+e) ∅ s ∧
      pmf (2*n+e) (1/2) (n+e+r)*pathMoment w h k (2*r+e) ∅ s ≤
          P*pathMoment w h k (2*r+e) ∅ s := by
    intro r hr
    have hrJ : r < J := Finset.mem_range.mp hr
    have hrn : r ≤ n := by omega
    have hrR : (r : ℝ) ≤ J := by exact_mod_cast hrJ.le
    have hE : (r : ℝ)*((r : ℝ)+e)/n ≤ E := by
      dsimp [E]
      gcongr
    have hrel := upperRatio_relative_error n hn he r hrn
    have hlo : 1-E ≤ upperRatio n e r := by
      have h' := (abs_le.mp hrel).1
      linarith
    have hu := upperRatio_le_one n he r
    have hM := pathMoment_nonneg w h k (2*r+e) ∅ s
    rw [pmf_eq_ratio_mul_peak]
    change (1-E)*P*_ ≤ upperRatio n e r*P*_ ∧ upperRatio n e r*P*_ ≤ P*_
    exact ⟨mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hlo hP) hM,
      by simpa using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hu hP) hM⟩
  have hlow := Finset.sum_le_sum (fun r hr => (hc r hr).1)
  have hupp := Finset.sum_le_sum (fun r hr => (hc r hr).2)
  simp only [← Finset.mul_sum] at hlow hupp
  have hcorr : 0 ≤ (if e=0 then P*deficitMoment k s else 0) ∧
      (if e=0 then P*deficitMoment k s else 0) ≤ P*deficitMoment k s := by
    have hM := mul_nonneg hP (deficitMoment_nonneg k s)
    split_ifs <;> exact ⟨by positivity,by linarith⟩
  rw [fairMoment_parity_sum w h n k he s,parity_sum_truncate w h ha hh n J k e hJn hs]
  change _ ≤ 2*(∑ r ∈ Finset.range J, pmf (2*n+e) (1/2) (n+e+r)*pathMoment w h k (2*r+e) ∅ s)-
      (if e=0 then P*deficitMoment k s else 0) ∧ _
  change _ ≤ _ ∧ _ ≤ 2*P*(∑ r ∈ Finset.range J, pathMoment w h k (2*r+e) ∅ s)
  unfold parityOccupation
  constructor <;> dsimp [P,E] at * <;> nlinarith [hcorr.1,hcorr.2]

omit [DecidableEq ι] [Nonempty ι] in
lemma weightedMean_bounds (w : Weights ι) (h : ι → ℝ) {a A : ℝ}
    (hh : ∀ i, h i ∈ Icc a A) (hW : 0 < totalWeight w) :
    weightedMean w h ∈ Icc a A := by
  have hlo : a*totalWeight w ≤ ∑ i, w.1 i*h i := by
    rw [totalWeight,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [(w.2 i).1,(hh i).1]
  have hup : (∑ i, w.1 i*h i) ≤ A*totalWeight w := by
    rw [totalWeight,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [(w.2 i).1,(hh i).2]
  change a ≤ (∑ i, w.1 i*h i)/totalWeight w ∧ (∑ i, w.1 i*h i)/totalWeight w ≤ A
  exact ⟨(le_div_iff₀ hW).mpr hlo,(div_le_iff₀ hW).mpr hup⟩

theorem finite_conditional_moment_bounds (w : Weights ι) (h : ι → ℝ)
    {a A : ℝ} (ha : 0 < a) (hh : ∀ i, h i ∈ Icc a A)
    {n J K k e : ℕ} (hn : 0 < n) (he : e ≤ 1) (hk : k ≤ 2)
    (hJn : J ≤ n+1) (hK : 2*J+1 ≤ K)
    (hW : 0 < totalWeight w) (hhalf : 2*(K : ℝ) ≤ totalWeight w)
    {s : ℝ} (hs : s ≤ 2*a*J)
    (hsmall : (J : ℝ)*((J : ℝ)+e)/n ≤ 1)
    (hdrift : 4*A*K/totalWeight w < weightedMean w h) :
    pmf (2*n+e) (1/2) (n+e)*(1-(J : ℝ)*((J : ℝ)+e)/n)*
        potential k (s-A)/(weightedMean w h+4*A*K/totalWeight w)-
        pmf (2*n+e) (1/2) (n+e)*deficitMoment k s ≤ fairMoment w h (2*n+e) k s ∧
    fairMoment w h (2*n+e) k s ≤
      pmf (2*n+e) (1/2) (n+e)*potential k (s+2*A)/(weightedMean w h-4*A*K/totalWeight w) := by
  have hμ := weightedMean_bounds w h hh hW
  have hA : 0 ≤ A := (ha.le.trans hμ.1).trans hμ.2
  have hδ : 0 ≤ 4*A*K/totalWeight w := by positivity
  have hμp : 0 < weightedMean w h+4*A*K/totalWeight w := by linarith [hμ.1]
  have hμm : 0 < weightedMean w h-4*A*K/totalWeight w := sub_pos.mpr hdrift
  have ho := actual_parity_occupation_bounds w h ha hh hk he hK hW hhalf hs
  have hm := fairMoment_vs_occupation (k := k) w h ha.le (fun i => (hh i).1) hn he hJn hs
  have hP := half_pmf_nonneg (2*n+e) (n+e)
  have hE : 0 ≤ 1-(J : ℝ)*((J : ℝ)+e)/n := by linarith
  have hlo : potential k (s-A)/(weightedMean w h+4*A*K/totalWeight w) ≤
      2*parityOccupation w h k J e s := by
    apply (div_le_iff₀ hμp).mpr
    nlinarith [ho.1]
  have hup : 2*parityOccupation w h k J e s ≤
      potential k (s+2*A)/(weightedMean w h-4*A*K/totalWeight w) := by
    apply (le_div_iff₀ hμm).mpr
    nlinarith [ho.2]
  constructor
  · have hx := mul_le_mul_of_nonneg_left hlo (mul_nonneg hP hE)
    rw [← mul_div_assoc] at hx
    exact (by nlinarith : _ ≤
      2*pmf (2*n+e) (1/2) (n+e)*(1-(J : ℝ)*((J : ℝ)+e)/n)*
        parityOccupation w h k J e s-pmf (2*n+e) (1/2) (n+e)*deficitMoment k s).trans hm.1
  · have hx := mul_le_mul_of_nonneg_left hup hP
    rw [← mul_div_assoc] at hx
    exact hm.2.trans (by nlinarith [hx])

end FCAppendix.Affine.Uniform06.EntryParityRenewal
