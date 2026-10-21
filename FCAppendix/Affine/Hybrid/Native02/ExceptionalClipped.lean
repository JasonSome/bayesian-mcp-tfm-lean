import FCAppendix.Affine.Hybrid.EqualRelabel
import FCAppendix.Affine.EqualCapacityLottery
import FCAppendix.Affine.Hybrid.FiniteSelector
import FCAppendix.Affine.Hybrid.HarmonicIntegration
import FCAppendix.Affine.Hybrid.SingletonPayoff
import FCAppendix.Affine.Hybrid.SourceFiniteMenuError
import FCAppendix.Affine.Hybrid.Native02.ExceptionalMenus

set_option maxHeartbeats 1500000
noncomputable section
namespace FCAppendix.Affine.Hybrid.Native02
open Set MeasureTheory Classical Filter Topology
open scoped BigOperators

lemma demand_antitone_price {xi b : ℝ} (hxi : 0 < xi) (hb : 0 < b) :
    Antitone (EqualCapacity.demand xi b) := by
  intro p q hpq
  unfold EqualCapacity.demand
  apply max_le_max le_rfl
  apply min_le_min le_rfl
  apply (div_le_div_iff_of_pos_right hxi).2
  exact sub_le_sub_left ((div_le_div_iff_of_pos_right hb).2 hpq) 1

def oneClippedDemand (xi S n b price : ℝ) : ℝ :=
  (n-price*S)/xi+EqualCapacity.demand xi b price

theorem exists_one_clipped_root {xi S n r b base q₀ : ℝ}
    (hxi : 0 < xi) (hS : 0 < S) (_hb : 0 < b)
    (hq₀ : q₀ ∈ Icc (0:ℝ) 1)
    (reference : (n-base*S)/xi+q₀=r) :
    ∃ price ∈ Icc (base-xi/S) (base+xi/S),
      oneClippedDemand xi S n b price=r ∧
      |price-base| ≤ xi/S := by
  let radius := xi/S
  have hr : 0 < radius := div_pos hxi hS
  have hmul : radius*S=xi := by dsimp [radius]; field_simp
  have hlow : r ≤ oneClippedDemand xi S n b (base-radius) := by
    have hp := (EqualCapacity.demand_bounds xi b (base-radius)).1
    have he : (n-(base-radius)*S)/xi=(n-base*S)/xi+1 := by
      field_simp [hxi.ne']
      nlinarith
    unfold oneClippedDemand
    rw [he]
    linarith [hq₀.2]
  have hhigh : oneClippedDemand xi S n b (base+radius) ≤ r := by
    have hp := (EqualCapacity.demand_bounds xi b (base+radius)).2
    have he : (n-(base+radius)*S)/xi=(n-base*S)/xi-1 := by
      field_simp [hxi.ne']
      nlinarith
    unfold oneClippedDemand
    rw [he]
    linarith [hq₀.1]
  have hc : Continuous (oneClippedDemand xi S n b) :=
    ((continuous_const.sub (continuous_id.mul_const S)).div_const xi).add
      (EqualCapacity.continuous_demand xi b)
  obtain ⟨price,hprice,hroot⟩ := intermediate_value_Icc'
    (show base-radius ≤ base+radius by linarith) hc.continuousOn ⟨hhigh,hlow⟩
  refine ⟨price,hprice,hroot,?_⟩
  exact abs_le.mpr ⟨by linarith [hprice.1],by linarith [hprice.2]⟩

theorem one_clipped_root_unique {xi S n b : ℝ}
    (hxi : 0 < xi) (hS : 0 < S) (hb : 0 < b) :
    StrictAnti (oneClippedDemand xi S n b) := by
  intro p q hpq
  have hd := demand_antitone_price hxi hb hpq.le
  have ha : (n-q*S)/xi < (n-p*S)/xi := by
    apply (div_lt_div_iff_of_pos_right hxi).2
    have hm := mul_lt_mul_of_pos_right hpq hS
    linarith
  unfold oneClippedDemand
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma sum_exposure_as_reciprocal (xi price : ℝ) (b : ι → ℝ) (D : Finset ι) :
    (∑ i ∈ D, exposure xi price (b i)) =
      ((D.card:ℝ)-price*(∑ i ∈ D,(b i)⁻¹))/xi := by
  unfold exposure
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  simp only [div_eq_mul_inv, Finset.mul_sum]

omit [Fintype ι] [DecidableEq ι] in

theorem reciprocal_radius_le {xi U : ℝ} (hxi : 0 < xi) (hU : 0 < U)
    (b : ι → ℝ) (D : Finset ι) (hD : D.Nonempty)
    (hb : ∀ i ∈ D, 0 < b i ∧ b i ≤ U) :
    xi/(∑ i ∈ D,(b i)⁻¹) ≤ xi*U/(D.card:ℝ) := by
  have hS : 0 < ∑ i ∈ D,(b i)⁻¹ :=
    reciprocal_sum_pos b D hD (fun i hi => (hb i hi).1)
  have hN : (0:ℝ) < D.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hD)
  have hbound : (D.card:ℝ)/U ≤ ∑ i ∈ D,(b i)⁻¹ := by
    calc
      (D.card:ℝ)/U = ∑ _i ∈ D,(1:ℝ)/U := by simp [div_eq_mul_inv]
      _ ≤ _ := Finset.sum_le_sum (fun i hi => by
        simpa only [one_div] using
          one_div_le_one_div_of_le (hb i hi).1 (hb i hi).2)
  have hNS : (D.card:ℝ) ≤ U*(∑ i ∈ D,(b i)⁻¹) := by
    have h := (div_le_iff₀ hU).mp hbound
    nlinarith
  apply (div_le_div_iff₀ hS hN).2
  have h := mul_le_mul_of_nonneg_left hNS hxi.le
  nlinarith

structure ClippedOwnerData (ι : Type*) [Fintype ι] [DecidableEq ι] where
  xi : ℝ
  xi_pos : 0 < xi
  xi_lt_one : xi < 1
  bid : ι → ℝ
  bid_pos : ∀ i, 0 < bid i
  owner₁ : Finset ι
  owner₂ : Finset ι
  owners_disjoint : Disjoint owner₁ owner₂
  residual : ℕ
  price : ℝ
  price_pos : 0 < price
  capacity : (∑ i ∈ Finset.univ \ (owner₁ ∪ owner₂),
    EqualCapacity.demand xi (bid i) price) = residual
  own_guard₁ : ∀ i ∈ owner₁, price ≤ bid i
  own_guard₂ : ∀ i ∈ owner₂, price ≤ bid i
  other_guard₁ : ∀ i ∈ owner₁, (1-xi)*bid i ≤ price
  other_guard₂ : ∀ i ∈ owner₂, (1-xi)*bid i ≤ price

namespace ClippedOwnerData
variable (G : ClippedOwnerData ι)

def mixed : Finset ι := Finset.univ \ (G.owner₁ ∪ G.owner₂)
def mixedP (i : ι) : ℝ := EqualCapacity.demand G.xi (G.bid i) G.price
def p₁ (i : ι) : ℝ := if i ∈ G.owner₁ then 1 else if i ∈ G.mixed then G.mixedP i else 0
def p₂ (i : ι) : ℝ := if i ∈ G.owner₂ then 1 else if i ∈ G.mixed then G.mixedP i else 0
def receipt₁ (i : ι) : ℝ := G.bid i*(1-G.xi*G.p₂ i)
def receipt₂ (i : ι) : ℝ := G.bid i*(1-G.xi*G.p₁ i)
def law₁ : FiniteLaw (Finset ι) := ExactCapacity.symmetricLottery G.p₁
def law₂ : FiniteLaw (Finset ι) := ExactCapacity.symmetricLottery G.p₂
def jointLaw : FiniteLaw (Finset ι × Finset ι) := G.law₁.prod G.law₂

lemma mixed_iff (i : ι) : i ∈ G.mixed ↔ i ∉ G.owner₁ ∧ i ∉ G.owner₂ := by
  simp [mixed]

lemma mixed_scalar (i : ι) :
    EqualCapacity.ScalarThreshold G.xi (G.bid i) G.price (G.mixedP i) :=
  EqualCapacity.demand_spec G.xi_pos G.xi_lt_one (G.bid_pos i) G.price

lemma marginal_bounds₁ (i : ι) : 0 ≤ G.p₁ i ∧ G.p₁ i ≤ 1 := by
  unfold p₁
  split_ifs <;> first | exact ⟨(G.mixed_scalar i).1,(G.mixed_scalar i).2.1⟩ | norm_num

lemma marginal_bounds₂ (i : ι) : 0 ≤ G.p₂ i ∧ G.p₂ i ≤ 1 := by
  unfold p₂
  split_ifs <;> first | exact ⟨(G.mixed_scalar i).1,(G.mixed_scalar i).2.1⟩ | norm_num

lemma p₁_sum : (∑ i,G.p₁ i) = (G.owner₁.card+G.residual:ℕ) := by
  have hp (i : ι) : G.p₁ i =
      (if i∈ G.owner₁ then (1:ℝ) else 0)+(if i∈ G.mixed then G.mixedP i else 0) := by
    by_cases hO : i∈ G.owner₁ <;> by_cases hM : i∈ G.mixed
    · exact False.elim (((G.mixed_iff i).mp hM).1 hO)
    · simp [p₁,hO,hM]
    · simp [p₁,hO,hM]
    · simp [p₁,hO,hM]
  have hs : (∑ i∈ G.mixed,G.mixedP i) = G.residual := G.capacity
  calc
    _ = (G.owner₁.card:ℝ)+(∑ i∈ G.mixed,G.mixedP i) := by
      simp_rw [hp,Finset.sum_add_distrib]
      simp
    _ = _ := by rw [hs]; norm_cast

lemma p₂_sum : (∑ i,G.p₂ i) = (G.owner₂.card+G.residual:ℕ) := by
  have hp (i : ι) : G.p₂ i =
      (if i∈ G.owner₂ then (1:ℝ) else 0)+(if i∈ G.mixed then G.mixedP i else 0) := by
    by_cases hO : i∈ G.owner₂ <;> by_cases hM : i∈ G.mixed
    · exact False.elim (((G.mixed_iff i).mp hM).2 hO)
    · simp [p₂,hO,hM]
    · simp [p₂,hO,hM]
    · simp [p₂,hO,hM]
  have hs : (∑ i∈ G.mixed,G.mixedP i) = G.residual := G.capacity
  calc
    _ = (G.owner₂.card:ℝ)+(∑ i∈ G.mixed,G.mixedP i) := by
      simp_rw [hp,Finset.sum_add_distrib]
      simp
    _ = _ := by rw [hs]; norm_cast

lemma law₁_implements : ExactCapacity.Implements G.p₁
    (G.owner₁.card+G.residual) G.law₁ :=
  ExactCapacity.symmetricLottery_implements G.p₁ _
    (fun i => (G.marginal_bounds₁ i).1) (fun i => (G.marginal_bounds₁ i).2) G.p₁_sum

lemma law₂_implements : ExactCapacity.Implements G.p₂
    (G.owner₂.card+G.residual) G.law₂ :=
  ExactCapacity.symmetricLottery_implements G.p₂ _
    (fun i => (G.marginal_bounds₂ i).1) (fun i => (G.marginal_bounds₂ i).2) G.p₂_sum

lemma threshold₁ : Proposer.Threshold G.p₁ G.receipt₁ G.price := by
  have scalar (i : ι) : EqualCapacity.ScalarThreshold G.xi (G.bid i) G.price (G.mixedP i) :=
    G.mixed_scalar i
  constructor
  · intro i hi
    by_cases h₁ : i∈ G.owner₁
    · simp [p₁,h₁] at hi
    · by_cases h₂ : i∈ G.owner₂
      · simpa [receipt₁,p₂,h₂,mul_comm (G.bid i)] using G.other_guard₂ i h₂
      · have hM := (G.mixed_iff i).mpr ⟨h₁,h₂⟩
        have hzero : G.mixedP i=0 := by simpa [p₁,h₁,hM] using hi
        simpa [receipt₁,p₂,h₂,hM] using (scalar i).2.2.1 hzero
  constructor
  · intro i hi
    by_cases h₁ : i∈ G.owner₁
    · have h₂ : i∉G.owner₂ := fun h => (Finset.disjoint_left.mp G.owners_disjoint) h₁ h
      have hM : i∉G.mixed := fun h => ((G.mixed_iff i).mp h).1 h₁
      simpa [receipt₁,p₂,h₂,hM] using G.own_guard₁ i h₁
    · by_cases h₂ : i∈ G.owner₂
      · have hM : i∉G.mixed := fun h => ((G.mixed_iff i).mp h).2 h₂
        simp [p₁,h₁,hM] at hi
      · have hM := (G.mixed_iff i).mpr ⟨h₁,h₂⟩
        have hone : G.mixedP i=1 := by simpa [p₁,h₁,hM] using hi
        simpa [receipt₁,p₂,h₂,hM] using (scalar i).2.2.2.1 hone
  · intro i hlo hhi
    by_cases h₁ : i∈ G.owner₁
    · simp [p₁,h₁] at hhi
    · by_cases h₂ : i∈ G.owner₂
      · have hM : i∉G.mixed := fun h => ((G.mixed_iff i).mp h).2 h₂
        simp [p₁,h₁,hM] at hlo
      · have hM := (G.mixed_iff i).mpr ⟨h₁,h₂⟩
        have hp0 : 0< G.mixedP i := by simpa [p₁,h₁,hM] using hlo
        have hp1 : G.mixedP i<1 := by simpa [p₁,h₁,hM] using hhi
        simpa [receipt₁,p₂,h₂,hM] using (scalar i).2.2.2.2 hp0 hp1

def swap : ClippedOwnerData ι where
  xi := G.xi
  xi_pos := G.xi_pos
  xi_lt_one := G.xi_lt_one
  bid := G.bid
  bid_pos := G.bid_pos
  owner₁ := G.owner₂
  owner₂ := G.owner₁
  owners_disjoint := G.owners_disjoint.symm
  residual := G.residual
  price := G.price
  price_pos := G.price_pos
  capacity := by simpa only [Finset.union_comm] using G.capacity
  own_guard₁ := G.own_guard₂
  own_guard₂ := G.own_guard₁
  other_guard₁ := G.other_guard₂
  other_guard₂ := G.other_guard₁

lemma swap_p₁ : G.swap.p₁=G.p₂ := by
  funext i
  simp only [p₁,p₂,mixed,mixedP,swap,Finset.union_comm]

lemma swap_p₂ : G.swap.p₂=G.p₁ := by
  funext i
  simp only [p₁,p₂,mixed,mixedP,swap,Finset.union_comm]

lemma threshold₂ : Proposer.Threshold G.p₂ G.receipt₂ G.price := by
  have h := G.swap.threshold₁
  have hr : G.swap.receipt₁ = G.receipt₂ := by
    funext i
    unfold receipt₁ receipt₂
    rw [G.swap_p₂]
    rfl
  change Proposer.Threshold G.swap.p₁ G.swap.receipt₁ G.price at h
  rwa [G.swap_p₁, hr] at h

theorem law₁_support_best_response (S : Finset ι) (hS : G.law₁.mass S ≠ 0) :
    Finite.Optimal (G.owner₁.card+G.residual) G.receipt₁ S := by
  apply CommonList.support_optimal _ G.receipt₁ G.law₁
    (fun T hT => (G.law₁_implements.1 T hT).le) _ S hS
  intro ν hν
  rw [Proposer.revenue_marginals,Proposer.revenue_marginals]
  simp only [Proposer.marginal,G.law₁_implements.2]
  exact Proposer.threshold_linear_optimal G.p₁ G.receipt₁ G.price _
    (fun i => (G.marginal_bounds₁ i).1) (fun i => (G.marginal_bounds₁ i).2)
    G.p₁_sum G.price_pos.le G.threshold₁ (Proposer.marginal ν)
    (fun i => ν.prob_nonneg _) (fun i => ν.prob_le_one _)
    (Proposer.marginal_capacity ν _ hν)

theorem law₂_support_best_response (S : Finset ι) (hS : G.law₂.mass S ≠ 0) :
    Finite.Optimal (G.owner₂.card+G.residual) G.receipt₂ S := by
  apply CommonList.support_optimal _ G.receipt₂ G.law₂
    (fun T hT => (G.law₂_implements.1 T hT).le) _ S hS
  intro ν hν
  rw [Proposer.revenue_marginals,Proposer.revenue_marginals]
  simp only [Proposer.marginal,G.law₂_implements.2]
  exact Proposer.threshold_linear_optimal G.p₂ G.receipt₂ G.price _
    (fun i => (G.marginal_bounds₂ i).1) (fun i => (G.marginal_bounds₂ i).2)
    G.p₂_sum G.price_pos.le G.threshold₂ (Proposer.marginal ν)
    (fun i => ν.prob_nonneg _) (fun i => ν.prob_le_one _)
    (Proposer.marginal_capacity ν _ hν)

theorem residual_le_card : G.residual ≤ G.mixed.card := by
  have hsum : (G.residual:ℝ) ≤ G.mixed.card := by
    calc
      (G.residual:ℝ) = ∑ i∈ G.mixed,G.mixedP i := G.capacity.symm
      _ ≤ ∑ _i∈ G.mixed,(1:ℝ) :=
        Finset.sum_le_sum (fun i _ => (G.mixed_scalar i).2.1)
      _ = G.mixed.card := by simp
  exact_mod_cast hsum

theorem mixedP_eq_canonical (i : G.mixed) :
    G.mixedP i = EqualCapacity.kernelMarginal G.xi G.residual
      (fun j : G.mixed => G.bid j) i := by
  have hk : EqualCapacity.IsKernel G.xi G.residual (fun j : G.mixed => G.bid j)
      (fun j : G.mixed => G.mixedP j) := by
    refine ⟨fun j => (G.mixed_scalar j).1,fun j => (G.mixed_scalar j).2.1,?_,
      G.price,G.price_pos.le,?_,?_,?_⟩
    · rw [Fintype.card_coe, min_eq_left G.residual_le_card]
      calc
        _ = ∑ j∈ G.mixed,G.mixedP j := Finset.sum_attach G.mixed _
        _ = G.residual := G.capacity
    · intro j hj; exact (G.mixed_scalar j).2.2.1 hj
    · intro j hj; exact (G.mixed_scalar j).2.2.2.1 hj
    · intro j hj hk; exact (G.mixed_scalar j).2.2.2.2 hj hk
  have hcanon := EqualCapacity.kernelMarginal_spec G.xi_pos G.xi_lt_one G.residual
    (fun j : G.mixed => G.bid j) (fun j => G.bid_pos j)
  exact congrFun (EqualCapacity.isKernel_unique G.xi_pos G.residual
    (fun j : G.mixed => G.bid j) (fun j => G.bid_pos j) _ _ hk hcanon) i

def of_guarded (H : GuardedData ι) : ClippedOwnerData ι where
  xi := H.xi
  xi_pos := H.xi_pos
  xi_lt_one := H.xi_lt_one
  bid := H.bid
  bid_pos := H.bid_pos
  owner₁ := H.owner₁
  owner₂ := H.owner₂
  owners_disjoint := H.owners_disjoint
  residual := H.residual
  price := H.multiplier
  price_pos := H.multiplier_pos
  capacity := by
    calc
      _ = ∑ i∈ H.mixed,exposure H.xi H.multiplier (H.bid i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact demand_eq_exposure H.xi_pos (H.bid_pos i) (H.lower_guard i) (H.upper_guard i)
      _ = H.residual := H.exposure_sum
  own_guard₁ := fun i _ => (H.upper_guard i).le
  own_guard₂ := fun i _ => (H.upper_guard i).le
  other_guard₁ := fun i _ => (H.lower_guard i).le
  other_guard₂ := fun i _ => (H.lower_guard i).le

lemma of_guarded_mixedP (H : GuardedData ι) (i : ι) :
    (of_guarded H).mixedP i=exposure H.xi H.multiplier (H.bid i) :=
  demand_eq_exposure H.xi_pos (H.bid_pos i) (H.lower_guard i) (H.upper_guard i)

lemma of_guarded_p₁ (H : GuardedData ι) : (of_guarded H).p₁=H.p₁ := by
  funext i
  change (if i ∈ H.owner₁ then 1 else if i ∈ H.mixed then (of_guarded H).mixedP i else 0) = _
  rw [of_guarded_mixedP]
  rfl

lemma of_guarded_p₂ (H : GuardedData ι) : (of_guarded H).p₂=H.p₂ := by
  funext i
  change (if i ∈ H.owner₂ then 1 else if i ∈ H.mixed then (of_guarded H).mixedP i else 0) = _
  rw [of_guarded_mixedP]
  rfl

lemma of_guarded_law₁ (H : GuardedData ι) : (of_guarded H).law₁=H.law₁ := by
  unfold law₁ GuardedData.law₁
  rw [of_guarded_p₁]

lemma of_guarded_law₂ (H : GuardedData ι) : (of_guarded H).law₂=H.law₂ := by
  unfold law₂ GuardedData.law₂
  rw [of_guarded_p₂]

end ClippedOwnerData

def maskedMixedBids (E₁ E₂ : Finset ι) (b : ι → ℝ) (i : ι) : ℝ :=
  if i∈ Finset.univ \ (E₁∪E₂) then b i else 0

def canonicalClippedOwnerP (xi : ℝ) (r : ℕ) (E₁ E₂ : Finset ι)
    (b : ι → ℝ) (i : ι) : ℝ :=
  if i∈ E₁ then 1 else EqualCapacity.positiveMarginal xi r (maskedMixedBids E₁ E₂ b) i

def canonicalClippedOwnerLaw (xi : ℝ) (r : ℕ) (E₁ E₂ : Finset ι)
    (b : ι → ℝ) : FiniteLaw (Finset ι) :=
  ExactCapacity.symmetricLottery (canonicalClippedOwnerP xi r E₁ E₂ b)

lemma measurable_maskedMixedBids (E₁ E₂ : Finset ι) :
    Measurable (maskedMixedBids E₁ E₂ : (ι → ℝ) → ι → ℝ) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i∈ Finset.univ \ (E₁∪E₂)
  · simpa [maskedMixedBids,hi] using (measurable_pi_apply i : Measurable (fun b : ι → ℝ => b i))
  · simp only [maskedMixedBids,if_neg hi]
    exact measurable_const

lemma measurable_canonicalClippedOwnerP {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (r : ℕ) (E₁ E₂ : Finset ι) :
    Measurable (canonicalClippedOwnerP xi r E₁ E₂ : (ι → ℝ) → ι → ℝ) := by
  have hm := (EqualCapacity.measurable_positiveMarginal xi r hxi hxi1).comp
    (measurable_maskedMixedBids E₁ E₂)
  apply measurable_pi_lambda
  intro i
  by_cases hi : i∈ E₁
  · simp only [canonicalClippedOwnerP,if_pos hi]
    exact measurable_const
  · simpa only [canonicalClippedOwnerP,if_neg hi, Function.comp_def] using (measurable_pi_apply i).comp hm

lemma canonicalClippedOwnerP_eq (G : ClippedOwnerData ι) :
    canonicalClippedOwnerP G.xi G.residual G.owner₁ G.owner₂ G.bid=G.p₁ := by
  have hsupport : Existence.PayOnceBounded.positiveSupport
      (maskedMixedBids G.owner₁ G.owner₂ G.bid)=G.mixed := by
    ext j
    rw [Existence.PayOnceBounded.mem_positiveSupport]
    by_cases hj : j∈ G.mixed
    · simp [maskedMixedBids,show j∈ Finset.univ \ (G.owner₁∪G.owner₂) from hj,
        hj,G.bid_pos j]
    · simp [maskedMixedBids,show j∉Finset.univ \ (G.owner₁∪G.owner₂) from hj,hj]
  have hrestricted : (fun j : G.mixed => maskedMixedBids G.owner₁ G.owner₂ G.bid j)=
      (fun j : G.mixed => G.bid j) := by
    funext j
    simp only [maskedMixedBids,show j.val∈ Finset.univ \ (G.owner₁∪G.owner₂) from j.2,if_pos]
  funext i
  by_cases h₁ : i∈ G.owner₁
  · simp only [canonicalClippedOwnerP,ClippedOwnerData.p₁,if_pos h₁]
  · by_cases hM : i∈ G.mixed
    · have hpos : i ∈ Existence.PayOnceBounded.positiveSupport
          (maskedMixedBids G.owner₁ G.owner₂ G.bid) := by rwa [hsupport]
      let e : Existence.PayOnceBounded.positiveSupport (maskedMixedBids G.owner₁ G.owner₂ G.bid) ≃ G.mixed :=
        Equiv.setCongr (by simpa only [Finset.coe_inj] using hsupport)
      have hb : (fun j : Existence.PayOnceBounded.positiveSupport (maskedMixedBids G.owner₁ G.owner₂ G.bid) =>
          maskedMixedBids G.owner₁ G.owner₂ G.bid j) =
          (fun j : G.mixed => G.bid j) ∘ e := by
        funext j
        change maskedMixedBids G.owner₁ G.owner₂ G.bid j = G.bid j
        unfold maskedMixedBids
        rw [if_pos (show j.val ∈ Finset.univ \ (G.owner₁ ∪ G.owner₂) from (e j).property)]
      simp only [canonicalClippedOwnerP, ClippedOwnerData.p₁, if_neg h₁, if_pos hM,
        EqualCapacity.positiveMarginal, EqualCapacity.onSupport, dif_pos hpos]
      rw [hb, EqualCapacity.kernelMarginal_equiv e G.xi_pos G.xi_lt_one G.residual
        (fun j : G.mixed => G.bid j) (fun j => G.bid_pos j)]
      exact (G.mixedP_eq_canonical (e ⟨i,hpos⟩)).symm
    · simp only [canonicalClippedOwnerP,ClippedOwnerData.p₁,if_neg h₁,if_neg hM,
        EqualCapacity.positiveMarginal,hsupport,EqualCapacity.onSupport,dif_neg hM]

lemma canonicalClippedOwnerLaw_eq (G : ClippedOwnerData ι) :
    canonicalClippedOwnerLaw G.xi G.residual G.owner₁ G.owner₂ G.bid=G.law₁ := by
  unfold canonicalClippedOwnerLaw ClippedOwnerData.law₁
  rw [canonicalClippedOwnerP_eq]

theorem exists_canonicalClippedSampler {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (r : ℕ) (E₁ E₂ : Finset ι) :
    ∃ f : (ι → ℝ) → unitInterval → Finset ι,
      Measurable (Function.uncurry f) ∧
      (∀ b u,0<(canonicalClippedOwnerLaw xi r E₁ E₂ b).mass (f b u)) ∧
      ∀ b,(volume : Measure unitInterval).map (f b)=
        FiniteLaw.probabilityMeasure (canonicalClippedOwnerLaw xi r E₁ E₂ b) := by
  apply exists_support_sampler (canonicalClippedOwnerLaw xi r E₁ E₂)
  intro S
  exact (ExactCapacity.measurable_symmetricLottery_mass S).comp
    (measurable_canonicalClippedOwnerP hxi hxi1 r E₁ E₂)

def clippedPrivateSample (xi : ℝ) (hxi : 0< xi) (hxi1 : xi<1)
    (r : ℕ) (E₁ E₂ : Finset ι) : (ι → ℝ) → unitInterval → Finset ι :=
  (exists_canonicalClippedSampler hxi hxi1 r E₁ E₂).choose

lemma clippedPrivateSample_spec (xi : ℝ) (hxi : 0< xi) (hxi1 : xi<1)
    (r : ℕ) (E₁ E₂ : Finset ι) :
    Measurable (Function.uncurry (clippedPrivateSample xi hxi hxi1 r E₁ E₂)) ∧
    (∀ b u,0<(canonicalClippedOwnerLaw xi r E₁ E₂ b).mass
      (clippedPrivateSample xi hxi hxi1 r E₁ E₂ b u)) ∧
    ∀ b,(volume : Measure unitInterval).map (clippedPrivateSample xi hxi hxi1 r E₁ E₂ b)=
      FiniteLaw.probabilityMeasure (canonicalClippedOwnerLaw xi r E₁ E₂ b) :=
  (exists_canonicalClippedSampler hxi hxi1 r E₁ E₂).choose_spec

lemma measurable_clippedPrivateSample_all_parameters (xi : ℝ)
    (hxi : 0< xi) (hxi1 : xi<1) :
    Measurable (fun z : (ℕ×Finset ι×Finset ι)×((ι → ℝ)×unitInterval) =>
      clippedPrivateSample xi hxi hxi1 z.1.1 z.1.2.1 z.1.2.2 z.2.1 z.2.2) :=
  measurable_from_prod_countable_right (fun K =>
    (clippedPrivateSample_spec xi hxi hxi1 K.1 K.2.1 K.2.2).1)

theorem clippedPrivateSample_optimal (G : ClippedOwnerData ι) (u : unitInterval) :
    let S := clippedPrivateSample G.xi G.xi_pos G.xi_lt_one
      G.residual G.owner₁ G.owner₂ G.bid u
    S.card=G.owner₁.card+G.residual ∧
      Finite.Optimal (G.owner₁.card+G.residual) G.receipt₁ S := by
  let S := clippedPrivateSample G.xi G.xi_pos G.xi_lt_one
    G.residual G.owner₁ G.owner₂ G.bid u
  have hp := (clippedPrivateSample_spec G.xi G.xi_pos G.xi_lt_one
    G.residual G.owner₁ G.owner₂).2.1 G.bid u
  rw [canonicalClippedOwnerLaw_eq] at hp
  exact ⟨G.law₁_implements.1 S hp.ne',G.law₁_support_best_response S hp.ne'⟩

theorem clippedPrivateSamples_product_law (G : ClippedOwnerData ι) :
    ((volume : Measure unitInterval).prod volume).map (fun u =>
      (clippedPrivateSample G.xi G.xi_pos G.xi_lt_one G.residual G.owner₁ G.owner₂ G.bid u.1,
       clippedPrivateSample G.xi G.xi_pos G.xi_lt_one G.residual G.owner₂ G.owner₁ G.bid u.2)) =
      (FiniteLaw.probabilityMeasure G.law₁).prod (FiniteLaw.probabilityMeasure G.law₂) := by
  have h₁ := clippedPrivateSample_spec G.xi G.xi_pos G.xi_lt_one G.residual G.owner₁ G.owner₂
  have h₂ := clippedPrivateSample_spec G.xi G.xi_pos G.xi_lt_one G.residual G.owner₂ G.owner₁
  have hm₁ := h₁.1.comp ((measurable_const (a := G.bid)).prodMk measurable_id)
  have hm₂ := h₂.1.comp ((measurable_const (a := G.bid)).prodMk measurable_id)
  have hmap := Measure.map_prod_map (volume : Measure unitInterval) (volume : Measure unitInterval) hm₁ hm₂
  change ((volume : Measure unitInterval).map (clippedPrivateSample G.xi G.xi_pos G.xi_lt_one G.residual G.owner₁ G.owner₂ G.bid)).prod ((volume : Measure unitInterval).map (clippedPrivateSample G.xi G.xi_pos G.xi_lt_one G.residual G.owner₂ G.owner₁ G.bid)) = _ at hmap
  calc
    _ = ((volume : Measure unitInterval).map (clippedPrivateSample G.xi G.xi_pos G.xi_lt_one G.residual G.owner₁ G.owner₂ G.bid)).prod ((volume : Measure unitInterval).map (clippedPrivateSample G.xi G.xi_pos G.xi_lt_one G.residual G.owner₂ G.owner₁ G.bid)) := hmap.symm
    _ = _ := by
      rw [h₁.2.2 G.bid,h₂.2.2 G.bid,
        canonicalClippedOwnerLaw_eq G]
      have hswap := canonicalClippedOwnerLaw_eq G.swap
      have he : canonicalClippedOwnerLaw G.xi G.residual G.owner₂ G.owner₁ G.bid=G.law₂ := by
        change canonicalClippedOwnerLaw G.xi G.residual G.owner₂ G.owner₁ G.bid =
          ExactCapacity.symmetricLottery G.swap.p₁ at hswap
        rw [G.swap_p₁] at hswap
        exact hswap
      rw [he]

lemma guarded_reference_without_target (G : GuardedData ι) (i : ι)
    (hi : i ∈ G.mixed) :
    (((G.mixed.erase i).card:ℝ)-G.multiplier*
      (∑ j∈ G.mixed.erase i,(G.bid j)⁻¹))/G.xi+
      exposure G.xi G.multiplier (G.bid i)=G.residual := by
  have hs := G.exposure_sum
  have hsplit := Finset.sum_erase_add G.mixed (fun j => exposure G.xi G.multiplier (G.bid j)) hi
  rw [sum_exposure_as_reciprocal] at hsplit
  linarith

theorem of_single_replacement (G : GuardedData ι) (i : ι)
    (hi : i ∈ G.mixed) (b : ℝ) (hb : 0 < b)
    (hrivals : (G.mixed.erase i).Nonempty)
    (hpositive : G.xi/(∑ j∈ G.mixed.erase i,(G.bid j)⁻¹) < G.multiplier)
    (hmargin : ∀ j, j≠i →
      (1-G.xi)*G.bid j < G.multiplier-G.xi/(∑ k∈ G.mixed.erase i,(G.bid k)⁻¹) ∧
      G.multiplier+G.xi/(∑ k∈ G.mixed.erase i,(G.bid k)⁻¹) < G.bid j) :
    ∃ Q : ClippedOwnerData ι,
      Q.xi=G.xi ∧ Q.bid=Function.update G.bid i b ∧
      Q.owner₁=G.owner₁ ∧ Q.owner₂=G.owner₂ ∧ Q.residual=G.residual ∧
      |Q.price-G.multiplier| ≤ G.xi/(∑ j∈ G.mixed.erase i,(G.bid j)⁻¹) := by
  let D := G.mixed.erase i
  let S := ∑ j∈ D,(G.bid j)⁻¹
  have hS : 0 < S := reciprocal_sum_pos G.bid D hrivals (fun j _ => G.bid_pos j)
  have hq₀ := G.exposure_interior i
  obtain ⟨price,hprice,hroot,hperturb⟩ := exists_one_clipped_root G.xi_pos hS hb
    ⟨hq₀.1.le,hq₀.2.le⟩ (guarded_reference_without_target G i hi)
  have hprice0 : 0 < price := by linarith [hprice.1]
  let bid := Function.update G.bid i b
  have hbid : ∀ j, 0 < bid j := by
    intro j
    by_cases hji : j=i
    · simpa [bid,hji] using hb
    · simpa [bid,Function.update_of_ne hji] using G.bid_pos j
  have hid₁ : i∉G.owner₁ := (G.mixed_iff i).mp hi |>.1
  have hid₂ : i∉G.owner₂ := (G.mixed_iff i).mp hi |>.2
  have hsum : (∑ j∈ G.mixed, EqualCapacity.demand G.xi (bid j) price)=G.residual := by
    have hs : (∑ j∈ D,EqualCapacity.demand G.xi (bid j) price) =
        ((D.card:ℝ)-price*S)/G.xi := by
      calc
        _ = ∑ j∈ D,exposure G.xi price (G.bid j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hji : j≠i := (Finset.mem_erase.mp hj).1
          have hm := hmargin j hji
          rw [show bid j=G.bid j by simp [bid,Function.update_of_ne hji]]
          exact demand_eq_exposure G.xi_pos (G.bid_pos j)
            (hm.1.trans_le hprice.1) (hprice.2.trans_lt hm.2)
        _ = _ := sum_exposure_as_reciprocal _ _ _ _
    have he := Finset.sum_erase_add G.mixed
      (fun j => EqualCapacity.demand G.xi (bid j) price) hi
    change (∑ j∈ D,EqualCapacity.demand G.xi (bid j) price)+
      EqualCapacity.demand G.xi (bid i) price = _ at he
    rw [hs,show bid i=b by simp [bid]] at he
    exact he.symm.trans hroot
  let Q : ClippedOwnerData ι := {
    xi := G.xi
    xi_pos := G.xi_pos
    xi_lt_one := G.xi_lt_one
    bid := bid
    bid_pos := hbid
    owner₁ := G.owner₁
    owner₂ := G.owner₂
    owners_disjoint := G.owners_disjoint
    residual := G.residual
    price := price
    price_pos := hprice0
    capacity := hsum
    own_guard₁ := by
      intro j hj
      have hji : j≠i := fun h => hid₁ (h ▸ hj)
      simpa [bid,Function.update_of_ne hji] using (hprice.2.trans_lt (hmargin j hji).2).le
    own_guard₂ := by
      intro j hj
      have hji : j≠i := fun h => hid₂ (h ▸ hj)
      simpa [bid,Function.update_of_ne hji] using (hprice.2.trans_lt (hmargin j hji).2).le
    other_guard₁ := by
      intro j hj
      have hji : j≠i := fun h => hid₁ (h ▸ hj)
      simpa [bid,Function.update_of_ne hji] using ((hmargin j hji).1.trans_le hprice.1).le
    other_guard₂ := by
      intro j hj
      have hji : j≠i := fun h => hid₂ (h ▸ hj)
      simpa [bid,Function.update_of_ne hji] using ((hmargin j hji).1.trans_le hprice.1).le }
  exact ⟨Q,rfl,rfl,rfl,rfl,rfl,hperturb⟩

def ClippedCountGuard (xi L U : ℝ) (n r : ℕ) : Prop :=
  2≤ n ∧ 0≤ finiteReceiptFactor xi n r ∧
    (1-xi)*U+xi*U/(n-1:ℕ)< finiteReceiptFactor xi n r*L ∧
    finiteReceiptFactor xi n r*U+xi*U/(n-1:ℕ)< L

theorem clipped_owner_of_box {xi L U : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (hL : 0< L) (hLU : L≤ U) (originalBid : ι → ℝ)
    (hbox : ∀ j,originalBid j∈ Icc L U) (E₁ E₂ : Finset ι)
    (hdis : Disjoint E₁ E₂) (r : ℕ)
    (hguard : ClippedCountGuard xi L U (Finset.univ \ (E₁∪E₂)).card r)
    (i : ι) (hi₁ : i∉E₁) (hi₂ : i∉E₂) (b : ℝ) (hb : 0< b) :
    ∃ Q : ClippedOwnerData ι,Q.xi=xi ∧ Q.bid=Function.update originalBid i b ∧
      Q.owner₁=E₁ ∧ Q.owner₂=E₂ ∧ Q.residual=r ∧
      |Q.price-finiteMultiplier xi originalBid (Finset.univ \ (E₁∪E₂)) r| ≤
        xi*U/((Finset.univ \ (E₁∪E₂)).card-1:ℕ) := by
  let D := Finset.univ \ (E₁∪E₂)
  let rad := xi*U/(D.card-1:ℕ)
  have hlarge : 2 ≤ D.card := hguard.1
  have hD : D.Nonempty := Finset.card_pos.mp (by omega)
  have hU : 0< U := hL.trans_le hLU
  have hrad : 0≤ rad := by dsimp [rad]; positivity
  have hlow : (1-xi)*U < finiteReceiptFactor xi D.card r*L := by
    have := hguard.2.2.1
    change (1-xi)*U+rad < _ at this
    linarith
  have hhigh : finiteReceiptFactor xi D.card r*U < L := by
    have := hguard.2.2.2
    change _+rad< L at this
    linarith
  let G := guardedDataOfBox hxi hxi1 hL originalBid hbox E₁ E₂ hdis r hD hguard.2.1 hlow hhigh
  have hi : i∈ G.mixed := by
    change i∈ Finset.univ \ (E₁∪E₂)
    simp [hi₁,hi₂]
  have hsize : (G.mixed.erase i).card=D.card-1 := Finset.card_erase_of_mem hi
  have hne : (G.mixed.erase i).Nonempty := Finset.card_pos.mp (by rw [hsize]; omega)
  have hradbound : G.xi/(∑ j∈ G.mixed.erase i,(G.bid j)⁻¹) ≤ rad := by
    have h := reciprocal_radius_le hxi hU originalBid (G.mixed.erase i) hne
      (fun j _ => ⟨hL.trans_le (hbox j).1,(hbox j).2⟩)
    change xi/(∑ j ∈ G.mixed.erase i, (originalBid j)⁻¹) ≤ _
    simpa only [hsize] using h
  change xi/(∑ j ∈ G.mixed.erase i, (originalBid j)⁻¹) ≤ rad at hradbound
  have hmult := finiteMultiplier_box_bounds hL originalBid D hD r (fun j _ => hbox j) hguard.2.1
  have hpositive : G.xi/(∑ j∈ G.mixed.erase i,(G.bid j)⁻¹)< G.multiplier := by
    have hkU : 0<(1-xi)*U := mul_pos (sub_pos.mpr hxi1) hU
    have hlow' := hguard.2.2.1
    change (1-xi)*U+rad < _ at hlow'
    change xi/(∑ j ∈ G.mixed.erase i, (originalBid j)⁻¹) < finiteMultiplier xi originalBid D r
    have hh : 0 < (1-xi)*U := mul_pos (sub_pos.mpr hxi1) hU
    have hbound0 : (1-xi)*U + rad < finiteReceiptFactor xi D.card r * L := hguard.2.2.1
    linarith only [hmult.1, hradbound, hbound0, hh]
  have hmargin (j : ι) (_hji : j≠i) :
      (1-G.xi)*G.bid j< G.multiplier-G.xi/(∑ k∈ G.mixed.erase i,(G.bid k)⁻¹) ∧
      G.multiplier+G.xi/(∑ k∈ G.mixed.erase i,(G.bid k)⁻¹)< G.bid j := by
    have hj := mul_le_mul_of_nonneg_left (hbox j).2 (sub_pos.mpr hxi1).le
    have hlo' := hguard.2.2.1
    have hhi' := hguard.2.2.2
    change (1-xi)*U+rad < _ at hlo'
    change _+rad < L at hhi'
    change (1-xi)*originalBid j< finiteMultiplier xi originalBid D r-
        xi/(∑ k∈ G.mixed.erase i,(originalBid k)⁻¹) ∧
      finiteMultiplier xi originalBid D r+xi/(∑ k∈ G.mixed.erase i,(originalBid k)⁻¹)< originalBid j
    constructor <;> linarith [hmult.1,hmult.2,(hbox j).1]
  obtain ⟨Q,hxiQ,hbid,hO₁,hO₂,hr,hperturb⟩ :=
    of_single_replacement G i hi b hb hne hpositive hmargin
  exact ⟨Q,hxiQ,hbid,hO₁,hO₂,hr,hperturb.trans hradbound⟩

theorem exists_clipped_count_neighborhood {xi L U h0 : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (hL : 0< L) (hLU : L≤ U)
    (hlo : (1-xi)*U< h0*L) (hhi : h0*U< L) :
    ∃ ε : ℝ,0<ε ∧ ∃ N : ℕ,∀ n r : ℕ,N≤ n →
      |finiteReceiptFactor xi n r-h0|<ε → ClippedCountGuard xi L U n r := by
  have hU : 0< U := hL.trans_le hLU
  let margin := min (h0*L-(1-xi)*U) (L-h0*U)
  have hm : 0< margin := lt_min (sub_pos.mpr hlo) (sub_pos.mpr hhi)
  let τ := margin/4
  have hτ : 0<τ := div_pos hm (by norm_num)
  let ε := τ/U
  have hε : 0<ε := div_pos hτ hU
  obtain ⟨N,hN⟩ := exists_nat_gt (max 2 (xi*U/τ+1))
  refine ⟨ε,hε,N,?_⟩
  intro n r hn hfactor
  have hnN : (N:ℝ)≤ n := by exact_mod_cast hn
  have hn2R : (2:ℝ)< n := (le_max_left _ _).trans_lt (hN.trans_le hnN)
  have hn2 : 2≤ n := by exact_mod_cast hn2R.le
  have hn1 : (0:ℝ)<(n-1:ℕ) := by exact_mod_cast (show 0< n-1 by omega)
  have hncast : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by rw [Nat.cast_sub (by omega)]; norm_num
  have hsize : xi*U/τ+1<(n:ℝ) := (le_max_right _ _).trans_lt (hN.trans_le hnN)
  have hrad : xi*U/(n-1:ℕ)<τ := by
    apply (div_lt_iff₀ hn1).2
    have hs : xi*U/τ<((n-1:ℕ):ℝ) := by rw [hncast]; linarith
    have hs' := (div_lt_iff₀ hτ).mp hs
    nlinarith
  have hfacU : |finiteReceiptFactor xi n r-h0| *U<τ :=
    (lt_div_iff₀ hU).mp hfactor
  have hfacL : |finiteReceiptFactor xi n r-h0| *L<τ :=
    (mul_le_mul_of_nonneg_left hLU (abs_nonneg _)).trans_lt hfacU
  have hloL : h0*L-τ< finiteReceiptFactor xi n r*L := by
    have ha := neg_abs_le (finiteReceiptFactor xi n r-h0)
    have hh := mul_le_mul_of_nonneg_right ha hL.le
    nlinarith
  have hhiU : finiteReceiptFactor xi n r*U< h0*U+τ := by
    have ha := le_abs_self (finiteReceiptFactor xi n r-h0)
    have hh := mul_le_mul_of_nonneg_right ha hU.le
    nlinarith
  have hmlo : 4*τ≤ h0*L-(1-xi)*U := by
    have := min_le_left (h0*L-(1-xi)*U) (L-h0*U)
    dsimp [τ,margin]
    linarith
  have hmhi : 4*τ≤ L-h0*U := by
    have := min_le_right (h0*L-(1-xi)*U) (L-h0*U)
    dsimp [τ,margin]
    linarith
  have hlow : (1-xi)*U+xi*U/(n-1:ℕ)< finiteReceiptFactor xi n r*L := by linarith
  have hg : 0≤ finiteReceiptFactor xi n r := by
    have hkU : 0<(1-xi)*U := mul_pos (sub_pos.mpr hxi1) hU
    have hrad0 : 0≤ xi*U/(n-1:ℕ) := by positivity
    have hprod : 0< finiteReceiptFactor xi n r*L := by linarith
    exact (pos_of_mul_pos_left hprod hL.le).le
  exact ⟨hn2,hg,hlow,by linarith⟩

def clippedPriceFromRivals (xi : ℝ) (b : ι → ℝ) (D : Finset ι) (r : ℕ) (q : ℝ) : ℝ :=
  finiteMultiplier xi b D r+xi*q/(∑ i∈ D,(b i)⁻¹)

omit [Fintype ι] [DecidableEq ι] in
lemma clippedPriceFromRivals_eq_root {xi bTarget price : ℝ}
    (b : ι → ℝ) (D : Finset ι) (r : ℕ)
    (hxi : xi≠0) (hS : (∑ i∈ D,(b i)⁻¹)≠0)
    (hroot : oneClippedDemand xi (∑ i∈ D,(b i)⁻¹) D.card bTarget price=r) :
    price=clippedPriceFromRivals xi b D r (EqualCapacity.demand xi bTarget price) := by
  unfold oneClippedDemand at hroot
  have hr := (div_eq_iff hxi).mp
    (show ((D.card:ℝ)-price*(∑ i∈ D,(b i)⁻¹))/xi =
      (r:ℝ)-EqualCapacity.demand xi bTarget price by linarith)
  unfold clippedPriceFromRivals finiteMultiplier
  rw [← add_div]
  apply (eq_div_iff hS).2
  nlinarith

theorem clippedPriceFromRivals_error (G : Measure ℝ) [IsProbabilityMeasure G]
    {xi L U h0 q : ℝ} (hxi : 0 < xi) (hL : 0 < L) (hLU : L ≤ U)
    (hbox : ∀ᵐ x ∂G,x∈ Icc L U) (hh0 : |h0|≤1)
    (b : ι → ℝ) (hb : ∀ i,b i∈ Icc L U) (D : Finset ι) (r : ℕ)
    (hD : D.Nonempty) (hq : q∈ Icc (0:ℝ) 1) :
    |clippedPriceFromRivals xi b D r q-h0/reciprocalMean G| ≤
      U*|finiteReceiptFactor xi D.card r-h0|+
      U^2*|(∑ i∈ D,(b i)⁻¹)/(D.card:ℝ)-reciprocalMean G|+
      xi*U/(D.card:ℝ) := by
  have hS : 0 < ∑ i∈ D,(b i)⁻¹ :=
    reciprocal_sum_pos b D hD (fun i _ => hL.trans_le (hb i).1)
  have hc : 0 ≤ xi*q/(∑ i∈ D,(b i)⁻¹) := div_nonneg (mul_nonneg hxi.le hq.1) hS.le
  have hqbound : xi*q/(∑ i∈ D,(b i)⁻¹) ≤ xi/(∑ i∈ D,(b i)⁻¹) := by
    apply (div_le_div_iff_of_pos_right hS).2
    exact mul_le_of_le_one_right hxi.le hq.2
  have hradius := reciprocal_radius_le hxi (hL.trans_le hLU) b D hD
    (fun i _ => ⟨hL.trans_le (hb i).1,(hb i).2⟩)
  have hm := finiteMultiplier_error G hL hLU hbox hh0 xi b hb D r hD
  have he : clippedPriceFromRivals xi b D r q-h0/reciprocalMean G =
      (finiteMultiplier xi b D r-h0/reciprocalMean G)+xi*q/(∑ i∈ D,(b i)⁻¹) := by
    unfold clippedPriceFromRivals
    ring
  rw [he]
  exact (abs_add_le _ _).trans (by rw [abs_of_nonneg hc]; linarith)

omit [DecidableEq ι] in
lemma integrable_iid_reciprocal_error (G : Measure ℝ) [IsProbabilityMeasure G]
    {L U : ℝ} (hL : 0 < L) (hbox : ∀ᵐ x ∂G,x∈ Icc L U) (D : Finset ι) :
    Integrable (fun x : ι → ℝ =>
      |(∑ j∈ D,(x j)⁻¹)/(D.card:ℝ)-reciprocalMean G|)
      (Measure.pi (fun _ : ι => G)) := by
  have hi := integrable_reciprocal_of_box G hL hbox
  have hj (j : ι) : Integrable (fun x : ι → ℝ => (x j)⁻¹)
      (Measure.pi (fun _ : ι => G)) := integrable_comp_eval (i:=j) hi
  exact (((integrable_finsetSum D (fun j _ => hj j)).div_const _).sub
    (integrable_const _)).abs

theorem favored_rival_reciprocal_sampling_L1 [Nonempty ι]
    (G : Measure ℝ) [IsProbabilityMeasure G] {L U : ℝ}
    (hL : 0 < L) (hbox : ∀ᵐ x ∂G,x∈ Icc L U)
    (K : ℕ) (hN : 2≤ Fintype.card ι) (hK : 1≤ K) (hKN : K< Fintype.card ι) :
    (∫ x : ι → ℝ,(favoredSetLaw x K).expect (fun E =>
      |(∑ j∈ Finset.univ \ E,(x j)⁻¹)/((Finset.univ \ E).card:ℝ)-reciprocalMean G|)
      ∂Measure.pi (fun _ : ι => G)) ≤
      2*((1/L)/Real.sqrt ((Fintype.card ι-K:ℕ):ℝ)) := by
  let P := Measure.pi (fun _ : ι => G)
  let F : (ι → ℝ) → ι → ℝ := fun x t => (conditionalFill K t).expect (fun E =>
    |(∑ j∈ Finset.univ \ E,(x j)⁻¹)/((Finset.univ \ E).card:ℝ)-reciprocalMean G|)
  have hi (t : ι) : Integrable (fun x => F x t) P := by
    apply integrable_finsetSum
    intro E _
    exact (integrable_iid_reciprocal_error G hL hbox (Finset.univ \ E)).const_mul _
  simp only [favoredSetLaw, FiniteLaw.expect_finiteMix]
  change (∫ x,(rankLaw x).expect (F x) ∂P) ≤ _
  apply integral_rank_expect_le_two P (fun x => x) measurable_id F _ hi
  · exact Filter.Eventually.of_forall (fun x t =>
      (conditionalFill K t).expect_nonneg (fun _ => abs_nonneg _))
  · intro t
    rw [show (∫ x,F x t ∂P) = (conditionalFill K t).expect (fun E =>
      ∫ x,|(∑ j∈ Finset.univ \ E,(x j)⁻¹)/((Finset.univ \ E).card:ℝ)-reciprocalMean G| ∂P) from
      integral_finite_expect P _ _ (fun E =>
        integrable_iid_reciprocal_error G hL hbox (Finset.univ \ E))]
    apply FiniteLaw.expect_le_const_of_support
    intro E hE
    have hcard := (conditionalFill_implements hN hK hKN.le t).1 E hE
    have hD : (Finset.univ \ E).card=Fintype.card ι-K := by
      simp only [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,hcard]
    have hne : (Finset.univ \ E).Nonempty := Finset.card_pos.mp (by rw [hD]; omega)
    simpa only [hD,reciprocalMean] using
      iid_subset_reciprocal_L1 G hL hbox (Finset.univ \ E) hne

theorem sourceOwners_rival_reciprocal_L1 [Nonempty ι]
    (G : Measure ℝ) [IsProbabilityMeasure G] {L U : ℝ}
    (hL : 0 < L) (hbox : ∀ᵐ x ∂G,x∈ Icc L U)
    (K₁ K₂ : ℕ) (hN : 2≤ Fintype.card ι) (hK : K₁+K₂< Fintype.card ι) :
    (∫ x : ι → ℝ,(sourceOwnersLaw x K₁ K₂).expect (fun AB =>
      |(∑ j∈ Finset.univ \ (AB.1∪AB.2),(x j)⁻¹)/
        ((Finset.univ \ (AB.1∪AB.2)).card:ℝ)-reciprocalMean G|)
      ∂Measure.pi (fun _ : ι => G)) ≤
      2*((1/L)/Real.sqrt ((Fintype.card ι-(K₁+K₂):ℕ):ℝ)) := by
  by_cases hz : K₁+K₂=0
  · have hzero : ∀ x : ι → ℝ, sourceOwnersLaw x K₁ K₂ = FiniteLaw.dirac (∅, ∅) := by
      intro x
      simp [sourceOwnersLaw, hz]
    simp_rw [hzero, FiniteLaw.expect_dirac]
    simp only [Finset.union_empty, Finset.sdiff_empty, hz, Nat.sub_zero]
    have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
    have hi := iid_subset_reciprocal_L1 G hL hbox Finset.univ hne
    have hn : 0 ≤ (1/L)/Real.sqrt (Fintype.card ι:ℝ) := by positivity
    simpa only [Finset.card_univ,reciprocalMean] using hi.trans (by linarith :
      (1/L)/Real.sqrt (Fintype.card ι:ℝ) ≤ 2*((1/L)/Real.sqrt (Fintype.card ι:ℝ)))
  · have he (x : ι → ℝ) := sourceOwnersLaw_expect_union x K₁ K₂ hN
      (show 1≤ K₁+K₂ by omega) hK.le
      (fun E => |(∑ j∈ Finset.univ \ E,(x j)⁻¹)/((Finset.univ \ E).card:ℝ)-reciprocalMean G|)
    simp_rw [he]
    exact favored_rival_reciprocal_sampling_L1 G hL hbox (K₁+K₂) hN (by omega) hK

omit [DecidableEq ι] in
lemma ae_iid_rival_box (G : Measure ℝ) [IsProbabilityMeasure G] {L U : ℝ}
    (hbox : ∀ᵐ x ∂G,x∈ Icc L U) :
    ∀ᵐ x ∂Measure.pi (fun _ : ι => G),∀ j,x j∈ Icc L U :=
  ae_all_iff.mpr (fun j =>
    (measurePreserving_eval (fun _ : ι => G) j).quasiMeasurePreserving.ae hbox)

lemma integrable_iid_multiplier (G : Measure ℝ) [IsProbabilityMeasure G]
    {L U : ℝ} (hL : 0< L) (hLU : L≤ U) (hbox : ∀ᵐ x ∂G,x∈ Icc L U)
    (xi : ℝ) (D : Finset ι) (r : ℕ) :
    Integrable (fun x : ι → ℝ => finiteMultiplier xi x D r)
      (Measure.pi (fun _ : ι => G)) := by
  by_cases hD : D.Nonempty
  · apply Integrable.of_bound (measurable_finiteMultiplier xi D r).aestronglyMeasurable
      (|finiteReceiptFactor xi D.card r| *U)
    filter_upwards [ae_iid_rival_box G hbox] with x hx
    have hU := hL.trans_le hLU
    have hs := (subset_reciprocalMean_bounds hL x hx D hD).1
    have hs0 := (one_div_pos.mpr hU).trans_le hs
    have hi : 1/((∑ j∈ D,(x j)⁻¹)/(D.card:ℝ))≤ U := by
      have hh := one_div_le_one_div_of_le (one_div_pos.mpr hU) hs
      simpa using hh
    rw [Real.norm_eq_abs,finiteMultiplier_eq_factor_div_mean xi x D r hD,
      abs_div,abs_of_pos hs0,div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hi (abs_nonneg _)
  · have hE := Finset.not_nonempty_iff_eq_empty.mp hD
    simp only [hE,finiteMultiplier,Finset.card_empty,Nat.cast_zero,Finset.sum_empty,div_zero]
    exact integrable_const _

lemma integrable_clippedPriceFromRivals (G : Measure ℝ) [IsProbabilityMeasure G]
    {xi L U : ℝ} (_hxi : 0< xi) (hL : 0< L) (hLU : L≤ U)
    (hbox : ∀ᵐ x ∂G,x∈ Icc L U) (D : Finset ι) (r : ℕ)
    (q : (ι → ℝ) → ℝ) (hqmeas : Measurable q) (hq : ∀ x,q x∈ Icc (0:ℝ) 1) :
    Integrable (fun x => clippedPriceFromRivals xi x D r (q x))
      (Measure.pi (fun _ : ι => G)) := by
  have hqint : Integrable q (Measure.pi (fun _ : ι => G)) := by
    apply Integrable.of_bound hqmeas.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hq x).1]
      exact (hq x).2)
  have hdenmeas : Measurable (fun x : ι → ℝ => (∑ j∈ D,(x j)⁻¹)⁻¹) :=
    (Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).inv)).inv
  have hdenbound : ∀ᵐ x ∂Measure.pi (fun _ : ι => G), ‖(∑ j∈ D,(x j)⁻¹)⁻¹‖≤ U := by
    filter_upwards [ae_iid_rival_box G hbox] with x hx
    by_cases hD : D.Nonempty
    · have hS : 0<∑ j∈ D,(x j)⁻¹ := reciprocal_sum_pos x D hD (fun j _ => hL.trans_le (hx j).1)
      have hr := reciprocal_radius_le (xi:=1) (by norm_num) (hL.trans_le hLU) x D hD
        (fun j _ => ⟨hL.trans_le (hx j).1,(hx j).2⟩)
      have hc : (1:ℝ)≤ D.card := by exact_mod_cast Finset.card_pos.mpr hD
      have hd : U/(D.card:ℝ)≤ U := div_le_self (hL.trans_le hLU).le hc
      rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hS)]
      simpa only [one_div,one_mul] using (by simpa only [one_mul] using hr : 1 / (∑ j ∈ D, (x j)⁻¹) ≤ U / (D.card : ℝ)).trans hd
    · simp only [Finset.not_nonempty_iff_eq_empty.mp hD,Finset.sum_empty,inv_zero,norm_zero]
      exact (hL.trans_le hLU).le
  have hcorr := ((hqint.bdd_mul (c:=U) hdenmeas.aestronglyMeasurable hdenbound).const_mul xi)
  have hm := integrable_iid_multiplier G hL hLU hbox xi D r
  convert! hm.add hcorr using 1
  funext x
  simp only [clippedPriceFromRivals,div_eq_mul_inv,Pi.add_apply]
  ring

lemma integrable_sourceOwners_expect [Nonempty ι] (G : Measure ℝ)
    (K₁ K₂ : ℕ) (f : (ι → ℝ) → (Finset ι × Finset ι) → ℝ)
    (hf : ∀ AB,Integrable (fun x => f x AB) (Measure.pi (fun _ : ι => G))) :
    Integrable (fun x => (sourceOwnersLaw x K₁ K₂).expect (f x))
      (Measure.pi (fun _ : ι => G)) := by
  apply integrable_finsetSum
  intro AB _
  apply (hf AB).bdd_mul (c:=1)
    (measurable_sourceOwnersLaw_mass K₁ K₂ AB).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg ((sourceOwnersLaw x K₁ K₂).nonneg AB)]
    exact FiniteLaw.mass_le_one _ _)

theorem sourceOwners_clippedPrice_L1 [Nonempty ι]
    (G : Measure ℝ) [IsProbabilityMeasure G] {xi L U h0 : ℝ}
    (hxi : 0< xi) (hL : 0< L) (hLU : L≤ U)
    (hbox : ∀ᵐ x ∂G,x∈ Icc L U) (hh0 : |h0|≤1)
    (K₁ K₂ r : ℕ) (hN : 2≤ Fintype.card ι) (hK : K₁+K₂< Fintype.card ι)
    (q : (ι → ℝ) → (Finset ι × Finset ι) → ℝ)
    (hqmeas : ∀ AB,Measurable (fun x => q x AB))
    (hq : ∀ x AB,q x AB∈ Icc (0:ℝ) 1) :
    let n := Fintype.card ι-(K₁+K₂)
    (∫ x : ι → ℝ,(sourceOwnersLaw x K₁ K₂).expect (fun AB =>
      |clippedPriceFromRivals xi x (Finset.univ \ (AB.1∪AB.2)) r (q x AB)-h0/reciprocalMean G|)
      ∂Measure.pi (fun _ : ι => G)) ≤
      U*|finiteReceiptFactor xi n r-h0|+
      U^2*(2*((1/L)/Real.sqrt (n:ℝ)))+xi*U/(n:ℝ) := by
  let P := Measure.pi (fun _ : ι => G)
  let n := Fintype.card ι-(K₁+K₂)
  let Q : (ι → ℝ) → ℝ := fun x => (sourceOwnersLaw x K₁ K₂).expect (fun AB =>
    |clippedPriceFromRivals xi x (Finset.univ \ (AB.1∪AB.2)) r (q x AB)-h0/reciprocalMean G|)
  let R : (ι → ℝ) → ℝ := fun x => (sourceOwnersLaw x K₁ K₂).expect (fun AB =>
    |(∑ j∈ Finset.univ \ (AB.1∪AB.2),(x j)⁻¹)/
      ((Finset.univ \ (AB.1∪AB.2)).card:ℝ)-reciprocalMean G|)
  have hQi : Integrable Q P := integrable_sourceOwners_expect G K₁ K₂ _ (fun AB =>
    ((integrable_clippedPriceFromRivals G hxi hL hLU hbox _ r
      (fun x => q x AB) (hqmeas AB) (fun x => hq x AB)).sub (integrable_const _)).abs)
  have hRi : Integrable R P := integrable_sourceOwners_expect G K₁ K₂ _ (fun AB =>
    integrable_iid_reciprocal_error G hL hbox (Finset.univ \ (AB.1∪AB.2)))
  have hpoint : ∀ᵐ x ∂P,Q x ≤
      U*|finiteReceiptFactor xi n r-h0|+U^2*R x+xi*U/(n:ℝ) := by
    filter_upwards [ae_iid_rival_box G hbox] with x hx
    have hE := expect_le_expect_on_support (sourceOwnersLaw x K₁ K₂)
      (f:=fun AB => |clippedPriceFromRivals xi x (Finset.univ \ (AB.1∪AB.2)) r (q x AB)-h0/reciprocalMean G|)
      (g:=fun AB => U*|finiteReceiptFactor xi n r-h0|+
        U^2*|(∑ j∈ Finset.univ \ (AB.1∪AB.2),(x j)⁻¹)/
          ((Finset.univ \ (AB.1∪AB.2)).card:ℝ)-reciprocalMean G|+xi*U/(n:ℝ)) (by
      intro AB hAB
      obtain ⟨h₁,h₂,hdis⟩ := sourceOwnersLaw_support x K₁ K₂ hN hK.le AB.1 AB.2 hAB
      have hcard : (Finset.univ \ (AB.1∪AB.2)).card=n := by
        rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
          Finset.card_union_of_disjoint hdis,h₁,h₂]
      have hD : (Finset.univ \ (AB.1∪AB.2)).Nonempty := Finset.card_pos.mp (by rw [hcard]; dsimp [n]; omega)
      simpa only [hcard] using clippedPriceFromRivals_error G hxi hL hLU hbox hh0
        x hx _ r hD (hq x AB))
    simpa only [FiniteLaw.expect_add,FiniteLaw.expect_const,
      FiniteLaw.expect_const_mul,Q,R] using hE
  have hupper : Integrable (fun x => U*|finiteReceiptFactor xi n r-h0|+
      U^2*R x+xi*U/(n:ℝ)) P :=
    ((integrable_const _).add (hRi.const_mul _)).add (integrable_const _)
  have hi := integral_mono_ae hQi hupper hpoint
  change (∫ x, Q x ∂P) ≤ ∫ x, ((fun _ : ι → ℝ => U * |finiteReceiptFactor xi n r-h0|) + (fun x : ι → ℝ => U^2*R x) + (fun _ : ι → ℝ => xi*U/(n:ℝ))) x ∂P at hi
  rw [integral_add' ((integrable_const _).add (hRi.const_mul _)) (integrable_const _),
    integral_add' (integrable_const _) (hRi.const_mul _),integral_const_mul] at hi
  simp only [integral_const,probReal_univ,one_smul] at hi
  rw [integral_const_mul (U^2) R] at hi
  have hR := sourceOwners_rival_reciprocal_L1 G hL hbox K₁ K₂ hN hK
  have hm := mul_le_mul_of_nonneg_left hR (sq_nonneg U)
  change (∫ x,Q x ∂P)≤ _
  linarith

theorem sourceOwners_clippedMenu_bounds [Nonempty ι]
    (G : Measure ℝ) [IsProbabilityMeasure G] {xi eta L U h0 v b M1 : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (heta : eta=1-2*xi) (hv : 0< v)
    (hL : 0< L) (hLU : L≤ U) (hbox : ∀ᵐ x ∂G,x∈ Icc L U) (hh0 : |h0|≤1)
    (K₁ K₂ r : ℕ) (hN : 2≤ Fintype.card ι) (hK : K₁+K₂< Fintype.card ι)
    (q : (ι → ℝ) → (Finset ι × Finset ι) → ℝ)
    (hqmeas : ∀ AB,Measurable (fun x => q x AB)) (hq : ∀ x AB,q x AB∈ Icc (0:ℝ) 1)
    (ht : ∀ᵐ x ∂Measure.pi (fun _ : ι => G),∀ AB,
      (sourceOwnersLaw x K₁ K₂).mass AB≠0 →
      EqualCapacity.ScalarThreshold xi b
        (clippedPriceFromRivals xi x (Finset.univ \ (AB.1∪AB.2)) r (q x AB)) (q x AB))
    (hM1 : ∀ p∈ Icc (0:ℝ) 1,outsideOneAt xi v (h0/reciprocalMean G) p≤ M1) :
    let n := Fintype.card ι-(K₁+K₂)
    let err := U*|finiteReceiptFactor xi n r-h0|+
      U^2*(2*((1/L)/Real.sqrt (n:ℝ)))+xi*U/(n:ℝ)
    (∫ x : ι → ℝ,(sourceOwnersLaw x K₁ K₂).expect (fun AB => q x AB*(v-b))
      ∂Measure.pi (fun _ : ι => G)) ≤ M1+err/(1-xi) ∧
    (∫ x : ι → ℝ,(sourceOwnersLaw x K₁ K₂).expect (fun AB => independentTwo eta v b (q x AB))
      ∂Measure.pi (fun _ : ι => G)) ≤ outsideTwo v (h0/reciprocalMean G)+2*err := by
  let P := Measure.pi (fun _ : ι => G)
  let lam := h0/reciprocalMean G
  let error : (ι → ℝ) → ℝ := fun x => (sourceOwnersLaw x K₁ K₂).expect (fun AB =>
    |clippedPriceFromRivals xi x (Finset.univ \ (AB.1∪AB.2)) r (q x AB)-lam|)
  have herror : Integrable error P := integrable_sourceOwners_expect G K₁ K₂ _ (fun AB =>
    ((integrable_clippedPriceFromRivals G hxi hL hLU hbox _ r
      (fun x => q x AB) (hqmeas AB) (fun x => hq x AB)).sub (integrable_const _)).abs)
  have hqi (AB : Finset ι × Finset ι) : Integrable (fun x => q x AB) P := by
    apply Integrable.of_bound (hqmeas AB).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hq x AB).1]; exact (hq x AB).2)
  have hq2i (AB : Finset ι × Finset ι) : Integrable (fun x => (q x AB)^2) P := by
    apply Integrable.of_bound ((hqmeas AB).pow_const 2).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      nlinarith [(hq x AB).1,(hq x AB).2])
  have hsingle : Integrable (fun x => (sourceOwnersLaw x K₁ K₂).expect
      (fun AB => q x AB*(v-b))) P :=
    integrable_sourceOwners_expect G K₁ K₂ _ (fun AB => (hqi AB).mul_const _)
  have hdouble : Integrable (fun x => (sourceOwnersLaw x K₁ K₂).expect
      (fun AB => independentTwo eta v b (q x AB))) P := by
    apply integrable_sourceOwners_expect G K₁ K₂
    intro AB
    exact (((hqi AB).const_mul 2).sub (hq2i AB)).const_mul v |>.sub
      ((((hqi AB).const_mul 2).sub ((hq2i AB).const_mul (1-eta))).const_mul b)
  have he := sourceOwners_clippedPrice_L1 G hxi hL hLU hbox hh0 K₁ K₂ r hN hK q hqmeas hq
  have hκ : 0<1-xi := sub_pos.mpr hxi1
  constructor
  · have hpoint : ∀ᵐ x ∂P,(sourceOwnersLaw x K₁ K₂).expect (fun AB => q x AB*(v-b))≤
        M1+error x/(1-xi) := by
      filter_upwards [ht] with x hx
      have hp := expect_le_expect_on_support (sourceOwnersLaw x K₁ K₂)
        (fun AB hAB => clipped_singleton_le_reference hxi hxi1 (hx AB hAB) hM1)
      simpa only [div_eq_mul_inv,FiniteLaw.expect_add,FiniteLaw.expect_const,
        FiniteLaw.expect_mul_const,error, lam] using hp
    have hi := integral_mono_ae hsingle ((integrable_const _).add (herror.div_const _)) hpoint
    dsimp only [Pi.add_apply, Pi.mul_apply] at hi
    rw [integral_add (integrable_const _) (herror.div_const _),integral_div] at hi
    simp only [integral_const,probReal_univ,one_smul] at hi
    have he' := (div_le_div_iff_of_pos_right hκ).2 he
    linarith
  · have hpoint : ∀ᵐ x ∂P,(sourceOwnersLaw x K₁ K₂).expect (fun AB => independentTwo eta v b (q x AB))≤
        outsideTwo v lam+2*error x := by
      filter_upwards [ht] with x hx
      have hp := expect_le_expect_on_support (sourceOwnersLaw x K₁ K₂)
        (fun AB hAB => clipped_broadcast_le_reference (lam := lam) hv heta (hx AB hAB))
      simpa only [FiniteLaw.expect_add,FiniteLaw.expect_const,FiniteLaw.expect_const_mul,error] using hp
    have hi := integral_mono_ae hdouble ((integrable_const _).add (herror.const_mul _)) hpoint
    dsimp only [Pi.add_apply, Pi.mul_apply] at hi
    rw [integral_add (integrable_const _) (herror.const_mul _),integral_const_mul] at hi
    simp only [integral_const,probReal_univ,one_smul] at hi
    linarith

def rivalEmbedding : ι ↪ Option ι where
  toFun := some
  inj' := fun _ _ h => Option.some.inj h

def augmentedRivalBids (b : ℝ) (x : ι → ℝ) : Option ι → ℝ
  | none => b
  | some j => x j

omit [Fintype ι] [DecidableEq ι] in
lemma none_not_rivalImage (A : Finset ι) :
    (none : Option ι)∉A.map rivalEmbedding := by simp [rivalEmbedding]

omit [Fintype ι] [DecidableEq ι] in
lemma some_mem_rivalImage (A : Finset ι) (j : ι) :
    some j∈ A.map rivalEmbedding ↔ j∈ A := by simp [rivalEmbedding]

omit [Fintype ι] [DecidableEq ι] in
lemma rivalImages_disjoint {A B : Finset ι} (hdis : Disjoint A B) :
    Disjoint (A.map rivalEmbedding) (B.map rivalEmbedding) := by
  apply Finset.disjoint_left.mpr
  intro k hkA hkB
  cases k with
  | none => exact none_not_rivalImage A hkA
  | some j => exact (Finset.disjoint_left.mp hdis) ((some_mem_rivalImage A j).mp hkA) ((some_mem_rivalImage B j).mp hkB)

lemma augmented_mixed (A B : Finset ι) :
    Finset.univ \ (A.map rivalEmbedding∪B.map rivalEmbedding) =
      insert none ((Finset.univ \ (A∪B)).map rivalEmbedding) := by
  ext k
  cases k with
  | none => simp [rivalEmbedding]
  | some j => simp [rivalEmbedding,Finset.mem_sdiff,Finset.mem_union]

lemma augmented_mixed_card (A B : Finset ι) :
    (Finset.univ \ (A.map rivalEmbedding∪B.map rivalEmbedding)).card =
      (Finset.univ \ (A∪B)).card+1 := by
  rw [augmented_mixed,Finset.card_insert_of_notMem (none_not_rivalImage _),Finset.card_map]

def canonicalExceptionalQ (xi : ℝ) (r : ℕ) (b : ℝ) (x : ι → ℝ)
    (AB : Finset ι × Finset ι) : ℝ :=
  EqualCapacity.positiveMarginal xi r
    (maskedMixedBids (AB.1.map rivalEmbedding) (AB.2.map rivalEmbedding) (augmentedRivalBids b x)) none

omit [Fintype ι] [DecidableEq ι] in
lemma measurable_augmentedRivalBids (b : ℝ) :
    Measurable (augmentedRivalBids b : (ι → ℝ) → Option ι → ℝ) := by
  apply measurable_pi_lambda
  intro k
  cases k with
  | none => exact measurable_const
  | some j => exact measurable_pi_apply j

lemma measurable_canonicalExceptionalQ {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (r : ℕ) (b : ℝ) (AB : Finset ι × Finset ι) :
    Measurable (fun x : ι → ℝ => canonicalExceptionalQ xi r b x AB) :=
  (measurable_pi_apply none).comp
    ((EqualCapacity.measurable_positiveMarginal xi r hxi hxi1).comp
      ((measurable_maskedMixedBids (AB.1.map rivalEmbedding) (AB.2.map rivalEmbedding)).comp
        (measurable_augmentedRivalBids b)))

lemma canonicalExceptionalQ_bounds {xi : ℝ} (hxi : 0< xi) (hxi1 : xi<1)
    (r : ℕ) (b : ℝ) (x : ι → ℝ) (AB : Finset ι × Finset ι) :
    canonicalExceptionalQ xi r b x AB∈ Icc (0:ℝ) 1 := by
  have hp := EqualCapacity.positiveMarginal_spec xi r hxi hxi1
    (maskedMixedBids (AB.1.map rivalEmbedding) (AB.2.map rivalEmbedding) (augmentedRivalBids b x))
  exact ⟨hp.1 none,hp.2.1 none⟩

theorem canonicalExceptionalQ_threshold {xi L U b : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (hL : 0< L) (hLU : L≤ U) (hb : 0< b)
    (x : ι → ℝ) (hx : ∀ j,x j∈ Icc L U) (A B : Finset ι) (hdis : Disjoint A B)
    (r : ℕ) (hguard : ClippedCountGuard xi L U ((Finset.univ \ (A∪B)).card+1) r) :
    EqualCapacity.ScalarThreshold xi b
      (clippedPriceFromRivals xi x (Finset.univ \ (A∪B)) r (canonicalExceptionalQ xi r b x (A,B)))
      (canonicalExceptionalQ xi r b x (A,B)) := by
  let E₁ := A.map rivalEmbedding
  let E₂ := B.map rivalEmbedding
  let D := Finset.univ \ (A∪B)
  let D' := Finset.univ \ (E₁∪E₂)
  let originalBid := augmentedRivalBids L x
  have hbidbox : ∀ j,originalBid j∈ Icc L U := by
    intro j
    cases j with
    | none => exact ⟨le_rfl,hLU⟩
    | some k => exact hx k
  have hdis' : Disjoint E₁ E₂ := rivalImages_disjoint hdis
  have hcard : D'.card=D.card+1 := augmented_mixed_card A B
  have hguard' : ClippedCountGuard xi L U D'.card r := by rw [hcard]; exact hguard
  obtain ⟨Q,hQxi,hQbid,hQO₁,hQO₂,hQr,hQbound⟩ := clipped_owner_of_box
    hxi hxi1 hL hLU originalBid hbidbox E₁ E₂ hdis' r hguard' none
    (none_not_rivalImage A) (none_not_rivalImage B) b hb
  have hbid : Q.bid=augmentedRivalBids b x := by
    rw [hQbid]
    funext j
    cases j <;> simp [originalBid,augmentedRivalBids]
  have hq : canonicalExceptionalQ xi r b x (A,B)=Q.mixedP none := by
    have hp := congrFun (canonicalClippedOwnerP_eq Q) none
    simpa [canonicalExceptionalQ,canonicalClippedOwnerP,ClippedOwnerData.p₁,
      ClippedOwnerData.mixed,hQxi,hbid,hQO₁,hQO₂,hQr,E₁,E₂,rivalEmbedding] using hp
  have hscalar : EqualCapacity.ScalarThreshold xi b Q.price
      (canonicalExceptionalQ xi r b x (A,B)) := by
    have hs := Q.mixed_scalar none
    rw [hQxi,hbid,←hq] at hs
    exact hs
  have hD' : D'.Nonempty := Finset.card_pos.mp (by have := hguard'.1; omega)
  have hD : D.Nonempty := by
    apply Finset.card_pos.mp
    have hlarge : 2 ≤ D.card + 1 := hguard.1
    omega
  have hmult := finiteMultiplier_box_bounds hL originalBid D' hD' r
    (fun j _ => hbidbox j) hguard'.2.1
  have hpriceLower : (1-xi)*U< Q.price := by
    have hdiff := (abs_le.mp hQbound).1
    have hg := hguard'.2.2.1
    linarith [hmult.1]
  have hpriceUpper : Q.price< L := by
    have hdiff := (abs_le.mp hQbound).2
    have hg := hguard'.2.2.2
    linarith [hmult.2]
  have hsum : (∑ j∈ D,EqualCapacity.demand xi (x j) Q.price)=
      ((D.card:ℝ)-Q.price*(∑ j∈ D,(x j)⁻¹))/xi := by
    calc
      _ = ∑ j∈ D,exposure xi Q.price (x j) := by
        apply Finset.sum_congr rfl
        intro j _
        apply demand_eq_exposure hxi (hL.trans_le (hx j).1)
        · exact (mul_le_mul_of_nonneg_left (hx j).2 (sub_pos.mpr hxi1).le).trans_lt hpriceLower
        · exact hpriceUpper.trans_le (hx j).1
      _ = _ := sum_exposure_as_reciprocal _ _ _ _
  have hcapacity := Q.capacity
  rw [hQxi,hbid,hQO₁,hQO₂,hQr] at hcapacity
  change (∑ j∈ Finset.univ \ (A.map rivalEmbedding∪B.map rivalEmbedding),
    EqualCapacity.demand xi (augmentedRivalBids b x j) Q.price)=(r:ℝ) at hcapacity
  rw [augmented_mixed,Finset.sum_insert (none_not_rivalImage _),Finset.sum_map] at hcapacity
  simp only [augmentedRivalBids,rivalEmbedding] at hcapacity
  change EqualCapacity.demand xi b Q.price+(∑ j∈ D,EqualCapacity.demand xi (x j) Q.price)=r at hcapacity
  rw [hsum] at hcapacity
  have hroot : oneClippedDemand xi (∑ j∈ D,(x j)⁻¹) D.card b Q.price=r := by
    unfold oneClippedDemand
    linarith
  have hS : 0<∑ j∈ D,(x j)⁻¹ := reciprocal_sum_pos x D hD (fun j _ => hL.trans_le (hx j).1)
  have hprice := clippedPriceFromRivals_eq_root x D r hxi.ne' hS.ne' hroot
  have heq : Q.price=clippedPriceFromRivals xi x D r (canonicalExceptionalQ xi r b x (A,B)) := by
    rw [hprice]
    have hqt : EqualCapacity.demand xi b Q.price=canonicalExceptionalQ xi r b x (A,B) :=
      (scalarThreshold_eq_demand hxi hxi1 hb hscalar).symm
    rw [hqt]
  rw [←heq]
  exact hscalar

theorem primitive_excluded_owner_menus [Nonempty ι]
    (G : Measure ℝ) [IsProbabilityMeasure G] {xi eta L U h0 v b M1 : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (heta : eta=1-2*xi) (hv : 0< v) (hb : 0< b)
    (hL : 0< L) (hLU : L≤ U) (hbox : ∀ᵐ x ∂G,x∈ Icc L U) (hh0 : |h0|≤1)
    (K₁ K₂ r : ℕ) (hN : 2≤ Fintype.card ι) (hK : K₁+K₂< Fintype.card ι)
    (hguard : ClippedCountGuard xi L U (Fintype.card ι-(K₁+K₂)+1) r)
    (hM1 : ∀ p∈ Icc (0:ℝ) 1,outsideOneAt xi v (h0/reciprocalMean G) p≤ M1) :
    let n := Fintype.card ι-(K₁+K₂)
    let err := U*|finiteReceiptFactor xi n r-h0|+
      U^2*(2*((1/L)/Real.sqrt (n:ℝ)))+xi*U/(n:ℝ)
    (∫ x : ι → ℝ,(sourceOwnersLaw x K₁ K₂).expect (fun AB =>
      canonicalExceptionalQ xi r b x AB*(v-b)) ∂Measure.pi (fun _ : ι => G)) ≤ M1+err/(1-xi) ∧
    (∫ x : ι → ℝ,(sourceOwnersLaw x K₁ K₂).expect (fun AB =>
      independentTwo eta v b (canonicalExceptionalQ xi r b x AB))
      ∂Measure.pi (fun _ : ι => G)) ≤ outsideTwo v (h0/reciprocalMean G)+2*err := by
  apply sourceOwners_clippedMenu_bounds G hxi hxi1 heta hv hL hLU hbox hh0
    K₁ K₂ r hN hK (canonicalExceptionalQ xi r b)
    (measurable_canonicalExceptionalQ hxi hxi1 r b)
    (fun x AB => canonicalExceptionalQ_bounds hxi hxi1 r b x AB) _ hM1
  filter_upwards [ae_iid_rival_box G hbox] with x hx
  intro AB hAB
  obtain ⟨h₁,h₂,hdis⟩ := sourceOwnersLaw_support x K₁ K₂ hN hK.le AB.1 AB.2 hAB
  have hcard : (Finset.univ \ (AB.1∪AB.2)).card=Fintype.card ι-(K₁+K₂) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
      Finset.card_union_of_disjoint hdis,h₁,h₂]
  exact canonicalExceptionalQ_threshold hxi hxi1 hL hLU hb x hx AB.1 AB.2 hdis r
    (by rw [hcard]; exact hguard)

lemma reciprocal_reference_bounds (G : Measure ℝ) [IsProbabilityMeasure G]
    {L U h0 : ℝ} (hL : 0< L) (hLU : L≤ U) (hbox : ∀ᵐ b ∂G,b∈ Icc L U)
    (hh0 : 0≤ h0) : h0*L≤ h0/reciprocalMean G ∧ h0/reciprocalMean G≤ h0*U := by
  have hU : 0< U := hL.trans_le hLU
  have hH := reciprocalMean_bounds G hL hbox
  have hH0 : 0< reciprocalMean G := (one_div_pos.mpr hU).trans_le hH.1
  constructor
  · apply (le_div_iff₀ hH0).2
    have hh := mul_le_mul_of_nonneg_left hH.2 (mul_nonneg hh0 hL.le)
    have he : h0*L*(1/L)=h0 := by field_simp
    nlinarith only [hh,he]
  · apply (div_le_iff₀ hH0).2
    have hh := mul_le_mul_of_nonneg_left hH.1 (mul_nonneg hh0 hU.le)
    have he : h0*U*(1/U)=h0 := by field_simp
    nlinarith only [hh,he]

theorem primitive_excluded_owner_zero_menu [Nonempty ι]
    (G : Measure ℝ) [IsProbabilityMeasure G]
    {xi eta d L U R W h0 vmin vmax v b : ℝ}
    (hxi : 0< xi) (hxi1 : xi<1) (heta : eta=1-2*xi)
    (hd : 0< d) (hdb : d≤ b) (hbR : b≤ R) (hvW : |v|≤ W)
    (hL : 0< L) (hLU : L≤ U) (hbox : ∀ᵐ x ∂G,x∈ Icc L U)
    (hh0 : 0< h0) (hh01 : h0≤1) (hUv : U< vmin) (hvmin : vmin≤ v) (hvmax : v≤ vmax)
    (hboxlo : (1-xi)*U< h0*L) (hboxhi : h0*U< L) (hout : b≤ L ∨ U≤ b)
    (hgapL : 0< lowerEndpointGap xi (h0*L) L vmin)
    (hgapU : 0< upperEndpointGap xi (h0*U) U vmax)
    (K₁ K₂ r : ℕ) (hN : 2≤ Fintype.card ι) (hK : K₁+K₂< Fintype.card ι)
    (hguard : ClippedCountGuard xi L U (Fintype.card ι-(K₁+K₂)+1) r) :
    let n := Fintype.card ι-(K₁+K₂)
    let err := U*|finiteReceiptFactor xi n r-h0|+
      U^2*(2*((1/L)/Real.sqrt (n:ℝ)))+xi*U/(n:ℝ)
    let gap := min (lowerEndpointGap xi (h0*L) L vmin) (upperEndpointGap xi (h0*U) U vmax)
    (∫ x : ι → ℝ,(sourceOwnersLaw x K₁ K₂).expect (fun AB =>
      independentTwo eta v b (canonicalExceptionalQ xi r b x AB))
      ∂Measure.pi (fun _ : ι => G))≤ outsideTwo v (h0/reciprocalMean G)-vmin*gap^2+
        (broadcastExposureModulus eta W R/(xi*d))*err := by
  let P := Measure.pi (fun _ : ι => G)
  let q := canonicalExceptionalQ (ι := ι) xi r b
  let lam := h0/reciprocalMean G
  let gap := min (lowerEndpointGap xi (h0*L) L vmin) (upperEndpointGap xi (h0*U) U vmax)
  let B := broadcastExposureModulus eta W R/(xi*d)
  let error : (ι → ℝ) → ℝ := fun x => (sourceOwnersLaw x K₁ K₂).expect (fun AB =>
    |clippedPriceFromRivals xi x (Finset.univ \ (AB.1∪AB.2)) r (q x AB)-lam|)
  have hqm (AB : Finset ι × Finset ι) : Measurable (fun x : ι → ℝ => q x AB) :=
    measurable_canonicalExceptionalQ hxi hxi1 r b AB
  have hqb (x : ι → ℝ) (AB : Finset ι × Finset ι) : q x AB∈ Icc (0:ℝ) 1 :=
    canonicalExceptionalQ_bounds hxi hxi1 r b x AB
  have herror : Integrable error P := integrable_sourceOwners_expect G K₁ K₂ _ (fun AB =>
    ((integrable_clippedPriceFromRivals G hxi hL hLU hbox _ r
      (fun x => q x AB) (hqm AB) (fun x => hqb x AB)).sub (integrable_const _)).abs)
  have hb : 0< b := hd.trans_le hdb
  have hBR : |b|≤ R := by rw [abs_of_pos hb]; exact hbR
  have hB : 0≤ B := div_nonneg
    (broadcastExposureModulus_nonneg ((abs_nonneg v).trans hvW) (hb.le.trans hbR))
    (mul_pos hxi hd).le
  have hpay : Integrable (fun x : ι → ℝ => (sourceOwnersLaw x K₁ K₂).expect
      (fun AB => independentTwo eta v b (q x AB))) P := by
    apply integrable_sourceOwners_expect G K₁ K₂
    intro AB
    have hm : Measurable (fun x : ι → ℝ => independentTwo eta v b (q x AB)) := by
      unfold independentTwo
      exact (measurable_const.mul (((hqm AB).const_mul 2).sub ((hqm AB).pow_const 2))).sub
        (measurable_const.mul (((hqm AB).const_mul 2).sub
          (((hqm AB).pow_const 2).const_mul (1-eta))))
    apply Integrable.of_bound hm.aestronglyMeasurable (broadcastExposureModulus eta W R)
    exact ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs]
      exact independentTwo_abs_le hvW hBR (hqb x AB))
  have hlam := reciprocal_reference_bounds G hL hLU hbox hh0.le
  have hpoint : ∀ᵐ x ∂P,(sourceOwnersLaw x K₁ K₂).expect
      (fun AB => independentTwo eta v b (q x AB))≤ outsideTwo v lam-vmin*gap^2+B*error x := by
    filter_upwards [ae_iid_rival_box G hbox] with x hx
    have he := expect_le_expect_on_support (sourceOwnersLaw x K₁ K₂)
      (f:=fun AB => independentTwo eta v b (q x AB))
      (g:=fun AB => outsideTwo v lam-vmin*gap^2+B*
        |clippedPriceFromRivals xi x (Finset.univ \ (AB.1∪AB.2)) r (q x AB)-lam|) (by
        intro AB hAB
        obtain ⟨h₁,h₂,hdis⟩ := sourceOwnersLaw_support x K₁ K₂ hN hK.le AB.1 AB.2 hAB
        have hcard : (Finset.univ \ (AB.1∪AB.2)).card=Fintype.card ι-(K₁+K₂) := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,
            Finset.card_union_of_disjoint hdis,h₁,h₂]
        have ht := canonicalExceptionalQ_threshold hxi hxi1 hL hLU hb x hx AB.1 AB.2 hdis r
          (by rw [hcard]; exact hguard)
        exact clipped_broadcast_le_reference_zero_gap hxi hxi1 heta hd hdb hbR hvW
          hL hLU hUv hvmin hvmax (mul_pos hh0 hL) hlam.1 hlam.2
          hboxlo hboxhi hout ht hgapL hgapU)
    simpa only [FiniteLaw.expect_add,FiniteLaw.expect_const,FiniteLaw.expect_const_mul,error] using he
  have hi := integral_mono_ae hpay ((integrable_const _).add (herror.const_mul B)) hpoint
  dsimp only [Pi.add_apply] at hi
  rw [integral_add (integrable_const _) (herror.const_mul B),integral_const_mul] at hi
  simp only [integral_const,probReal_univ,one_smul] at hi
  have herr := sourceOwners_clippedPrice_L1 G hxi hL hLU hbox
    (by rw [abs_of_pos hh0]; exact hh01) K₁ K₂ r hN hK q hqm hqb
  have hm := mul_le_mul_of_nonneg_left herr hB
  dsimp only
  convert! hi.trans (add_le_add le_rfl hm) using 1

lemma rival_factor_error {xi : ℝ} (hxi : 0 ≤ xi) {n r : ℕ}
    (hn : 0< n) (hr : r≤ n+1) :
    |finiteReceiptFactor xi n r-finiteReceiptFactor xi (n+1) r| ≤ xi/(n:ℝ) := by
  have hn0 : (0:ℝ)< n := Nat.cast_pos.mpr hn
  have hn1 : (0:ℝ)<(n+1:ℕ) := by positivity
  have hn1R : (0:ℝ)<(n:ℝ)+1 := by positivity
  have he : finiteReceiptFactor xi n r-finiteReceiptFactor xi (n+1) r =
      -(xi*(r:ℝ)/((n:ℝ)*(n+1))) := by
    unfold finiteReceiptFactor
    push_cast
    field_simp [hn0.ne',hn1R.ne']
    ring
  rw [he,abs_neg,abs_of_nonneg (by positivity)]
  apply (div_le_div_iff₀ (mul_pos hn0 (by positivity)) hn0).2
  have hrR : (r:ℝ)≤(n:ℝ)+1 := by exact_mod_cast hr
  have hm := mul_le_mul_of_nonneg_left hrR (mul_nonneg hxi hn0.le)
  nlinarith

def clippedSamplingError (xi L U : ℝ) (n : ℕ) : ℝ :=
  U^2*(2*((1/L)/Real.sqrt (n:ℝ)))+2*xi*U/(n:ℝ)

lemma clippedSamplingError_tendsto_zero (xi L U : ℝ) :
    Filter.Tendsto (clippedSamplingError xi L U) Filter.atTop (nhds 0) := by
  have hn : Filter.Tendsto (fun n : ℕ => (n:ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hr : Filter.Tendsto (fun n : ℕ => Real.sqrt (n:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_sqrt_atTop.comp hn
  have ha : Filter.Tendsto (fun n : ℕ => (1/L)/Real.sqrt (n:ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hr
  have hb : Filter.Tendsto (fun n : ℕ => (2*xi*U)/(n:ℝ)) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hn
  convert! ((ha.const_mul 2).const_mul (U^2)).add hb using 1
  simp only [mul_zero,add_zero]

theorem eventually_source_clipped_guards_and_error
    (a h rho z xi L U : ℝ)
    (ha : 0< a) (hz0 : 0≤ z) (hz1 : z<1) (hxi : 0< xi) (hxi1 : xi<1)
    (hL : 0< L) (hLU : L≤ U) (hlower : h/2< rho) (hupper : rho< a+h/2)
    (hq0 : 0< sourceExposure a h rho z) (hq1 : sourceExposure a h rho z<1)
    (hboxlo : (1-xi)*U<(1-xi*sourceExposure a h rho z)*L)
    (hboxhi : (1-xi*sourceExposure a h rho z)*U< L)
    (c : ℕ → ℕ) (hc : Filter.Tendsto (fun M => (c M:ℝ)/(M:ℝ)) Filter.atTop (nhds rho))
    (eps : ℝ) (heps : 0< eps) :
    ∃ delta : ℝ,0< delta ∧ ∀ᶠ M : ℕ in Filter.atTop,∀ A H₀ H₁ : ℕ,
      |(A:ℝ)-(M:ℝ)*a|≤ M*delta →
      |(H₀:ℝ)-(M:ℝ)*(h/2)|≤ M*delta →
      |(H₁:ℝ)-(M:ℝ)*(h/2)|≤ M*delta →
      let d₀ := activeResidual (c M) A H₀
      let d₁ := activeResidual (c M) A H₁
      let small := min d₀ d₁
      let ell := exclusiveQuota z A
      let gap := residualDifference d₀ d₁
      let K := 2*ell+gap
      let r := small-ell
      let D := A-K
      let n := D-1
      3≤ A ∧ 2≤ D ∧ ell< small ∧ K≤ A-1 ∧ r≤ n ∧
      ClippedCountGuard xi L U D r ∧
      U*|finiteReceiptFactor xi n r-(1-xi*sourceExposure a h rho z)|+
        U^2*(2*((1/L)/Real.sqrt (n:ℝ)))+xi*U/(n:ℝ)< eps := by
  let h0 := 1-xi*sourceExposure a h rho z
  have hU : 0< U := hL.trans_le hLU
  obtain ⟨eta,heta,Nguard,hguard⟩ := exists_clipped_count_neighborhood
    hxi hxi1 hL hLU hboxlo hboxhi
  let tau := min eta (eps/(2*U))
  have htau : 0< tau := lt_min heta (div_pos heps (mul_pos (by norm_num) hU))
  have hneighborhood := source_menu_neighborhood a h rho z xi L U tau
    ha hz1 hxi hxi1 hq0 hq1 hboxlo hboxhi htau
  obtain ⟨delta,hdelta,hcounts⟩ := eventually_typical_count_point_mem a h rho z hz0 hz1.le
    hlower hupper c hc _ hneighborhood
  have hsample : ∀ᶠ n : ℕ in Filter.atTop,clippedSamplingError xi L U n< eps/2 :=
    (clippedSamplingError_tendsto_zero xi L U).eventually
      (Iio_mem_nhds (half_pos heps))
  obtain ⟨T,hT⟩ := Filter.eventually_atTop.mp hsample
  let N := max 3 (max Nguard (T+1))
  have hlarge := eventually_linear_counts_large (half_pos ha)
    (half_pos (mul_pos ha (sub_pos.mpr hz1))) N
  refine ⟨delta,hdelta,?_⟩
  filter_upwards [hcounts,hlarge,Filter.eventually_gt_atTop (0:ℕ)] with M hMc hMl hM
  intro A H₀ H₁ hA hH₀ hH₁
  let d₀ := activeResidual (c M) A H₀
  let d₁ := activeResidual (c M) A H₁
  let small := min d₀ d₁
  let ell := exclusiveQuota z A
  let gap := residualDifference d₀ d₁
  let K := 2*ell+gap
  let r := small-ell
  let D := A-K
  let n := D-1
  let p := finiteCountPoint M A small ell gap
  have hp := hMc A H₀ H₁ hA hH₀ hH₁
  change NormalizedGuardRegion xi L U p ∧ a/2< p 0 ∧
    a*(1-z)/2< normalizedMixed p ∧ |normalizedOwnerShare p-z|< tau ∧
    |normalizedFactor xi p-h0|< tau at hp
  obtain ⟨hsmall,hK⟩ := count_region_integer_tests M A small ell gap hM hp.1
  have hm : (0:ℝ)< M := Nat.cast_pos.mpr hM
  have hDreal : (D:ℝ)=(A:ℝ)-2*ell-gap := by
    dsimp [D,K]
    rw [Nat.cast_sub hK.le]
    push_cast
    ring
  have hrreal : (r:ℝ)=(small:ℝ)-ell := by dsimp [r]; rw [Nat.cast_sub hsmall.le]
  have hDM : normalizedMixed p=(D:ℝ)/(M:ℝ) := by
    dsimp [p,normalizedMixed,finiteCountPoint]
    rw [hDreal]
    ring
  have hRM : normalizedResidual p=(r:ℝ)/(M:ℝ) := by
    dsimp [p,normalizedResidual,finiteCountPoint]
    rw [hrreal]
    ring
  have hfactor : normalizedFactor xi p=finiteReceiptFactor xi D r :=
    normalizedFactor_count_eq M A small ell gap hM hsmall hK
  have hnlarge := hMl A D hp.2.1 (by rw [←hDM]; exact hp.2.2.1)
  have hAN : 3≤ A := (le_max_left _ _).trans hnlarge.1
  have hDguard : Nguard≤ D := (le_max_left Nguard (T+1)).trans ((le_max_right _ _).trans hnlarge.2)
  have hDT : T+1≤ D := (le_max_right Nguard (T+1)).trans ((le_max_right _ _).trans hnlarge.2)
  have hD3 : 3≤ D := (le_max_left _ _).trans hnlarge.2
  have hnpos : 0< n := by dsimp [n]; omega
  have hnT : T≤ n := by dsimp [n]; omega
  have hDr : r< D := by
    have h := hp.1.2.2.1
    rw [hRM,hDM] at h
    have h' := (div_lt_div_iff_of_pos_right hm).mp h
    exact_mod_cast h'
  have hrn : r≤ n := by dsimp [n]; omega
  have hfactorClose : |finiteReceiptFactor xi D r-h0|< tau := by
    rw [←hfactor]; exact hp.2.2.2.2
  have hClipped : ClippedCountGuard xi L U D r :=
    hguard D r hDguard (hfactorClose.trans_le (min_le_left _ _))
  have hsampleN := hT n hnT
  have hstep := rival_factor_error hxi.le (n:=n) (r:=r) hnpos (by omega)
  have hnEq : n+1=D := by dsimp [n]; omega
  rw [hnEq] at hstep
  have htri : |finiteReceiptFactor xi n r-h0|≤
      xi/(n:ℝ)+|finiteReceiptFactor xi D r-h0| :=
    (abs_sub_le _ (finiteReceiptFactor xi D r) _).trans (add_le_add hstep le_rfl)
  have htriU := mul_le_mul_of_nonneg_left htri hU.le
  have hfactorSmall : U*|finiteReceiptFactor xi D r-h0|< eps/2 := by
    have ht : tau≤ eps/(2*U) := min_le_right _ _
    have hnum := (lt_div_iff₀ (mul_pos (by norm_num) hU)).mp (hfactorClose.trans_le ht)
    nlinarith
  change 3 ≤ A ∧ 2 ≤ D ∧ ell < small ∧ K ≤ A-1 ∧ r ≤ n ∧ ClippedCountGuard xi L U D r ∧ _
  refine ⟨hAN,by omega,hsmall,by dsimp only [D] at hD3; omega,hrn,hClipped,?_⟩
  dsimp [clippedSamplingError] at hsampleN
  have hsame : U*(xi/(n:ℝ))+xi*U/(n:ℝ)=2*xi*U/(n:ℝ) := by ring
  nlinarith

end FCAppendix.Affine.Hybrid.Native02
