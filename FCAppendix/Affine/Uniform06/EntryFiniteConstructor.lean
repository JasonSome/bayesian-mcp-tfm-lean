import FCAppendix.Affine.Uniform06.EntryPopulationMargins
import FCAppendix.Affine.Uniform06.EntryLiteralCanonicalTransfer
import FCAppendix.Affine.Uniform06.CapacityFloor

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.EntryFiniteConstructor

open MeasureTheory Set Filter Topology LowBody
open FCAppendix.Affine.Uniform07 FCAppendix.Affine.ClippedResidual
open LiteralExperiment LiteralPrefixStieltjes ActualEntryGoodGeometry
open EntryPopulationMargins EntryLiteralResponseGeometry EntryLiteralCanonicalTransfer
open SourcePrefixConstructor

def lowerPrice (i : Row) : ℝ := entry i-cutoff i/1000
def gamma (i : Row) : ℝ := demandSlack i (radius i) (ReceiptGap.cap i)
def residualMass (i : Row) : ℝ := rho-(1-cutoff i)/2
def roomMass (i : Row) : ℝ := cutoff i-residualMass i

def budget (i : Row) : ℝ :=
  min 1 (min (gamma i) (min (stripMass i)
    (min (residualMass i) (min (roomMass i) (cutoff i/2)))))

def epsilon (i : Row) : ℝ := budget i/100

def normalizeCount (g : GuardData) : GuardData :=
  {g with countMargin := 2*g.margin*g.population}

theorem residual_pos (i : Row) : 0< residualMass i := by
  rw [residualMass,← residual_density i]
  exact mul_pos (cutoff_pos i) (EntryEarlySourceLimits.requiredDemand_bounds i).1

theorem room_pos (i : Row) : 0< roomMass i := by
  unfold roomMass residualMass
  rw [← residual_density i]
  have h := EntryEarlySourceLimits.requiredDemand_bounds i
  have ht := cutoff_pos i
  nlinarith only [mul_pos ht (sub_pos.mpr (h.2.trans (by norm_num : (1/2:ℝ)<1)))]

theorem gamma_pos (i : Row) : 0< gamma i := by
  have ht := cutoff_pos i
  exact demandSlack_pos i (by unfold radius; positivity) (ReceiptGap.cap_bounds i).1

theorem epsilon_bounds (i : Row) :
    0< epsilon i ∧ epsilon i≤1 ∧ 100*epsilon i≤ gamma i ∧
    100*epsilon i≤ stripMass i ∧ 100*epsilon i≤ residualMass i ∧
    100*epsilon i≤ roomMass i ∧ 100*epsilon i≤ cutoff i/2 := by
  have ht := cutoff_pos i
  have hB : 0< budget i := by
    unfold budget
    exact lt_min (by norm_num) (lt_min (gamma_pos i) (lt_min (stripMass_pos i)
      (lt_min (residual_pos i) (lt_min (room_pos i) (by positivity)))))
  have h1 : budget i≤1 := min_le_left _ _
  have hγ : budget i≤ gamma i := (min_le_right _ _).trans (min_le_left _ _)
  have hq : budget i≤ stripMass i :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hr : budget i≤ residualMass i :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hroom : budget i≤ roomMass i :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hs : budget i≤ cutoff i/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  unfold epsilon
  exact ⟨by positivity,by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith⟩

@[simp] theorem tests_normalize (ξ A U : ℝ) (g : GuardData) :
    tests ξ (normalizeCount g) A U=tests ξ g A U := rfl

@[simp] theorem canonical_normalize {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ξ : ℝ) (g : GuardData) (T : PureTemplate ι) (B : ι→ℝ) :
    canonicalLaw ξ (normalizeCount g) T B=canonicalLaw ξ g T B := rfl

@[simp] theorem canonicalGoodMarginal_normalize (i : Row) (G : Measure (ℝ×ℝ))
    (C N : ℕ) (g : GuardData) (b A U ε : ℝ) :
    canonicalGoodMarginal i G C N (normalizeCount g) b A U ε=
      canonicalGoodMarginal i G C N g b A U ε := rfl

@[simp] theorem canonicalGoodDuplicate_normalize (i : Row) (G : Measure (ℝ×ℝ))
    (C N : ℕ) (g : GuardData) (b A U ε : ℝ) :
    canonicalGoodDuplicate i G C N (normalizeCount g) b A U ε=
      canonicalGoodDuplicate i G C N g b A U ε := rfl

theorem scalar_geometry (i : Row) (g : GuardData) (hf : LiteralFields i g)
    (hL : |g.multiplier-entry i|< cutoff i/40000)
    (hz : entry i+cutoff i/100< g.rejectionRoot) :
    PrefixConditions (xi i) g (g.multiplier+g.radius) ∧
    0< lowerPrice i ∧ lowerPrice i< entry i ∧
    lowerPrice i≤ g.multiplier-g.radius ∧
    (1-xi i)*ReceiptGap.cap i≤ g.multiplier-g.radius ∧
    2*g.radius≤ xi i*g.requiredDemand*g.multiplier/4 := by
  have hp := (prefix_of_scalar_roots i g hf hL hz).1
  have ht := cutoff_pos i
  have he := abs_lt.mp hL
  have ha : g.radius=cutoff i/10000 := hf.radius_eq
  have hx : (7/10:ℝ)≤ x i := by cases i <;> norm_num [x,xQ]
  have hξ : (2/5:ℝ)≤ xi i := by cases i <;> norm_num [xi,xiQ,etaQ]
  have hr : (1/60:ℝ)≤ g.requiredDemand := by rw [hf.demand_eq]; exact requiredDemand_lower i
  have hLL : (2/3:ℝ)*cutoff i≤ g.multiplier := by
    have hh := mul_le_mul_of_nonneg_right hx ht.le
    unfold entry at he
    linarith
  have hprod : cutoff i/225≤ xi i*g.requiredDemand*g.multiplier := by
    calc
      cutoff i/225=(2/5:ℝ)*(1/60)*((2/3)*cutoff i) := by ring
      _ ≤ xi i*g.requiredDemand*g.multiplier :=
        mul_le_mul (mul_le_mul hξ hr (by norm_num) (xi_pos i).le) hLL
          (by positivity) (mul_nonneg (xi_pos i).le hp.requiredDemand_pos.le)
  have hre : g.multiplier+g.radius≤ g.rejectionRoot := by rw [ha]; linarith
  have hrec := ReceiptGap.lower_guard_above_threshold i g
    (show entry i-cutoff i/200≤ g.multiplier by linarith)
    (show g.radius≤ cutoff i/100 by rw [ha]; linarith)
  have hκ : (1-xi i)*ReceiptGap.cap i≤ ReceiptGap.threshold i := by
    unfold ReceiptGap.threshold
    nlinarith [mul_pos (xi_pos i) (ReceiptGap.cap_bounds i).1]
  refine ⟨{hp with upper := le_rfl,rejection := hre},?_,?_,?_,?_,?_⟩
  · unfold lowerPrice entry
    have hh := mul_le_mul_of_nonneg_right hx ht.le
    nlinarith
  · unfold lowerPrice
    linarith
  · unfold lowerPrice
    rw [ha]
    linarith
  · linarith
  · rw [ha]
    linarith

theorem floor_error {n : ℕ} (hn : 2≤ n) :
    |(capacity n:ℝ)-((n-1:ℕ):ℝ)*rho|≤1 := by
  have hf := PhysicalRates.capacity_floor_bounds n
  have he : ((n-1:ℕ):ℝ)=(n:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤ n),Nat.cast_one]
  rw [he]
  apply abs_le.mpr
  norm_num only [rho] at hf ⊢
  constructor <;> nlinarith

theorem finite_inputs (i : Row) (G : Measure (ℝ×ℝ)) [IsProbabilityMeasure G]
    (g : GuardData) (hf : LiteralFields i g) {n : ℕ} (hn : 4≤ n)
    (hpopulation : g.population=(n:ℝ))
    (hmargin : g.margin≤ epsilon i)
    (hlarge : 100≤ epsilon i*((n-1:ℕ):ℝ))
    (hL : |g.multiplier-entry i|< cutoff i/40000)
    (hz : entry i+cutoff i/100< g.rejectionRoot)
    (hcap : ∀ᵐ p ∂G,p.2≤ ReceiptGap.cap i)
    (hvalue : G.map Prod.fst=LowChernoff.conditionalValueLaw i)
    (hbid : ∀ᵐ p ∂G,p.2≤ p.1)
    (hroot : (∫ p,exposure (xi i) g.multiplier p.2 ∂G)=PrefixRoot.requiredDemand i)
    (hpsi : (∫ p,PrefixRoot.sourcePsi i g.rejectionRoot p.2 ∂G)=3*PrefixRoot.requiredDemand i)
    {b c : ℝ} (hb : b∈Icc (g.multiplier-g.radius) (g.multiplier+g.radius))
    (hbcap : b≤ ReceiptGap.cap i) (hhalf : ReceiptGap.threshold i≤ b)
    (hweight : c+epsilon i≤ weightMean i G g.multiplier) :
    Inputs (RawMixedSource.source i G) i (normalizeCount g) (n-1) (capacity n)
      b (g.multiplier+2*g.radius) (ReceiptGap.cap i) (epsilon i) c (stripMass i)
      (lowerPrice i) (gamma i) (weightMean i G g.multiplier) (cutoff i/2) := by
  have ht := cutoff_pos i
  have hgeom := scalar_geometry i g hf hL hz
  have hε := epsilon_bounds i
  have hN : (0:ℝ)<((n-1:ℕ):ℝ) := by exact_mod_cast (show 0< n-1 by omega)
  have hpop : g.population=((n-1:ℕ):ℝ)+1 := by
    rw [hpopulation,Nat.cast_sub (by omega : 1≤ n),Nat.cast_one]
    ring
  have ha : 0< g.radius := by rw [hf.radius_eq]; unfold radius; positivity
  have hL0 : 0< g.multiplier := by linarith [hgeom.1.lower_pos]
  have hmeans := original_meanMargins i G g hf (ReceiptGap.cap_bounds i).1
    hgeom.1.lower_pos hgeom.2.2.2.2.1 hgeom.2.2.2.2.2 hcap hvalue hbid hroot hpsi
  have hw := original_weight_lower i G hL0 hroot
  have hcontrol : 2*g.margin*g.population≤2*epsilon i*(((n-1:ℕ):ℝ)+1) := by
    rw [hpop]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmargin (by norm_num)) (by positivity)
  have hgN := mul_le_mul_of_nonneg_right hε.2.2.1 hN.le
  have hwN := mul_le_mul_of_nonneg_right (hε.2.2.2.1.trans hw) hN.le
  have hrN := mul_le_mul_of_nonneg_right hε.2.2.2.2.1 hN.le
  have hroomN := mul_le_mul_of_nonneg_right hε.2.2.2.2.2.1 hN.le
  have hqN := mul_le_mul_of_nonneg_right hε.2.2.2.1 hN.le
  have hsN := mul_le_mul_of_nonneg_right hε.2.2.2.2.2.2 hN.le
  refine {
    rivals_pos := by omega
    epsilon_nonneg := hε.1.le
    lo_pos := hgeom.2.1
    cap_pos := (ReceiptGap.cap_bounds i).1
    strip_pos := stripMass_pos i
    radius_pos := ha
    «prefix» := hgeom.1.update_countMargin _
    requiredDemand_eq := hf.demand_eq
    lower_price := hgeom.2.2.2.1
    cap_receipt := hgeom.2.2.2.2.1
    half_receipt := hhalf
    bid_window := hb
    bid_cap := hbcap
    strip_above := by change g.multiplier+g.radius< g.multiplier+2*g.radius; linarith
    means := ?_
    floor_error := floor_error (by omega)
    residual_positive := ?_
    residual_room := ?_
    demand_margin := ?_
    weight_margin := ?_
    rejection_margin := ?_
    seed_margin := ?_
    strip_margin := ?_
    count_margin := le_rfl
    sample_weight_margin := ?_ }
  · constructor
    · simpa only [normalizeCount,tests,hf.radius_eq,gamma] using hmeans.lower
    · simpa only [normalizeCount,tests,hf.radius_eq,gamma] using hmeans.upper0
    · simpa only [normalizeCount,tests,hf.radius_eq,gamma] using hmeans.upper1
    · simpa only [normalizeCount,tests,hf.radius_eq,gamma] using hmeans.lowerDemand
    · simpa only [normalizeCount,tests,hf.radius_eq,gamma] using hmeans.upperDemand
    · simpa only [normalizeCount,tests,hf.radius_eq,gamma] using hmeans.weight
    · simpa only [normalizeCount,tests,hf.radius_eq,gamma] using hmeans.rejection
    · simpa only [normalizeCount,tests,hf.radius_eq,gamma] using hmeans.seed
    · simpa only [normalizeCount,tests,hf.radius_eq,gamma] using hmeans.strip
  · change epsilon i*((n-1:ℕ):ℝ)+2<((n-1:ℕ):ℝ)*residualMass i
    nlinarith only [hrN,hlarge]
  · change 2*epsilon i*((n-1:ℕ):ℝ)+3≤((n-1:ℕ):ℝ)*roomMass i
    nlinarith only [hroomN,hlarge]
  · change 2*g.margin*g.population≤ gamma i*((n-1:ℕ):ℝ)-2*error (n-1) (epsilon i)-1
    unfold error
    nlinarith only [hcontrol,hgN,hlarge,hε.2.1]
  · change 2*g.margin*g.population≤ weightMean i G g.multiplier*((n-1:ℕ):ℝ)-3*error (n-1) (epsilon i)
    unfold error
    nlinarith only [hcontrol,hwN,hlarge,hε.2.1]
  · change 2*g.margin*g.population≤ residualMass i*((n-1:ℕ):ℝ)-3*error (n-1) (epsilon i)
    unfold error
    nlinarith only [hcontrol,hrN,hlarge,hε.2.1]
  · nlinarith only [hsN,hlarge]
  · unfold error
    nlinarith only [hqN,hlarge]
  · have hh := mul_le_mul_of_nonneg_right hweight hN.le
    nlinarith only [hh]

end FCAppendix.Affine.Uniform06.EntryFiniteConstructor
