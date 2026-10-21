import FCAppendix.Affine.UniformFinite.RawCounts
import FCAppendix.Affine.UniformFinite.RestrictedICAdapters
import FCAppendix.Affine.UniformFinite.ProductPayoff
import FCAppendix.Affine.UniformFinite.CapLocalization

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Late
open Set MeasureTheory ProbabilityTheory Filter Topology
open Uniform05

def floorTop (i : Row) : ℝ := chi*(t i-v0 i)
def floorGap (i : Row) : ℝ := (s i-lambda i)^2/s i

lemma floorTop_nonneg (i : Row) : 0≤ floorTop i := by
  have ht:=t_pos i
  unfold floorTop chi v0
  linarith

lemma floor_le_floorTop (i : Row) {v : ℝ} (hv : v≤ t i) : floorBid i v≤ floorTop i := by
  have ht:=t_pos i
  have h : max 0 (v-v0 i)≤ t i-v0 i := by
    apply max_le
    · dsimp [v0]; linarith
    · linarith
  exact (floor_le_chi_positivePart i v).trans
    (mul_le_mul_of_nonneg_left h (by norm_num [chi]))

lemma floorTop_lt_entry (i : Row) : floorTop i< lambda i := full_floor_max_below_lambda i

lemma floorTop_lt_cap (i : Row) : floorTop i< cap i := by
  have h:=source_activeBid_feasible i (v:=t i) (by
    have hx:=x_range i
    have ht:=t_pos i
    unfold lambda
    nlinarith) le_rfl
  have hb:=activeBidAt_bounds (xi_range i).1 (xi_range i).2 (lambda_pos i)
    (show lambda i< t i from by have hx:=x_range i; have ht:=t_pos i; unfold lambda; nlinarith)
  have hBc:=h.2.trans (min_le_right _ _)
  change lambda i< activeBid i (t i) ∧ _ at hb
  exact (floorTop_lt_entry i).trans (hb.1.trans_le hBc)

lemma floorGap_pos (i : Row) : 0< floorGap i := by
  have ht:=t_pos i
  have hL:=lambda_pos i
  have hs : lambda i< s i := by unfold s; linarith
  exact div_pos (sq_pos_of_pos (sub_pos.mpr hs)) (hL.trans hs)

def SourceRawApprox (i : Row) (N : ℕ) (pi : Joint i) (err : ℝ) : Prop :=
  ∀v∈Icc (0:ℝ) (t i),∀b : Bid i,
    |rawUtility i N (restrictedLaw i (0,pi)) v b-
      productPayoff (xi i) v (lambda i) b|< err

theorem no_below_floor_of_source_menu (i : Row) (N : ℕ) (pi : Joint i)
    (hIC : RestrictedIC i N pi)
    (hmenu : SourceRawApprox i N pi (floorGap i/4)) :
    ∀ᵐp ∂(pi.1 : Measure (Value i×unitInterval)),∀b : ℝ,0≤ b→ b< floorBid i p.1→
      rawUtility i N (restrictedLaw i (0,pi)) p.1 b<
        rawUtility i N (restrictedLaw i (0,pi)) p.1 (baseBid i p) ∧
      (∀j : Fin 2,rawRouteUtility i N (restrictedLaw i (0,pi)) j p.1 b<
        rawUtility i N (restrictedLaw i (0,pi)) p.1 (baseBid i p)) ∧
      oneRouteRawUtility i N (restrictedLaw i (0,pi)) p.1 b<
        rawUtility i N (restrictedLaw i (0,pi)) p.1 (baseBid i p) := by
  let G:=restrictedLaw i (0,pi)
  have hg:=floorGap_pos i
  filter_upwards [hIC] with p hp
  intro b hb0 hbf
  have hf : 0< floorBid i p.1 := hb0.trans_lt hbf
  obtain ⟨_,a,ha,hag⟩:=floored_type_product_gap i p.1.property.1 p.1.property.2 hf
  let a' : Bid i:=⟨a,(floor_nonneg i p.1).trans ha.1,ha.2.trans (min_le_right _ _)⟩
  have hma:=hmenu p.1 p.1.property a'
  have hchosen:=hp a ha
  have hinc : floorGap i-floorGap i/4≤ rawUtility i N G p.1 (baseBid i p) := by
    have hbound:=(abs_lt.mp hma).1
    change floorGap i≤ productPayoff (xi i) p.1 (lambda i) a at hag
    change rawUtility i N G p.1 a≤ rawUtility i N G p.1 (baseBid i p) at hchosen
    change -(floorGap i/4)< rawUtility i N G p.1 a-productPayoff (xi i) p.1 (lambda i) a at hbound
    linarith
  have hbtop : b≤ floorTop i := hbf.le.trans (floor_le_floorTop i p.1.property.2)
  have hbU : b≤ cap i := hbtop.trans (floorTop_lt_cap i).le
  let b' : Bid i:=⟨b,hb0,hbU⟩
  have hbL : b≤ lambda i := hbtop.trans (floorTop_lt_entry i).le
  have hpzero (v : ℝ) : productPayoff (xi i) v (lambda i) b=0 := product_zero hbL
  have hraw : rawUtility i N G p.1 b< floorGap i/4 := by
    have h:=hmenu p.1 p.1.property b'
    change |rawUtility i N G p.1 b-productPayoff (xi i) p.1 (lambda i) b|< _ at h
    rw [hpzero,sub_zero] at h
    exact (le_abs_self _).trans_lt h
  have htmenu:=hmenu (t i) ⟨(t_pos i).le,le_rfl⟩ b'
  have hzmenu:=hmenu 0 ⟨le_rfl,(t_pos i).le⟩ b'
  change |rawUtility i N G (t i) b-productPayoff (xi i) (t i) (lambda i) b|< _ at htmenu
  change |rawUtility i N G 0 b-productPayoff (xi i) 0 (lambda i) b|< _ at hzmenu
  rw [hpzero,sub_zero] at htmenu hzmenu
  have hid:=raw_value_difference i N G b' (t i) 0
  simp only [sub_zero] at hid
  have hsuccess : t i*rawSuccess i N G b< floorGap i/2 := by
    have hT:=(abs_lt.mp htmenu).2
    have hZ:=(abs_lt.mp hzmenu).1
    change rawUtility i N G (t i) b-rawUtility i N G 0 b=t i*rawSuccess i N G b at hid
    linarith
  refine ⟨by linarith,?_,?_⟩
  · intro j
    have hroute:=rawRouteUtility_le_success i N G j p.1 b' p.1.property.2
    change rawRouteUtility i N G j p.1 b≤ _ at hroute
    linarith
  · have hroute:=oneRouteRawUtility_le_success i N G p.1 b' p.1.property.2
    change oneRouteRawUtility i N G p.1 b≤ _ at hroute
    linarith

theorem remove_floor (i : Row) :
    ∀ᶠ N : ℕ in atTop,∀pi : Joint i,NoisyIC i N 0 pi→
      ∀ᵐp ∂(pi.1 : Measure (Value i×unitInterval)),∀b : ℝ,0≤ b→ b< floorBid i p.1→
        rawUtility i N (restrictedLaw i (0,pi)) p.1 b<
          rawUtility i N (restrictedLaw i (0,pi)) p.1 (baseBid i p) ∧
        (∀j : Fin 2,rawRouteUtility i N (restrictedLaw i (0,pi)) j p.1 b<
          rawUtility i N (restrictedLaw i (0,pi)) p.1 (baseBid i p)) ∧
        oneRouteRawUtility i N (restrictedLaw i (0,pi)) p.1 b<
          rawUtility i N (restrictedLaw i (0,pi)) p.1 (baseBid i p) := by
  filter_upwards [uniform_source_raw_menu i (div_pos (floorGap_pos i) (by norm_num : (0:ℝ)<4))]
    with N hN
  intro pi hIC
  apply no_below_floor_of_source_menu i N pi ((noisy_zero_iff_restricted_IC i N pi).mp hIC)
  intro v hv b
  exact hN pi hIC v b hv

end FCAppendix.Affine.UniformFinite.Late
