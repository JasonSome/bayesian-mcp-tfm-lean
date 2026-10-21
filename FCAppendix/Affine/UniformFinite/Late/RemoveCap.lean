import FCAppendix.Affine.UniformFinite.Late.ExceptionalMenu
import FCAppendix.Affine.UniformFinite.RestrictedICAdapters
import FCAppendix.Affine.UniformFinite.ActualSurplus

noncomputable section
namespace FCAppendix.Affine.UniformFinite.Late
open Set MeasureTheory ProbabilityTheory Filter Topology Classical
open Uniform05 Source
open Existence.Distributional
open scoped BigOperators

namespace Exceptional

theorem source_receipt_margin (i : Row) :
    0 < lambda i-guardRadius i-kappa i*t i := by
  have ht := t_pos i
  cases i <;> norm_num [lambda,x,kappa,xi,eta,guardRadius] <;> nlinarith

theorem source_full_receipt (i : Row) : kappa i*t i < lambda i := by
  have h := source_receipt_margin i
  linarith [guardRadius_pos i]

theorem eventual_receipt (i : Row) :
    ∀ᶠ N : ℕ in atTop, ∀ pi : Joint i, NoisyIC i N 0 pi →
      kappa i*t i ≤ rootLo i (restrictedLaw i (0,pi)) := by
  let radius := (lambda i-guardRadius i-kappa i*t i)/2
  have hr : 0 < radius := half_pos (source_receipt_margin i)
  obtain ⟨N0,eps0,heps,hroot⟩ := noisy_multiplier_localization i hr
  filter_upwards [eventually_ge_atTop N0] with N hN
  intro pi hIC
  have h := hroot N hN 0 heps.le pi hIC
  have hh := (abs_lt.mp h).1
  unfold rootLo
  dsimp [radius] at hh
  linarith [source_receipt_margin i]

abbrev FullProductBox (i : Row) := Value i × (ProductRoot i × Value i)

def fullProductPayoff (i : Row) (p : FullProductBox i) : ℝ :=
  productPayoff (xi i) p.1 p.2.1 p.2.2

theorem continuous_fullProductPayoff (i : Row) : Continuous (fullProductPayoff i) := by
  have hV : Continuous (fun p : FullProductBox i => (p.1:ℝ)) := by fun_prop
  have hL : Continuous (fun p : FullProductBox i => (p.2.1:ℝ)) := by fun_prop
  have hB : Continuous (fun p : FullProductBox i => (p.2.2:ℝ)) := by fun_prop
  have hp : Continuous (fun p : FullProductBox i =>
      ClippedResidual.exposure (xi i) p.2.1 p.2.2) := by
    unfold ClippedResidual.exposure
    apply continuous_const.min
    apply (continuous_const.max (hB.sub hL)).div (continuous_const.mul (hB.max hL))
    intro p
    have hpos := (demandLo_pos i).trans_le p.2.1.property.1
    exact (mul_pos (xi_range i).1
      (hpos.trans_le (le_max_right (p.2.2:ℝ) p.2.1))).ne'
  exact (hV.mul ((continuous_const.mul hp).sub (hp.pow 2))).sub
    (((continuous_const.mul hB).mul hp).mul
      (continuous_const.sub (continuous_const.mul hp)))

theorem full_product_modulus (i : Row) {tol : ℝ} (htol : 0 < tol) :
    ∃ radius : ℝ, 0 < radius ∧ ∀v b : Value i, ∀L K : ProductRoot i,
      |(L:ℝ)-K| < radius →
        |productPayoff (xi i) v L b-productPayoff (xi i) v K b| < tol := by
  obtain ⟨radius,hr,hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous (continuous_fullProductPayoff i)) tol htol
  refine ⟨radius,hr,?_⟩
  intro v b L K hL
  have hd : dist (v,(L,b)) (v,(K,b)) < radius := by
    simp only [Prod.dist_eq,dist_self,Subtype.dist_eq,Real.dist_eq]
    exact max_lt hr (max_lt hL hr)
  simpa only [Real.dist_eq,fullProductPayoff] using hmod hd

theorem uniform_source_raw_menu (i : Row) {tol : ℝ} (htol : 0 < tol) :
    ∀ᶠ N : ℕ in atTop, ∀ pi : Joint i, NoisyIC i N 0 pi →
      ∀v own : ℝ, v ∈ Icc (0:ℝ) (t i) → own ∈ Icc (0:ℝ) (t i) →
        |rawUtility i N (restrictedLaw i (0,pi)) v own-
          productPayoff (xi i) v (lambda i) own| < tol := by
  have ht2 := half_pos htol
  obtain ⟨radius,hr,hmod⟩ := full_product_modulus i ht2
  obtain ⟨N0,eps0,he0,hroot⟩ := noisy_multiplier_localization i hr
  filter_upwards [eventually_ge_atTop N0,eventual_receipt i,uniform_product_menu i ht2]
    with N hN hreceipt hmenu
  intro pi hIC v own hv hown
  have hL := hroot N hN 0 he0.le pi hIC
  have hP := hmod (⟨v,hv⟩ : Value i) (⟨own,hown⟩ : Value i)
    (actualProductRoot i (restrictedLaw i (0,pi))) (sourceProductRoot i) hL
  have hA := hmenu (restrictedLaw i (0,pi)) (hreceipt pi hIC) v own hv hown
  calc
    _ ≤ |rawUtility i N (restrictedLaw i (0,pi)) v own-
        productPayoff (xi i) v (restrictedLaw i (0,pi)).multiplier own|+
      |productPayoff (xi i) v (restrictedLaw i (0,pi)).multiplier own-
        productPayoff (xi i) v (lambda i) own| := abs_sub_le _ _ _
    _ < tol/2+tol/2 := add_lt_add hA hP
    _ = tol := by ring

theorem source_entry_lt_cap (i : Row) : lambda i < cap i := by
  have h := source_bid_top_above_entry i
  have ht := t_pos i
  unfold cap
  linarith

def aboveCapBox (i : Row) : Set (Value i × Value i) :=
  {p | cap i ≤ (p.1:ℝ) ∧ cap i ≤ (p.2:ℝ)}

theorem isClosed_aboveCapBox (i : Row) : IsClosed (aboveCapBox i) :=
  (isClosed_le continuous_const (continuous_subtype_val.comp continuous_fst)).inter
    (isClosed_le continuous_const (continuous_subtype_val.comp continuous_snd))

theorem aboveCapBox_nonempty (i : Row) : (aboveCapBox i).Nonempty := by
  let top : Value i := ⟨t i,(t_pos i).le,le_rfl⟩
  exact ⟨(top,top),(cap_lt_t i).le,(cap_lt_t i).le⟩

theorem source_above_cap_gap_pos (i : Row) {p : Value i × Value i}
    (hp : p ∈ aboveCapBox i) :
    0 < sourceProfit i p.1-productPayoff (xi i) p.1 (lambda i) p.2 := by
  have hv := (source_entry_lt_cap i).trans_le hp.1
  have hxi := xi_range i
  have hL := lambda_pos i
  have hclip : (1-xi i)*t i ≤ lambda i := (source_full_receipt i).le
  have hsrc : sourceProfit i p.1=((p.1:ℝ)-lambda i)^2/(p.1:ℝ) :=
    activeBidAt_product hxi.1 hxi.2 hL hv
  have hup := product_upper_bound hxi.1 hxi.2 hL hclip p.2.property.2 hv
  have hstrict : productPayoff (xi i) p.1 (lambda i) p.2 <
      ((p.1:ℝ)-lambda i)^2/(p.1:ℝ) := by
    apply lt_of_le_of_ne hup
    intro he
    have heq := product_maximum_unique hxi.1 hxi.2 hL hclip p.2.property.2 hv he
    have hmono := activeBidAt_mono_value hxi.1 hxi.2 hL p.1.property.1 p.1.property.2
    simp only [source_activeBid_eq] at heq hmono
    have hbc := hp.2
    rw [heq] at hbc
    unfold cap at hbc
    linarith [t_pos i]
  rw [hsrc]
  exact sub_pos.mpr hstrict

theorem source_above_cap_gap (i : Row) :
    ∃ gap : ℝ, 0 < gap ∧ ∀v b : Value i,
      cap i ≤ (v:ℝ) → cap i ≤ (b:ℝ) →
        gap ≤ sourceProfit i v-productPayoff (xi i) v (lambda i) b := by
  let f : Value i × Value i → ℝ := fun p =>
    sourceProfit i p.1-productPayoff (xi i) p.1 (lambda i) p.2
  have harg : Continuous (fun p : Value i × Value i =>
      ((p.1:ℝ),(p.2:ℝ))) := by fun_prop
  have hf : Continuous f := ((continuous_sourceProfit i).comp continuous_fst).sub
    ((continuous_product_fixed_root (xi_range i).1 (lambda_pos i)).comp harg)
  obtain ⟨p,hp,hmin⟩ := (isClosed_aboveCapBox i).isCompact.exists_isMinOn
    (aboveCapBox_nonempty i) hf.continuousOn
  refine ⟨f p,source_above_cap_gap_pos i hp,?_⟩
  intro v b hv hb
  change f p ≤ f (v,b)
  exact hmin (show (v,b) ∈ aboveCapBox i from ⟨hv,hb⟩)

end Exceptional

theorem floor_payment_le_value (i : Row) {v : ℝ} (hv : 0 ≤ v) :
    (1+eta i)*floorBid i v ≤ v := by
  have he := (eta_range i).1
  have hf := floor_le_chi_mul i hv (t_pos i).le
  have hc : (1+eta i)*chi < 1 := by
    have h := (chi_margins i).2
    have hd : 0 < 1+eta i := by linarith
    have hh := (lt_div_iff₀ hd).mp h
    simpa only [mul_comm] using hh
  calc
    _ ≤ (1+eta i)*(chi*v) := mul_le_mul_of_nonneg_left hf (by linarith)
    _ = ((1+eta i)*chi)*v := by ring
    _ ≤ 1*v := mul_le_mul_of_nonneg_right hc.le hv
    _ = v := one_mul v

theorem raw_floor_nonnegative (i : Row) (N : ℕ) (G : RestrictedLaw i)
    {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ UniformFinite.rawUtility i N G v (floorBid i v) := by
  unfold UniformFinite.rawUtility
  apply FiniteLaw.expect_nonneg
  intro kind
  apply integral_nonneg
  intro b
  apply ActualSurplus.rowPayoff_nonneg i G (focalRow kind) v
    (focalBids i kind (floorBid i v) b) 0
  · simpa only [focalBids_zero] using floor_nonneg i v
  · simpa only [focalBids_zero] using floor_payment_le_value i hv

theorem restricted_incumbent_nonnegative (i : Row) (N : ℕ) (pi : Joint i)
    (hIC : RestrictedIC i N pi) :
    ∀ᵐp ∂(pi.1 : Measure (Value i × unitInterval)),
      0 ≤ UniformFinite.rawUtility i N (restrictedLaw i (0,pi)) p.1 (baseBid i p) := by
  filter_upwards [hIC] with p hp
  have hfloor := floor_le_min_value_cap i p.1.property.1 p.1.property.2
  exact (raw_floor_nonnegative i N (restrictedLaw i (0,pi)) p.1.property.1).trans
    (hp (floorBid i p.1) ⟨le_rfl,hfloor⟩)

theorem remove_cap_broadcast (i : Row) :
    ∀ᶠ N : ℕ in atTop, ∀ pi : Joint i, NoisyIC i N 0 pi →
      ∀ᵐp ∂(pi.1 : Measure (Value i × unitInterval)), ∀b : ℝ, cap i < b →
        Exceptional.rawUtility i N (restrictedLaw i (0,pi)) p.1 b ≤
          UniformFinite.rawUtility i N (restrictedLaw i (0,pi)) p.1 (baseBid i p) := by
  obtain ⟨gap,hgap,hgapall⟩ := Exceptional.source_above_cap_gap i
  have herr : 0 < gap/4 := by positivity
  filter_upwards [UniformFinite.uniform_source_raw_menu i herr,
    Exceptional.uniform_source_raw_menu i herr] with N hmenu hexception
  intro pi hIC
  have hraw := (noisy_zero_iff_restricted_IC i N pi).mp hIC
  filter_upwards [hraw,restricted_incumbent_nonnegative i N pi hraw] with p hp hnonneg
  intro b hb
  by_cases hbt : b ≤ t i
  · by_cases hvc : cap i ≤ (p.1:ℝ)
    · have hval := (Exceptional.source_entry_lt_cap i).trans_le hvc
      have ha := source_activeBid_feasible i hval p.1.property.2
      have hplay := hp (activeBid i p.1) ha
      have happrox := hmenu pi hIC p.1 (sourceActiveBid i p.1) p.1.property
      have hexc := hexception pi hIC p.1 b p.1.property
        ⟨(cap_pos i).le.trans hb.le,hbt⟩
      have hgap' := hgapall p.1 (⟨b,(cap_pos i).le.trans hb.le,hbt⟩ : Value i) hvc hb.le
      have hlow := (abs_lt.mp happrox).1
      have hupp := (abs_lt.mp hexc).2
      change -(gap/4) < UniformFinite.rawUtility i N (restrictedLaw i (0,pi))
        p.1 (activeBid i p.1)-sourceProfit i p.1 at hlow
      change Exceptional.rawUtility i N (restrictedLaw i (0,pi)) p.1 b-
        productPayoff (xi i) p.1 (lambda i) b < gap/4 at hupp
      change gap ≤ sourceProfit i p.1-productPayoff (xi i) p.1 (lambda i) b at hgap'
      linarith
    · exact (Exceptional.rawUtility_overbid i N (restrictedLaw i (0,pi))
        p.1.property.1 ((lt_of_not_ge hvc).trans hb)).trans hnonneg
  · exact (Exceptional.rawUtility_overbid i N (restrictedLaw i (0,pi))
      p.1.property.1 (p.1.property.2.trans_lt (lt_of_not_ge hbt))).trans hnonneg

end FCAppendix.Affine.UniformFinite.Late
