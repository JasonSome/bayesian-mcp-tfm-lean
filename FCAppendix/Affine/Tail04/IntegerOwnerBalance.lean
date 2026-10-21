import FCAppendix.Affine.Tail04.IntegerOwners
import FCAppendix.Affine.Tail04.UnusedBidPriceTest
import Mathlib.MeasureTheory.Function.Floor

noncomputable section
namespace FCAppendix.Affine.Tail04
open MeasureTheory Set

def nearestQuota (x : ℝ) : ℕ := ⌊x+1/2⌋₊

theorem nearestQuota_error {x : ℝ} (hx : 0 ≤ x) :
    |(nearestQuota x : ℝ)-x| ≤ 1/2 := by
  have hlo : (nearestQuota x : ℝ) ≤ x+1/2 := Nat.floor_le (by linarith)
  have hhi : x+1/2 < (nearestQuota x : ℝ)+1 := Nat.lt_floor_add_one _
  apply abs_le.mpr
  constructor <;> linarith

theorem nearestQuota_le {x : ℝ} {E : ℕ} (hx0 : 0 ≤ x) (hxE : x ≤ E) :
    nearestQuota x ≤ E := by
  have hlo : (nearestQuota x : ℝ) ≤ x+1/2 := Nat.floor_le (by linarith)
  have hlt : (nearestQuota x : ℝ) < (E:ℝ)+1 := by linarith
  have hnat : nearestQuota x < E+1 := by exact_mod_cast hlt
  omega

def balancedOwnerQuota (E : ℕ) (mean1 mean2 : ℝ) : ℕ :=
  nearestQuota (((E:ℝ)+mean2-mean1)/2)

def ownerBalanceError (E : ℕ) (mean1 mean2 : ℝ) : ℝ :=
  (balancedOwnerQuota E mean1 mean2 : ℝ)-((E:ℝ)+mean2-mean1)/2

theorem balancedOwnerQuota_guards (E : ℕ) (mean1 mean2 : ℝ)
    (hmean : |mean2-mean1| ≤ E) :
    balancedOwnerQuota E mean1 mean2 ≤ E ∧
      |ownerBalanceError E mean1 mean2| ≤ 1/2 := by
  have hm := abs_le.mp hmean
  have hx0 : 0 ≤ ((E:ℝ)+mean2-mean1)/2 := by linarith [hm.1]
  have hxE : ((E:ℝ)+mean2-mean1)/2 ≤ E := by linarith [hm.2]
  exact ⟨nearestQuota_le hx0 hxE, nearestQuota_error hx0⟩

theorem balancedOwnerQuota_complement_error (E : ℕ) (mean1 mean2 : ℝ)
    (hmean : |mean2-mean1| ≤ E) :
    ((E-balancedOwnerQuota E mean1 mean2 : ℕ) : ℝ) -
        ((E:ℝ)+mean1-mean2)/2 = -ownerBalanceError E mean1 mean2 := by
  have hK := (balancedOwnerQuota_guards E mean1 mean2 hmean).1
  rw [Nat.cast_sub hK]
  unfold ownerBalanceError
  ring

theorem balancedOwnerQuota_price_errors (E : ℕ) (mean1 mean2 : ℝ)
    (hmean : |mean2-mean1| ≤ E) :
    ∃ e1 e2 : ℝ,
      (balancedOwnerQuota E mean1 mean2 : ℝ) = ((E:ℝ)+mean2-mean1)/2+e1 ∧
      ((E-balancedOwnerQuota E mean1 mean2 : ℕ) : ℝ) = ((E:ℝ)+mean1-mean2)/2+e2 ∧
      |e1| ≤ 1/2 ∧ |e2| ≤ 1/2 ∧ e1+e2=0 := by
  refine ⟨ownerBalanceError E mean1 mean2,-ownerBalanceError E mean1 mean2,?_,?_,?_,?_,?_⟩
  · unfold ownerBalanceError
    ring
  · have hh := balancedOwnerQuota_complement_error E mean1 mean2 hmean
    linarith
  · exact (balancedOwnerQuota_guards E mean1 mean2 hmean).2
  · simpa only [abs_neg] using (balancedOwnerQuota_guards E mean1 mean2 hmean).2
  · ring

theorem measurable_balancedOwnerQuota {X : Type*} [MeasurableSpace X]
    (E : ℕ) (mean1 mean2 : X → ℝ) (h1 : Measurable mean1) (h2 : Measurable mean2) :
    Measurable (fun x => balancedOwnerQuota E (mean1 x) (mean2 x)) := by
  unfold balancedOwnerQuota nearestQuota
  have h : Measurable (fun x => (((E:ℝ)+mean2 x-mean1 x)/2)+1/2) :=
    (((measurable_const.add h2).sub h1).div_const 2).add_const (1/2)
  exact h.nat_floor

end FCAppendix.Affine.Tail04
