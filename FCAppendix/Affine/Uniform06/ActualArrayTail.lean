import FCAppendix.Affine.Uniform06.ArrayRecount
import FCAppendix.Affine.Uniform06.CapacityFloor

set_option autoImplicit false
noncomputable section
namespace FCAppendix.Affine.Uniform06.ActualArrayTail

open MeasureTheory Set Filter Topology MixedIntervalLLT
variable {Ω : Type*} [MeasurableSpace Ω]

def along (A : CenteredArray Ω) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    CenteredArray Ω where
  law := fun n => A.law (φ n)
  probability := fun n => A.probability (φ n)
  X := fun n => A.X (φ n)
  Y := fun n => A.Y (φ n)
  N := fun n => A.N (φ n)
  d := fun n => A.d (φ n)
  measurable_X := fun n => A.measurable_X (φ n)
  measurable_Y := fun n => A.measurable_Y (φ n)
  bounded := fun n => A.bounded (φ n)
  mean_X := fun n => A.mean_X (φ n)
  mean_Y := fun n => A.mean_Y (φ n)
  covariance := fun n => A.covariance (φ n)
  d_nonneg := fun n => A.d_nonneg (φ n)
  d_zero := A.d_zero.comp hφ
  scale := fun n => A.scale (φ n)
  market := A.market.comp hφ
  vX := A.vX
  vY := A.vY
  lowerVariance := A.lowerVariance
  lowerVariance_pos := A.lowerVariance_pos
  variance_X_lower := fun n => A.variance_X_lower (φ n)
  variance_Y_lower := fun n => A.variance_Y_lower (φ n)
  variance_X_limit := A.variance_X_limit.comp hφ
  variance_Y_limit := A.variance_Y_limit.comp hφ

theorem along_gap (A : CenteredArray Ω) (hgap : A.CompactGap)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    (along A φ hφ).CompactGap := by
  intro T hT
  obtain ⟨r,hr0,hr1,he⟩ := hgap T hT
  exact ⟨r,hr0,hr1,hφ.eventually he⟩

def tail (A : CenteredArray Ω) (k : ℕ) : CenteredArray Ω :=
  along A (fun n => n+k) (tendsto_add_atTop_nat k)

theorem tail_gap (A : CenteredArray Ω) (hgap : A.CompactGap) (k : ℕ) :
    (tail A k).CompactGap := along_gap A hgap _ _

def physicalTail (A : CenteredArray Ω) (m : ℕ → ℕ) (hN : ∀ n,A.N n=m n-1)
    (hm : Tendsto m atTop atTop) (k : ℕ) : CenteredArray Ω :=
  ArrayRecount.recount (tail A k) (fun n => m (n+k)-1)
    (fun n => by rw [← hN]; exact Nat.cast_pos.mp (A.N_pos (n+k)))
    (PhysicalRates.rivals_tendsto.comp (hm.comp (tendsto_add_atTop_nat k)))

theorem physicalTail_gap (A : CenteredArray Ω) (hgap : A.CompactGap)
    (m : ℕ → ℕ) (hN : ∀ n,A.N n=m n-1) (hm : Tendsto m atTop atTop) (k : ℕ) :
    (physicalTail A m hN hm k).CompactGap := tail_gap A hgap k

end FCAppendix.Affine.Uniform06.ActualArrayTail
