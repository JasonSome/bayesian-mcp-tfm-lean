import FCAppendix.Affine.Tail04.OrderedOriginalNoisySequence
import FCAppendix.Affine.Tail04.OrderedAtomPartialFinite

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomPartialLimit
open MeasureTheory ProbabilityTheory Set Filter Topology Classical Game Bayes Hybrid
open Existence.Distributional OriginalValues OriginalPopulation
open SourceTailNoisyFixedPoint OrderedNativeNoisySource OrderedOriginalNoisySequence
open LatentSpeciesCalculus OrderedNativeBandCarrierIC OrderedAtomPartialFinite PartialAtomCarrier
open scoped BigOperators

variable (D : FiniteTailNoisyGame.Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (upperBid : ℝ → ℝ) (hupperBid : Measurable upperBid)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (hfloor : ∀ v,t< v → H≤ upperBid v)
  (N : ℕ)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+1:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
  (S : Sequence D P t ht N)

def gameAt (j : ℕ) : FiniteGame (N+1) 2 D.c NativeLocalPolicy.Seed :=
  OrderedNativeNoisySource.game (S.data j) P t ht hdR H ((S.physical_cap_le j).trans_lt hBH)
    πL (S.law j) upperBid hupperBid hfloor (N+1) (S.rare_guard hrare j)

lemma realBaseLaw_cluster (π : JointProfile D P t ht) (k : Fin 3)
    (J : Set ℝ) (hJ : MeasurableSet J) :
    (Sequence.realBaseLaw k π : Measure ℝ).real J=
      ((π k).1 : Measure _).real (typedCluster D P t k J) := by
  change (((ProbabilityMeasure.toMeasure (π k).1).map (fun x => (x.2:ℝ))) J).toReal=_
  rw [Measure.map_apply measurable_snd.subtype_val hJ]
  rfl

def radii (β : ℝ) (n : ℕ) : ℝ := min ((D.Up-β)/4) (1/(n+1:ℝ))

lemma radii_pos (β : ℝ) (hβ : β< D.Up) (n : ℕ) : 0< radii D β n :=
  lt_min (by linarith) (by positivity)

lemma radii_tendsto (β : ℝ) (hβ : β< D.Up) : Tendsto (radii D β) atTop (𝓝 0) := by
  have hconst : Tendsto (fun _ : ℕ => (D.Up-β)/4) atTop (𝓝 ((D.Up-β)/4)) :=
    tendsto_const_nhds
  have h := hconst.min (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  change Tendsto (fun n : ℕ => min ((D.Up-β)/4) (1/(n+1:ℝ))) atTop (𝓝 0)
  simpa only [radii,Nat.cast_add,Nat.cast_one,
    min_eq_right (show 0≤(D.Up-β)/4 by linarith)] using h

def comparison (β : ℝ) (hRβ : D.R≤ β) (hβ : β< D.Up) (n : ℕ) : Icc D.R D.Up :=
  ⟨β+2*radii D β n,by
    have hr := radii_pos D β hβ n
    have hh : radii D β n≤(D.Up-β)/4 := min_le_left _ _
    constructor <;> linarith⟩

theorem partial_interior_atom_zero (hbudget : D.eps≤1) (hlow : P.d0<1-D.ξ)
    (hc : 0< D.c) (hcm : D.c< N+1) (hvalue : D.V<2-P.w)
    (hidentity : ∀ (j : ℕ) (i : Fin (N+1)) x,
      (∫ u,(problem (gameAt D P t ht πL upperBid hupperBid hdR H hBH hfloor N hrare S j) i).payoff
        (x.1:ℝ) (physicalBandAction (S.data j) P t 2 x u)
          ∂(volume : Measure unitInterval))=
        SourceOrderedNoisyFixedPoint.payoff (S.data j) P t ht N 2 (S.law j,x))
    (β : ℝ) (hRβ : D.R≤ β) (hβ : β< D.Up) :
    (Sequence.realBaseLaw 2 S.limit : Measure ℝ) {β}=0 := by
  let m := N+1
  let K := (2-P.w-D.V)*((m:ℝ)-D.c)*(partialMass/2)^m
  let err : ℕ → ℝ := fun n => 6*radii D β n*(m:ℝ)*partialMass
  have hm : 0< m := by omega
  have hmc : 0<(m:ℝ)-D.c := by
    have hc' : (D.c:ℝ)<(m:ℝ) := by exact_mod_cast hcm
    linarith
  have hK : 0< K := mul_pos (mul_pos (by linarith) hmc)
    (pow_pos (by norm_num [partialMass]) _)
  have herr : Tendsto err atTop (𝓝 0) := by
    simpa only [err,mul_zero,zero_mul] using
      (((radii_tendsto D β hβ).const_mul 6).mul_const (m:ℝ)).mul_const partialMass
  apply partial_atom_zero_of_cluster_bounds m hm
    (fun j => Sequence.realBaseLaw 2 (S.law j)) (Sequence.realBaseLaw 2 S.limit)
    (S.realBaseLaw_tendsto 2) β K hK (radii D β) err (radii_pos D β hβ) herr
  intro n
  have hnoise : ∀ᶠ j in atTop,(S.eps j:ℝ)*D.Up≤ radii D β n :=
    ((S.noise_real_tendsto.mul_const D.Up).eventually_lt_const
      (by simpa only [zero_mul] using radii_pos D β hβ n)).mono fun _ h => h.le
  filter_upwards [hnoise] with j hj
  let Dj := S.data j
  let y := comparison D β hRβ hβ n
  let p := ((S.law j 2).1 : Measure _).real (typedCluster D P t 2
    (Ioo (β-radii D β n) (β+radii D β n)))
  have hp0 : 0≤ p := measureReal_nonneg
  have hp1 : p≤1 := measureReal_le_one
  have hvj : Dj.V≤2-P.w := (S.partial_cap_le j).trans hvalue.le
  have hf := original_partial_cluster_bound Dj P t ht πL (S.law j) upperBid hupperBid
    hdR H ((S.physical_cap_le j).trans_lt hBH) hfloor N (S.rare_guard hrare j)
    hlow hc ((S.noise_small j).le.trans hbudget) hvj β (radii D β n) (radii_pos D β hβ n)
    hj y rfl (hidentity j) (S.optimal j 2)
  have hpow : (partialMass*p/2)^m=(partialMass/2)^m*p^m := by
    rw [←mul_pow]
    congr 1
    ring
  have hcoef : (2-P.w-D.V)*((m:ℝ)-D.c)*(partialMass*p/2)^m≤
      (2-P.w-Dj.V)*((m:ℝ)-D.c)*(partialMass*p/2)^m := by
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg
      (div_nonneg (mul_nonneg (by norm_num [partialMass]) hp0) (by norm_num)) _)
    exact mul_le_mul_of_nonneg_right (by linarith [S.partial_cap_le j]) hmc.le
  rw [realBaseLaw_cluster D P t ht (S.law j) 2 _ isOpen_Ioo.measurableSet]
  change K*p^m≤ err n
  calc
    _ = (2-P.w-D.V)*((m:ℝ)-D.c)*(partialMass*p/2)^m := by
      rw [hpow]
      dsimp [K]
      ring
    _ ≤ (2-P.w-Dj.V)*((m:ℝ)-D.c)*(partialMass*p/2)^m := hcoef
    _ ≤ 6*radii D β n*(m:ℝ)*partialMass*p := hf
    _ ≤ err n := by
      have hh := mul_le_mul_of_nonneg_left hp1
        (show 0≤6*radii D β n*(m:ℝ)*partialMass by
          have hr := (radii_pos D β hβ n).le
          norm_num [partialMass] at *
          positivity)
      simpa only [mul_one,err] using hh

end FCAppendix.Affine.Tail04.OrderedAtomPartialLimit
