import FCAppendix.Affine.Tail04.OrderedAtomFlagVariation
import FCAppendix.Affine.Tail04.OrderedAtomTwoPrefix
import FCAppendix.Affine.Tail04.RealIntegralTransport

noncomputable section
namespace FCAppendix.Affine.Tail04.OrderedAtomRestoredBeta
open MeasureTheory ProbabilityTheory Set Classical Game Bayes
open Existence.Distributional OriginalValues FiniteTailNoisyGame SourceTailNoisyFixedPoint
open OrderedAtomActiveCompression OriginalActiveCrossingCarrier OrderedAtomCountExceptions
open OrderedAtomFiniteGain OrderedAtomClusterBound OrderedAtomActiveLaw
open LatentNoisyPopulation OrderedAtomActiveIC

section Generic
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {N : ℕ}

theorem restore_map (f : X→ Y) (j : Fin (N+1)) (w : X) (row : Fin N→ X) :
    f ∘ restore j w row=restore j (f w) (f ∘ row) := by
  funext i
  by_cases hi : i=j
  · subst i
    simp only [Function.comp_apply,restore_self]
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hi
    simp only [Function.comp_apply,restore_succAbove]

variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (tag : X→ Fin 4) (decode : X→ Icc (1:ℝ) D.B)
local notation "Ds" => installOriginal D P t ht

def restoredBeta (reg : Bool) (j : Fin (N+1)) (w : X)
    (b y : Icc (1:ℝ) D.B) (row : Fin N→ X) : ℝ :=
  beta D P t ht (N+1) (tags tag (restore j w row)) reg
    (focalRow Ds (tags tag (restore j w row)) decode b (restore j w row)) y

lemma measurable_restoredBeta (htag : Measurable tag) (hdecode : Measurable decode)
    (reg : Bool) (j : Fin (N+1)) (w : X) (b y : Icc (1:ℝ) D.B) :
    Measurable (restoredBeta D P t ht tag decode reg j w b y) := by
  have hr : Measurable (fun row : Fin N→ X => restore j w row) :=
    (measurable_restore j).comp (measurable_const.prodMk measurable_id)
  apply LocalCoordinates.measurable_finite_eval
    (fun row : Fin N→X => tags tag (restore j w row))
    (fun row kind => beta D P t ht (N+1) kind reg
      (focalRow Ds kind decode b (restore j w row)) y)
    ((measurable_tags tag htag).comp hr)
  intro kind
  have hb : Measurable (fun row : Fin N→ X =>
      fun k => (focalRow Ds kind decode b (restore j w row) k:ℝ)) :=
    measurable_pi_lambda _ fun k => measurable_subtype_coe.comp
      ((measurable_pi_apply k).comp ((measurable_focalRow Ds kind decode hdecode).comp
        (measurable_const.prodMk hr)))
  have hw := IntegratedActiveFiniteGain.measurable_weightFailure (A:=(Ds).count kind 1+1)
    (min ((Ds).count kind 2) ((Ds).count kind 3)) (max ((Ds).count kind 2) ((Ds).count kind 3)) D.c D.ξ D.B D.R D.V D.width
      (D.e0 reg) D.F reg (decide (0< (Ds).count kind 0)) ((Ds).marksLaw _) ((Ds).marksLaw _)
  exact (hw.comp (IntegratedActiveFiniteGain.measurable_freeze _ hb 0 _ measurable_const)).add
    (hw.comp (Resample.measurable_update_pair 0 |>.comp (measurable_const.prodMk hb)))

lemma restoredBeta_bounds (reg : Bool) (j : Fin (N+1)) (w : X)
    (b y : Icc (1:ℝ) D.B) (row : Fin N→ X) :
    restoredBeta D P t ht tag decode reg j w b y row∈Icc (0:ℝ) 2 :=
  beta_bounds D P t ht (N+1) _ reg _ _

theorem restoredBeta_map (f : Y→ X) (reg : Bool) (j : Fin (N+1)) (w : Y)
    (b y : Icc (1:ℝ) D.B) (row : Fin N→ Y) :
    restoredBeta D P t ht (tag ∘ f) (decode ∘ f) reg j w b y row=
      restoredBeta D P t ht tag decode reg j (f w) b y (f ∘ row) := by
  unfold restoredBeta
  rw [←restore_map f j w row]
  rfl

end Generic

section Source
variable (D : Data) (P : ValueParameters) (t : ℝ) (ht : P.M< t)
  (hdR : P.d0< D.R) (H : ℝ) (hBH : D.B< H) (N : ℕ)
local notation "E" => NativeNoisySource.regions D P hdR H hBH

def nativeRestoredBeta (reg : Bool) (j : Fin (N+1)) (w : UserDraw 2)
    (b y : Icc (1:ℝ) D.B) : (Fin N→ UserDraw 2)→ℝ :=
  restoredBeta D P t ht (E).coarseTag
    (NoisyNativeFiberProduct.commonProjection D P hdR H hBH) reg j w b y

lemma measurable_nativeRestoredBeta (reg : Bool) (j : Fin (N+1)) (w : UserDraw 2)
    (b y : Icc (1:ℝ) D.B) : Measurable (nativeRestoredBeta D P t ht hdR H hBH N reg j w b y) :=
  measurable_restoredBeta D P t ht (E).coarseTag
    (NoisyNativeFiberProduct.commonProjection D P hdR H hBH) (E).measurable_coarseTag
      (NoisyNativeFiberProduct.measurable_commonProjection D P hdR H hBH) reg j w b y

variable (πL : Law (A:=LowBody.LowValue P.d0) P.originalLowLaw)
  (π : JointProfile D P t ht) (upperBid : ℝ→ℝ) (hupperBid : Measurable upperBid)
  (hfloor : ∀ v,t< v→ H≤ upperBid v)
  (hrare : (1-D.ξ)*D.B+D.ξ*D.B*((N+2:ℕ)*
    (tailMass P t/(partialMass+tailMass P t)))≤ D.R)
local notation "μ" => drawLaw D P t ht πL π upperBid hupperBid
local notation "Γ" => NativeNoisySource.game D P t ht hdR H hBH
  πL π upperBid hupperBid hfloor (N+2) hrare

include πL π upperBid hupperBid hfloor hrare in
theorem original_carrierBeta_integral (reg : Bool) (j : Fin (N+1)) (x w : Draw)
    (y : Icc (1:ℝ) D.U) :
    (∫ row,carrierRegimeBeta D P t ht hdR H hBH (N+1) reg y (x,restore j w row)
      ∂Measure.pi (fun _ : Fin N => μ))=
    ∫ row,nativeRestoredBeta D P t ht hdR H hBH N reg j (realize D w)
      (latentBid D P hdR H hBH x) (raisedBid D y x) row
        ∂Measure.pi (fun _ : Fin N => userLaw Γ) := by
  have hp : MeasurePreserving (fun row : Fin N→ Draw => fun k => realize D (row k))
      (Measure.pi (fun _ : Fin N => μ)) (Measure.pi (fun _ : Fin N => userLaw Γ)) :=
    ⟨measurable_pi_lambda _ (fun k => (measurable_realize D).comp (measurable_pi_apply k)),
      original_remaining_realize D P t ht πL π upperBid hupperBid hdR H hBH hfloor N hrare⟩
  have hf := measurable_nativeRestoredBeta D P t ht hdR H hBH N reg j (realize D w)
    (latentBid D P hdR H hBH x) (raisedBid D y x)
  have he := hp.integral_comp_ae_real hf.aestronglyMeasurable
  convert! he using 1
  apply integral_congr_ae
  exact ae_of_all _ fun row => restoredBeta_map D P t ht (E).coarseTag
    (NoisyNativeFiberProduct.commonProjection D P hdR H hBH) (realize D) reg j w
      (latentBid D P hdR H hBH x) (raisedBid D y x) row

end Source
end FCAppendix.Affine.Tail04.OrderedAtomRestoredBeta
