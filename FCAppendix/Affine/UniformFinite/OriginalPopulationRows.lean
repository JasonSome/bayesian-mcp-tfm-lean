import FCAppendix.Affine.UniformFinite.OriginalPopulation

noncomputable section
namespace FCAppendix.Affine.UniformFinite.OriginalPopulation
open Set MeasureTheory ProbabilityTheory Filter Topology Classical Game Bayes
open Existence.Distributional
open scoped BigOperators

def clipBid (i : Row) (b : ℝ) : Bid i :=
  ⟨min (Uniform05.cap i) (max 0 b),
    le_min (Uniform05.cap_pos i).le (le_max_left _ _),min_le_left _ _⟩

theorem continuous_clipBid (i : Row) : Continuous (clipBid i) :=
  (continuous_const.min (continuous_const.max continuous_id)).subtype_mk _

@[simp] theorem clipBid_coe (i : Row) (b : Bid i) : clipBid i b=b := by
  apply Subtype.ext
  simp [clipBid,max_eq_right b.property.1,min_eq_right b.property.2]

def numericalOfFour (i : Row) (x : LowBody.RowRival) : NumericObservation i :=
  if x.1=0 then Sum.inl (clipBid i x.2) else if x.1=2 then Sum.inr 0 else Sum.inr 1

theorem measurable_numericalOfFour (i : Row) : Measurable (numericalOfFour i) :=
  Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const)
    (measurable_inl.comp ((continuous_clipBid i).measurable.comp measurable_snd))
    (Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const measurable_const)

def numericalDraw (i : Row) (u : UserDraw 2) : NumericObservation i :=
  numericalOfFour i (Hybrid.collapseAction (Uniform05.cap i) (Uniform05.cap i) (u.1.2,u.2))

theorem measurable_numericalDraw (i : Row) : Measurable (numericalDraw i) :=
  (measurable_numericalOfFour i).comp
    ((Hybrid.measurable_collapseAction (Uniform05.cap i) (Uniform05.cap i)).comp
      (measurable_fst.snd.prodMk measurable_snd))

theorem lowerJoint_bidLaw {i : Row} {M : ℕ} (E : ExactRestrictedLaw i M) :
    (lowerJoint E : Measure (ℝ×JointAction 2)).map (fun x=> x.2.bid)=
      (E.realBid : Measure ℝ) := by
  have hb : Measurable (fun x : ℝ×JointAction 2=>x.2.bid) :=
    (measurable_bid 2).comp measurable_snd
  rw [lowerJoint,ProbabilityMeasure.toMeasure_map,
    Measure.map_map hb
      ((measurable_subtype_coe.comp measurable_fst).prodMk (measurable_lowerAction i))]
  rw [ExactRestrictedLaw.realBid,← PositiveClusters.baseRealLaw_zero,PositiveClusters.baseRealLaw,
    ProbabilityMeasure.toMeasure_map]
  rfl

theorem realBid_clipLaw {i : Row} {M : ℕ} (E : ExactRestrictedLaw i M) :
    (E.realBid : Measure ℝ).map (clipBid i)=(E.law.bidLaw : Measure (Bid i)) := by
  change ((bidLaw i (0,E.pi) : Measure (Bid i)).map Subtype.val).map (clipBid i)=_
  rw [Measure.map_map (continuous_clipBid i).measurable measurable_subtype_coe]
  simp only [Function.comp_def,clipBid_coe,Measure.map_id',ExactRestrictedLaw.law,restrictedLaw_bidLaw]

theorem four_to_numeric_law {i : Row} {M : ℕ} (E : ExactRestrictedLaw i M) :
    (LowBody.rivalLaw (Uniform05.t i) 0 (1-Uniform05.t i) (E.realBid : Measure ℝ)).map
      (numericalOfFour i)=numericObservationLaw i E.law := by
  have hm:=measurable_numericalOfFour i
  rw [LowBody.rivalLaw,Measure.map_add _ _ hm,Measure.map_add _ _ hm,
    Measure.map_add _ _ hm]
  simp only [ENNReal.ofReal_zero,zero_smul,Measure.map_zero,add_zero,Measure.map_smul,
    Measure.map_dirac' hm]
  have he : ((E.realBid : Measure ℝ).map (fun b=>((0:Fin 4),b))).map (numericalOfFour i)=
      (E.law.bidLaw : Measure (Bid i)).map Sum.inl := by
    have hm0 : Measurable (fun b : ℝ=>((0:Fin 4),b)) :=
      (measurable_const (a:=(0:Fin 4))).prodMk measurable_id
    rw [Measure.map_map hm hm0]
    change (E.realBid : Measure ℝ).map (Sum.inl∘clipBid i)=_
    rw [← Measure.map_map measurable_inl (continuous_clipBid i).measurable,realBid_clipLaw]
  rw [he]
  simp [numericalOfFour,numericObservationLaw]

variable {i : Row} {M : ℕ} [NeZero M] {R : ℝ}

theorem game_four_row_law (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R)
    (hR : Uniform05.cap i< R) :
    (userLaw (game E H)).map (fun u : UserDraw 2=>
      Hybrid.collapseAction (Uniform05.cap i) (Uniform05.cap i) (u.1.2,u.2))=
      LowBody.rivalLaw (Uniform05.t i) 0 (1-Uniform05.t i) (E.realBid : Measure ℝ) := by
  have hm : Measurable (fun u : UserDraw 2=>
      Hybrid.collapseAction (Uniform05.cap i) (Uniform05.cap i) (u.1.2,u.2)) :=
    (Hybrid.measurable_collapseAction (Uniform05.cap i) (Uniform05.cap i)).comp
      (measurable_fst.snd.prodMk measurable_snd)
  rw [userLaw,game_joint,fullLaw_mixture,Measure.add_prod,
    Measure.prod_smul_left,Measure.prod_smul_left,Measure.map_add _ _ hm,Measure.map_smul,Measure.map_smul]
  rw [Hybrid.collapse_low_population (lowerJoint E) (Uniform05.cap i) (Uniform05.cap i)
    ((lowerJoint_shape E).mono (fun _ h=> h.1)),lowerJoint_bidLaw]
  rw [Hybrid.collapse_upper_population (upperJoint H) le_rfl
    ((upperJoint_shape H).mono (fun _ h=> hR.trans_le h.1)),smul_add,smul_smul,smul_smul]
  have hh : ENNReal.ofReal (1-Uniform05.t i)*ENNReal.ofReal (1/2:ℝ)=
      ENNReal.ofReal ((1-Uniform05.t i)/2) := by
    rw [← ENNReal.ofReal_mul (sub_nonneg.mpr (Uniform05.t_lt_one i).le)]
    congr 1
    ring
  simp only [hh,LowBody.rivalLaw,ENNReal.ofReal_zero,zero_smul,add_zero]
  exact (add_assoc _ _ _).symm

theorem game_numeric_row_law (E : ExactRestrictedLaw i M) (H : UpperPriorityLaw i R)
    (hR : Uniform05.cap i< R) :
    (userLaw (game E H)).map (numericalDraw i)=numericObservationLaw i E.law := by
  change (userLaw (game E H)).map ((numericalOfFour i)∘(fun u : UserDraw 2=>
      Hybrid.collapseAction (Uniform05.cap i) (Uniform05.cap i) (u.1.2,u.2)))=_
  have hm : Measurable (fun u : UserDraw 2=>
      Hybrid.collapseAction (Uniform05.cap i) (Uniform05.cap i) (u.1.2,u.2)) :=
    (Hybrid.measurable_collapseAction (Uniform05.cap i) (Uniform05.cap i)).comp
      (measurable_fst.snd.prodMk measurable_snd)
  rw [← Measure.map_map (measurable_numericalOfFour i) hm,
    game_four_row_law E H hR,four_to_numeric_law]

theorem game_deleted_numeric_rows {N : ℕ}
    (E : ExactRestrictedLaw i (N+1)) (H : UpperPriorityLaw i R)
    (hR : Uniform05.cap i< R) (a : Fin (N+1)) :
    (userProfileLaw (game E H)).map
      (fun x=> fun j : Fin N=> numericalDraw i (x (a.succAbove j)))=
        Measure.pi (fun _ : Fin N=> numericObservationLaw i E.law) := by
  let delete : UserProfile (N+1) 2→(Fin N→ UserDraw 2):=fun x j=> x (a.succAbove j)
  have hp : MeasurePreserving delete (userProfileLaw (game E H))
      (Measure.pi (fun _ : Fin N=> userLaw (game E H))) :=
    (measurePreserving_snd (μ:=userLaw (game E H))
      (ν:=Measure.pi (fun _ : Fin N=> userLaw (game E H)))).comp
        (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1)=> userLaw (game E H)) a)
  have hm : Measurable (fun x : Fin N→ UserDraw 2=> fun j=> numericalDraw i (x j)) :=
    measurable_pi_lambda _ (fun j=>(measurable_numericalDraw i).comp (measurable_pi_apply j))
  rw [show (fun x : UserProfile (N+1) 2=> fun j : Fin N=> numericalDraw i (x (a.succAbove j)))=
      (fun x : Fin N→ UserDraw 2=> fun j=> numericalDraw i (x j))∘delete from rfl,
    ← Measure.map_map hm hp.measurable,hp.map_eq,
    Measure.pi_map_pi (fun _=>(measurable_numericalDraw i).aemeasurable),game_numeric_row_law E H hR]

theorem game_two_deleted_numeric_rows {N : ℕ}
    (E : ExactRestrictedLaw i (N+2)) (H : UpperPriorityLaw i R)
    (hR : Uniform05.cap i< R) (a : Fin (N+2)) (b : Fin (N+1)) :
    (userProfileLaw (game E H)).map
      (fun x=> fun j : Fin N=> numericalDraw i (x (a.succAbove (b.succAbove j))))=
        Measure.pi (fun _ : Fin N=> numericObservationLaw i E.law) := by
  let μ:=numericObservationLaw i E.law
  have hp : MeasurePreserving (fun x : Fin (N+1)→ NumericObservation i=> fun j : Fin N=> x (b.succAbove j))
      (Measure.pi (fun _ : Fin (N+1)=>μ)) (Measure.pi (fun _ : Fin N=>μ)) :=
    (measurePreserving_snd (μ:=μ) (ν:=Measure.pi (fun _ : Fin N=>μ))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1)=>μ) b)
  have hfirst:=game_deleted_numeric_rows E H hR a
  have hm : Measurable (fun x : UserProfile (N+2) 2=> fun j : Fin (N+1)=>
      numericalDraw i (x (a.succAbove j))) :=
    measurable_pi_lambda _ (fun j=>(measurable_numericalDraw i).comp (measurable_pi_apply _))
  rw [show (fun x : UserProfile (N+2) 2=> fun j : Fin N=>
      numericalDraw i (x (a.succAbove (b.succAbove j))))=
      (fun x : Fin (N+1)→ NumericObservation i=> fun j : Fin N=> x (b.succAbove j))∘
        (fun x : UserProfile (N+2) 2=> fun j : Fin (N+1)=> numericalDraw i (x (a.succAbove j))) from rfl,
    ← Measure.map_map hp.measurable hm,hfirst,hp.map_eq]

end FCAppendix.Affine.UniformFinite.OriginalPopulation
