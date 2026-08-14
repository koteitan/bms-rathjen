import Rows.G6

open TM Term BMS Trans Rows Rows.Selected

namespace Rows.Selected.G7Dict

/-- The raw Gamma ladder, with the normal-form simplifications made explicit. -/
def G : Nat → Term
  | 0 => phi (ofNat 2) zero
  | n+1 => phi (G n) zero

def Q (n : Nat) : Term := add (Z zero) (G n)
def X (n : Nat) : Term := phi zero (Q n)
def Y (n : Nat) : Term := phi zero (X n)

theorem G_ne_zero : ∀ n : Nat, G n≠zero
  | 0 => by decide
  | _+1 => by intro h; cases h

theorem G_ne_one : ∀ n : Nat, G n≠one
  | 0 => by decide
  | n+1 => by
    intro h
    injection h with h0 _
    exact G_ne_zero n h0

theorem G_isAP (n : Nat) : (G n).isAP=true := by cases n <;> rfl

theorem G_cnv : ∀ n : Nat, Evidence.WF.CNV (G n)=true
  | 0 => by decide
  | n+1 => by
    show (Evidence.WF.CNV (G n) && Evidence.WF.CNV zero)=true
    rw [G_cnv n]
    rfl

theorem G_inT (n : Nat) : inT (G n)=true :=
  Evidence.WF.inT_of_cnv _ (G_cnv n)

theorem G_lt_M (n : Nat) : lt (G n) M=true :=
  Evidence.WF.cnv_lt_M _ (G_cnv n)

theorem G_lt_Z : ∀ n : Nat, lt (G n) (Z zero)=true
  | 0 => by decide
  | n+1 => by
    rw [G]
    unfold lt
    cases h:fuelOf (phi (G n) zero) (Z zero) with
    | zero => simp [fuelOf] at h
    | succ f =>
      rw [Evidence.WF.ltF_succ_phi_Z]
      simp only [Bool.and_eq_true]
      have hg:=Evidence.WF.deg_pos (G n)
      have hz:=Evidence.WF.deg_pos (Z zero)
      have h0:=Evidence.WF.deg_pos zero
      have hf : (G n).deg+(Z zero).deg≤f := by
        unfold fuelOf at h
        simp only [Term.deg] at h ⊢
        omega
      constructor
      · rw [← Evidence.WF.lt_eq_ltF (G n) (Z zero) f hf]
        exact G_lt_Z n
      · exact Evidence.WF.ltF_left_zero (by omega) (by simp)

theorem G_lt_Z1 (n : Nat) : lt (G n) (Z one)=true := by
  exact Evidence.WF.lt_trans_inT (G_inT n) (by decide) (by decide)
    (G_lt_Z n) (by decide)

theorem G_toList (n : Nat) : (G n).toList=[G n] := by cases n <;> rfl

theorem G_beq_one (n : Nat) : ((G n)==one)=false :=
  beq_eq_false_iff_ne.mpr (G_ne_one n)

theorem plus_Z_G (n : Nat) : plus (Z zero) (G n)=Q n := by
  unfold plus Q
  rw [G_toList,show (Z zero).toList=[Z zero] from rfl]
  simp only [List.filter_cons,List.filter_nil]
  rw [show le (G n) (Z zero)=true from Evidence.WF.le_of_lt (G_lt_Z n)]
  rfl

theorem omegaNF_Q (n : Nat) : omegaNF (Q n)=X n := by
  unfold Q X omegaNF
  rw [show lt M (add (Z zero) (G n))=false from by rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show ((add (Z zero) (G n):Term)==M)=false from rfl]
  exact Evidence.StageB.phiNF_add_pair (by rfl) (G_isAP n) (G_beq_one n)

theorem collapse_one_G (n : Nat) : Trans.Dict.collapse 1 (G n)=X n := by
  have hw : Trans.Dict.wcnf (Z one) [G n]=([],G n) := by
    rw [Trans.Dict.wcnf,if_pos (G_lt_Z1 n)]
    rfl
  unfold Trans.Dict.collapse
  simp only [Trans.Dict.reg,TM.Term.ofNat]
  rw [show plus zero one=one from rfl,G_toList,hw]
  simp only [List.foldl_nil,Option.getD_none]
  rw [Rows.ProofsB.plus_zero_left (G_isAP n),plus_Z_G,omegaNF_Q]

theorem Q_lt_Z1 (n : Nat) : lt (Q n) (Z one)=true := by
  unfold Q lt
  cases h:fuelOf (add (Z zero) (G n)) (Z one) with
  | zero => simp [fuelOf] at h
  | succ f =>
    simp only [ltF]
    rw [show ((add (Z zero) (G n):Term)==Z one)=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    have hg:=Evidence.WF.deg_pos (G n)
    have hz0:=Evidence.WF.deg_pos (Z zero)
    have hz1:=Evidence.WF.deg_pos (Z one)
    have hf : (Z zero).deg+(Z one).deg≤f := by
      unfold fuelOf at h
      simp only [Term.deg] at h ⊢
      omega
    rw [← Evidence.WF.lt_eq_ltF (Z zero) (Z one) f hf]
    exact (by decide)

theorem X_lt_Z1 (n : Nat) : lt (X n) (Z one)=true := by
  unfold X lt
  cases h:fuelOf (phi zero (Q n)) (Z one) with
  | zero => simp [fuelOf] at h
  | succ f =>
    rw [Evidence.WF.ltF_succ_phi_Z]
    simp only [Bool.and_eq_true]
    have hq:=Evidence.WF.deg_pos (Q n)
    have hz1:=Evidence.WF.deg_pos (Z one)
    have h0:=Evidence.WF.deg_pos zero
    have hf : (Q n).deg+(Z one).deg≤f := by
      unfold fuelOf at h
      simp only [Term.deg] at h ⊢
      omega
    constructor
    · exact Evidence.WF.ltF_left_zero (by omega) (by simp)
    · rw [← Evidence.WF.lt_eq_ltF (Q n) (Z one) f hf]
      exact Q_lt_Z1 n

theorem Q_inT (n : Nat) : inT (Q n)=true := by
  cases n with
  | zero => decide
  | succ n =>
    unfold Q
    rw [show G (n+1)=phi (G n) zero from rfl]
    unfold inT
    rw [show inT (phi (G n) zero)=true from G_inT (n+1),
      show (phi (G n) zero).isAP=true from G_isAP (n+1),
      show le (phi (G n) zero) (Z zero)=true from
        Evidence.WF.le_of_lt (G_lt_Z (n+1))]
    rfl

theorem Q_lt_M (n : Nat) : lt (Q n) M=true := by
  unfold Q
  rw [Evidence.WF.lt_add_M]
  decide

theorem X_inT (n : Nat) : inT (X n)=true := by
  unfold X inT
  rw [Q_inT,Q_lt_M]
  rfl

theorem Z_lt_X (n : Nat) : lt (Z zero) (X n)=true := by
  have hzq : lt (Z zero) (Q n)=true := by
    unfold Q
    exact Evidence.WF.lt_head_add (by rfl) (G n)
  unfold X lt
  cases h:fuelOf (Z zero) (phi zero (Q n)) with
  | zero => simp [fuelOf] at h
  | succ f =>
    simp only [ltF]
    rw [show ((Z zero:Term)==phi zero (Q n))=false from rfl]
    simp only [Bool.false_eq_true,if_false]
    rw [show ((Z zero:Term)==zero)=false from rfl,
      show ((Z zero:Term)==Q n)=false from by unfold Q; rfl]
    simp only [Bool.false_or]
    rw [Rows.ProofsB.ltF_lt_zero]
    simp only [Bool.false_or]
    have hz:=Evidence.WF.deg_pos (Z zero)
    have hq:=Evidence.WF.deg_pos (Q n)
    have hf : (Z zero).deg+(Q n).deg≤f := by
      unfold fuelOf at h
      simp only [Term.deg] at h ⊢
      omega
    rw [← Evidence.WF.lt_eq_ltF (Z zero) (Q n) f hf]
    exact hzq

theorem plus_Z_X (n : Nat) : plus (Z zero) (X n)=X n := by
  unfold plus X
  rw [show (phi zero (Q n)).toList=[phi zero (Q n)] from rfl,
    show (Z zero).toList=[Z zero] from rfl]
  simp only [List.filter_cons,List.filter_nil]
  rw [show le (phi zero (Q n)) (Z zero)=false from by
    unfold le
    rw [show ((phi zero (Q n):Term)==Z zero)=false from rfl]
    simp only [Bool.false_or]
    exact Evidence.WF.lt_asymm_inT (by decide) (X_inT n) (Z_lt_X n)]
  rfl

theorem collapse_one_X (n : Nat) : Trans.Dict.collapse 1 (X n)=Y n := by
  have hw : Trans.Dict.wcnf (Z one) [X n]=([],X n) := by
    rw [Trans.Dict.wcnf,if_pos (X_lt_Z1 n)]
    rfl
  unfold Trans.Dict.collapse
  simp only [Trans.Dict.reg,TM.Term.ofNat]
  rw [show plus zero one=one from rfl]
  rw [show (X n).toList=[X n] from by unfold X; rfl,hw]
  simp only [List.foldl_nil,Option.getD_none]
  rw [Rows.ProofsB.plus_zero_left (by unfold X; rfl),plus_Z_X]
  unfold Y X
  exact Evidence.StageA.omegaNF_of_compPhi0
    (Evidence.StageA.compPhi0_phi0 (Q n))

theorem phiShifted_zero_phi (z : Term) (hz : z≠zero) :
    phiShifted zero (phi zero z)=false := by
  have hne : ((phi zero z:Term)==one)=false := by
    apply beq_eq_false_iff_ne.mpr
    intro h
    injection h with _ h0
    exact hz h0
  have hsplit:splitFin (phi zero z)=(phi zero z,0) := by
    simp [splitFin,TM.Term.toList,TM.Term.ofList,hne]
  unfold phiShifted
  rw [hsplit]
  simp [TM.Term.isFP,TM.Term.isSC,Rows.ProofsB.lt_irrefl]

theorem Q_ne_zero (n : Nat) : Q n≠zero := by unfold Q; intro h; cases h

theorem logOm_X (n : Nat) : Trans.Dict.logOm (X n)=Q n := by
  unfold X
  change (if phiShifted zero (Q n) then plus (Q n) one else Q n)=Q n
  rw [show phiShifted zero (Q n)=false from by
    change phiShifted zero (add (Z zero) (G n))=false
    unfold phiShifted
    rw [Evidence.StageB.splitFin_add_pair (G_isAP n) (G_beq_one n)]
    rfl]
  rfl

theorem logOm_Y (n : Nat) : Trans.Dict.logOm (Y n)=X n := by
  unfold Y
  change (if phiShifted zero (X n) then plus (X n) one else X n)=X n
  unfold X
  rw [phiShifted_zero_phi (Q n) (Q_ne_zero n)]
  rfl

theorem omegaNF_G (n : Nat) : omegaNF (G n)=G n := by
  cases n with
  | zero => exact Rows.ProofsB.omegaNF_phi_ne_zero (by decide)
  | succ n => exact Rows.ProofsB.omegaNF_phi_ne_zero (G_ne_zero n)

theorem divAP_Z_X (n : Nat) :
    Trans.Dict.divAP (Z zero) (X n)=G n := by
  unfold Trans.Dict.divAP
  rw [logOm_X]
  unfold Trans.Dict.subAP Q
  rw [show (add (Z zero) (G n)).toList=[Z zero,G n] from by
    change Z zero::(G n).toList=[Z zero,G n]
    rw [G_toList]]
  simp only [show ((Z zero:Term)==Z zero)=true from rfl,if_true]
  exact omegaNF_G n

theorem Q_not_lt_Z (n : Nat) : lt (Q n) (Z zero)=false := by
  unfold Q lt
  cases h:fuelOf (add (Z zero) (G n)) (Z zero) with
  | zero => rfl
  | succ f =>
    simp only [ltF]
    rw [show ((add (Z zero) (G n):Term)==Z zero)=false from rfl]
    simp only [Bool.false_eq_true,if_false,Evidence.WF.ltF_irrefl]

theorem X_not_lt_Z (n : Nat) : lt (X n) (Z zero)=false := by
  exact Evidence.WF.lt_asymm_inT (by decide) (X_inT n) (Z_lt_X n)

theorem Y_not_lt_Z (n : Nat) : lt (Y n) (Z zero)=false := by
  unfold Y lt
  cases h:fuelOf (phi zero (X n)) (Z zero) with
  | zero => rfl
  | succ f =>
    rw [Evidence.WF.ltF_succ_phi_Z]
    have hx:=Evidence.WF.deg_pos (X n)
    have hz:=Evidence.WF.deg_pos (Z zero)
    have h0:=Evidence.WF.deg_pos zero
    have hf : (X n).deg+(Z zero).deg≤f := by
      unfold fuelOf at h
      simp only [Term.deg] at h ⊢
      omega
    rw [show ltF f (X n) (Z zero)=false from by
      rw [← Evidence.WF.lt_eq_ltF (X n) (Z zero) f hf]
      exact X_not_lt_Z n]
    simp

theorem wcnf_Y (n : Nat) :
    Trans.Dict.wcnf (Z zero) [Y n]=([(G n,one)],zero) := by
  rw [Trans.Dict.wcnf,if_neg (by
    rw [Y_not_lt_Z n]
    exact Bool.noConfusion)]
  rw [logOm_Y]
  dsimp only
  rw [show (X n).toList=[X n] from by unfold X; rfl]
  simp only [X_not_lt_Z,Bool.not_false,if_true,List.filter_cons,
    List.filter_nil,List.map_cons,List.map_nil,divAP_Z_X,TM.Term.ofList]
  rw [Trans.Dict.wcnf]
  rfl

theorem not_le_Z_G (n : Nat) : le (Z zero) (G n)=false := by
  unfold le
  rw [show ((Z zero:Term)==G n)=false from
    beq_eq_false_iff_ne.mpr (Ne.symm (Evidence.WF.ne_of_ltF (G_lt_Z n)))]
  simp only [Bool.false_or]
  exact Evidence.WF.lt_asymm_inT (G_inT n) (by decide) (G_lt_Z n)

theorem collapse_zero_Y (n : Nat) :
    Trans.Dict.collapse 0 (Y n)=phiNF (G n) zero := by
  unfold Trans.Dict.collapse
  simp only [Trans.Dict.reg,TM.Term.ofNat]
  rw [show (Y n).toList=[Y n] from by unfold Y; rfl,wcnf_Y]
  simp only [List.foldl_cons,List.foldl_nil,not_le_Z_G,
    Bool.false_eq_true,if_false]
  rw [show Trans.Dict.sub1 one=zero from rfl]
  simp only [show ((0:Nat)==0)=true from rfl,if_true,Option.getD_some,
    TM.Term.plus_zero]
  rw [Rows.ProofsB.plus_zero_left (Rows.ProofsB.isAP_phiNF _ _)]
  rw [show phiNF (G n) zero=phi (G n) zero from
    Rows.ProofsB.phiNF_zero_arg (by cases n <;> rfl)]
  exact Rows.ProofsB.omegaNF_phi_ne_zero (G_ne_zero n)

theorem dict_D011_G (x : Trans.Dict.BT) (n : Nat)
    (h : Trans.Dict.dict x=G n) :
    Trans.Dict.dict (.D 0 (.D 1 (.D 1 x)))=G (n+1) := by
  rw [Trans.Dict.dict_D,Trans.Dict.dict_D,Trans.Dict.dict_D,h,
    collapse_one_G,collapse_one_X,collapse_zero_Y]
  rw [Rows.ProofsB.phiNF_zero_arg (by cases n <;> rfl)]
  rfl

theorem fB_eq_G : ∀ n : Nat, fB n=G n
  | 0 => rfl
  | n+1 => by
    rw [show fB (n+1)=phiNF (fB n) zero from rfl,fB_eq_G n,
      Rows.ProofsB.phiNF_zero_arg (by cases n <;> rfl)]
    rfl

end Rows.Selected.G7Dict
