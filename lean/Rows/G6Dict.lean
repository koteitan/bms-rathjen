import Rows.G5

open TM Term Trans Rows Rows.Selected

namespace Rows.Selected.G6Dict

abbrev Om : Term := Z zero
abbrev Z1 : Term := Z one
abbrev Dph : Term := Rows.Selected.Dph

def base : Term := plus Dph Dph
def I (n : Nat) : Term := Evidence.WF.iterPhi zero base n
def J (n : Nat) : Term := plus Z1 (I n)

abbrev X : Trans.Dict.BT := .D 2 .zero

def W : Nat → Trans.Dict.BT → Trans.Dict.BT
  | 0, b => b
  | k+1, b => .sum X (.D 1 (W k b))

theorem iterPhiAt_eq_I : ∀ n, iterPhiAt zero base n=I n
  | 0 => rfl
  | n+1 => by
    rw [iterPhiAt,iterPhiAt_eq_I n]
    unfold I Evidence.WF.iterPhi
    cases n with
    | zero => rfl
    | succ n => exact Rows.ProofsB.phiNF_phi_arg Rows.ProofsB.isSC_zero

theorem I_succ (n : Nat) : I (n+1)=phi zero (I n) := rfl

theorem I_ne_zero (n : Nat) : I n≠zero := by
  cases n with
  | zero => decide
  | succ n => rw [I_succ]; exact TM.Term.noConfusion

theorem lt_Z_phi_of_le (x : Term) (h : le Om x=true) :
    lt Om (phi zero x)=true := by
  unfold lt
  rw [show fuelOf Om (phi zero x)=
      (2*(Om.deg+(phi zero x).deg)+7)+1 from by unfold fuelOf; omega,
    Evidence.WF.ltF_succ_Z_phi]
  simp only [show ((Om:Term)==zero)=false from rfl,Bool.false_or,
    Evidence.WF.ltF_right_zero,Bool.or_false]
  have hd : Om.deg+x.deg≤2*(Om.deg+(phi zero x).deg)+7 := by
    simp only [Term.deg]
    omega
  rw [← Evidence.WF.lt_eq_ltF Om x _ hd]
  exact h

theorem le_Om_I : ∀ n, le Om (I n)=true
  | 0 => by decide
  | n+1 => by
    rw [I_succ]
    exact Evidence.WF.le_of_lt (lt_Z_phi_of_le (I n) (le_Om_I n))

theorem Z_lt_I_succ (n : Nat) : lt Om (I (n+1))=true := by
  rw [I_succ]
  exact lt_Z_phi_of_le (I n) (le_Om_I n)

theorem I_lt_Z1 : ∀ n, lt (I n) Z1=true
  | 0 => by decide
  | n+1 => by
    rw [I_succ]
    unfold lt
    cases h : fuelOf (phi zero (I n)) Z1 with
    | zero => simp [fuelOf] at h
    | succ f =>
      rw [Evidence.WF.ltF_succ_phi_Z]
      simp only [Bool.and_eq_true]
      have hi:=Evidence.WF.deg_pos (I n)
      have hz:=Evidence.WF.deg_pos Z1
      have hf : (I n).deg+Z1.deg≤f := by
        change (I n).deg+(1+one.deg)≤f
        simp only [fuelOf,Term.deg] at h
        omega
      constructor
      · exact Evidence.WF.ltF_left_zero (by omega) (by simp)
      · rw [← Evidence.WF.lt_eq_ltF (I n) Z1 f hf]
        exact I_lt_Z1 n

theorem I_lt_M (n : Nat) : lt (I n) M=true := by
  cases n with
  | zero => decide
  | succ n => rw [I_succ]; rfl

theorem inT_I : ∀ n, inT (I n)=true
  | 0 => by decide
  | n+1 => by
    rw [I_succ]
    simp only [TM.Term.inT,inT_I n,I_lt_M n]
    rfl

set_option maxHeartbeats 1000000 in
theorem not_le_I_Om_succ (n : Nat) : le (I (n+1)) Om=false := by
  unfold le
  rw [show ((I (n+1):Term)==Om)=false from
    beq_eq_false_iff_ne.mpr (by
      intro h
      have hz:=Z_lt_I_succ n
      rw [h,Evidence.WF.lt_irrefl] at hz
      exact Bool.noConfusion hz)]
  simp only [Bool.false_or]
  exact Evidence.WF.lt_asymm_inT (by decide) (inT_I (n+1)) (Z_lt_I_succ n)

theorem plus_Z_I_succ (n : Nat) : plus Om (I (n+1))=I (n+1) := by
  unfold plus
  rw [show (I (n+1)).toList=[I (n+1)] from by rw [I_succ]; rfl,
    show Om.toList=[Om] from rfl]
  simp only [List.filter_cons,List.filter_nil,not_le_I_Om_succ,
    Bool.false_eq_true,if_false]
  rfl

theorem le_Dph_I : ∀ n, le Dph (I n)=true
  | 0 => by decide
  | n+1 => Evidence.WF.le_of_lt (by
      rw [I_succ]
      change lt (phi one Om) (phi zero (I n))=true
      rw [Evidence.WF.lt_phi_phi (by
        intro h
        injection h with h1 _
        exact TM.Term.noConfusion h1),
        if_neg (by intro h; exact TM.Term.noConfusion h),
        if_neg (by decide)]
      exact le_Dph_I n)

theorem Dph_lt_I_succ (n : Nat) : lt Dph (I (n+1))=true := by
  rw [I_succ]
  change lt (phi one Om) (phi zero (I n))=true
  rw [Evidence.WF.lt_phi_phi (by
    intro h
    injection h with h1 _
    exact TM.Term.noConfusion h1),
    if_neg (by intro h; exact TM.Term.noConfusion h),
    if_neg (by decide)]
  exact le_Dph_I n

theorem not_le_I_Dph_succ (n : Nat) : le (I (n+1)) Dph=false := by
  unfold le
  rw [show ((I (n+1):Term)==Dph)=false from
    beq_eq_false_iff_ne.mpr (by
      intro h
      have hd:=Dph_lt_I_succ n
      rw [h,Evidence.WF.lt_irrefl] at hd
      exact Bool.noConfusion hd)]
  simp only [Bool.false_or]
  exact Evidence.WF.lt_asymm_inT (by decide) (inT_I (n+1)) (Dph_lt_I_succ n)

theorem plus_Dph_I_succ (n : Nat) : plus Dph (I (n+1))=I (n+1) :=
  Rows.ProofsB.plus_drop rfl (by rw [I_succ]; rfl) (not_le_I_Dph_succ n)

theorem toList_J_succ (n : Nat) : (J (n+1)).toList=[Z1,I (n+1)] := by
  unfold J plus
  rw [show Z1.toList=[Z1] from rfl,
    show (I (n+1)).toList=[I (n+1)] from by rw [I_succ]; rfl]
  change (ofList (([Z1].filter (fun a=>le (I (n+1)) a))++[I (n+1)])).toList=_
  simp only [List.filter_cons,List.filter_nil]
  rw [show le (I (n+1)) Z1=true from Evidence.WF.le_of_lt (I_lt_Z1 (n+1))]
  rfl

theorem wcnf_J_succ (n : Nat) :
    Trans.Dict.wcnf Z1 [Z1,I (n+1)]=([(one,one)],I (n+1)) := by
  unfold Trans.Dict.wcnf
  rw [show lt Z1 Z1=false from Evidence.WF.lt_irrefl Z1]
  simp only [Bool.false_eq_true,if_false]
  rw [show Trans.Dict.logOm Z1=Z1 from rfl,
    show Z1.toList=[Z1] from rfl]
  simp only [List.filter_cons,List.filter_nil,
    show lt Z1 Z1=false from Evidence.WF.lt_irrefl Z1,
    Bool.not_false,if_true,List.map_cons,List.map_nil,
    show Trans.Dict.divAP Z1 Z1=one from rfl,TM.Term.ofList,
    I_lt_Z1 (n+1),Trans.Dict.wcnf]
  rfl

theorem collapse_one_J_succ (n : Nat) :
    Trans.Dict.collapse 1 (J (n+1))=I (n+2) := by
  unfold Trans.Dict.collapse
  rw [show Trans.Dict.reg (1+1)=Z1 from rfl,
    show Trans.Dict.reg 1=Om from rfl]
  rw [toList_J_succ]
  simp only [wcnf_J_succ]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show le Z1 one=false from by decide]
  simp only [Bool.false_eq_true,if_false,
    show ((1:Nat)==0)=false from rfl,
    show Trans.Dict.sub1 one=zero from rfl,
    TM.Term.plus_zero,Option.getD_some]
  rw [show phiNF one (plus Om one)=Dph from by decide,
    plus_Dph_I_succ,plus_Z_I_succ]
  rw [I_succ,I_succ]
  exact Rows.ProofsB.omegaNF_phi zero (I n) |>.trans
    (Rows.ProofsB.phiNF_phi_arg Rows.ProofsB.isSC_zero)

theorem phiShifted_I : ∀ n, phiShifted zero (I n)=false
  | 0 => by decide
  | n+1 => by
    rw [I_succ]
    exact G4Dict.phiShifted_zero_phi (I n) (I_ne_zero n)

theorem logOm_I_succ (n : Nat) : Trans.Dict.logOm (I (n+1))=I n := by
  rw [I_succ]
  unfold Trans.Dict.logOm
  change (if phiShifted zero (I n)=true then plus (I n) one else I n)=I n
  rw [phiShifted_I]
  rfl

theorem subAP_I_succ (n : Nat) :
    Trans.Dict.subAP Om (I (n+1))=I (n+1) := by
  rw [I_succ]
  unfold Trans.Dict.subAP
  simp only [TM.Term.toList]
  rw [show ((phi zero (I n):Term)==Om)=false from rfl]
  rfl

theorem I_not_lt_Om_succ (n : Nat) : lt (I (n+1)) Om=false :=
  Evidence.WF.lt_asymm_inT (by decide) (inT_I (n+1)) (Z_lt_I_succ n)

theorem divAP_I_succ : ∀ n,
    Trans.Dict.divAP Om (I (n+1))=I (n+1)
  | 0 => by decide
  | n+1 => by
    unfold Trans.Dict.divAP
    rw [logOm_I_succ,subAP_I_succ]
    calc
      omegaNF (I (n+1)) = omegaNF (phi zero (I n)) := by rw [I_succ]
      _ = phi zero (phi zero (I n)) :=
        Rows.ProofsB.omegaNF_phi zero (I n) |>.trans
          (Rows.ProofsB.phiNF_phi_arg Rows.ProofsB.isSC_zero)
      _ = I (n+1+1) := by rw [I_succ (n+1),I_succ n]

theorem wcnf_I_succ : ∀ n,
    Trans.Dict.wcnf Om [I (n+1)]=([(I n,one)],zero)
  | 0 => by decide
  | n+1 => by
    unfold Trans.Dict.wcnf
    rw [I_not_lt_Om_succ (n+1)]
    simp only [Bool.false_eq_true,if_false,logOm_I_succ]
    rw [show (I (n+1)).toList=[I (n+1)] from by rw [I_succ]; rfl]
    simp only [I_not_lt_Om_succ n,Bool.not_false,if_true,List.filter_cons,
      List.filter_nil,List.map_cons,List.map_nil,divAP_I_succ,TM.Term.ofList,
      Trans.Dict.wcnf]
    rfl

theorem mulL_Om_I_succ : ∀ n,
    Trans.Dict.mulL Om (I (n+1))=I (n+1)
  | 0 => by decide
  | n+1 => by
    unfold Trans.Dict.mulL
    rw [show (I (n+1+1)).toList=[I (n+1+1)] from by rw [I_succ]; rfl]
    simp only [List.map_cons,List.map_nil,TM.Term.ofList]
    rw [logOm_I_succ,plus_Z_I_succ]
    calc
      omegaNF (I (n+1)) = omegaNF (phi zero (I n)) := by rw [I_succ]
      _ = phi zero (phi zero (I n)) :=
        Rows.ProofsB.omegaNF_phi zero (I n) |>.trans
          (Rows.ProofsB.phiNF_phi_arg Rows.ProofsB.isSC_zero)
      _ = I (n+1+1) := by rw [I_succ (n+1),I_succ n]

theorem mulL_I_one_succ (n : Nat) :
    Trans.Dict.mulL (I (n+1)) one=I (n+2) := by
  unfold Trans.Dict.mulL
  rw [show one.toList=[one] from rfl]
  simp only [List.map_cons,List.map_nil,TM.Term.ofList]
  rw [show Trans.Dict.logOm one=zero from rfl,TM.Term.plus_zero]
  calc
    omegaNF (I (n+1)) = omegaNF (phi zero (I n)) := by rw [I_succ]
    _ = phi zero (phi zero (I n)) :=
      Rows.ProofsB.omegaNF_phi zero (I n) |>.trans
        (Rows.ProofsB.phiNF_phi_arg Rows.ProofsB.isSC_zero)
    _ = I (n+2) := by rw [I_succ (n+1),I_succ n]

theorem sub1_I_succ (n : Nat) : Trans.Dict.sub1 (I (n+1))=I (n+1) := by
  rw [I_succ]
  unfold Trans.Dict.sub1
  simp only [TM.Term.toList]
  rw [show ((phi zero (I n):Term)==one)=false from by
    apply beq_eq_false_iff_ne.mpr
    intro h
    injection h with _ hz
    exact I_ne_zero n hz]
  rfl

theorem ne_Z1_I (n : Nat) : (Z1==I n)=false := by
  apply beq_eq_false_iff_ne.mpr
  intro h
  have hi:=I_lt_Z1 n
  rw [← h,Evidence.WF.lt_irrefl] at hi
  exact Bool.noConfusion hi

theorem wcnf_J_Om_succ (n : Nat) :
    Trans.Dict.wcnf Om [Z1,I (n+1)]=
      ([(Z1,one),(I n,one)],zero) := by
  unfold Trans.Dict.wcnf
  rw [show lt Z1 Om=false from by decide]
  simp only [Bool.false_eq_true,if_false]
  rw [show Trans.Dict.logOm Z1=Z1 from rfl,
    show Z1.toList=[Z1] from rfl]
  simp only [List.filter_cons,List.filter_nil,
    show lt Z1 Om=false from by decide,Bool.not_false,if_true,
    List.map_cons,List.map_nil,
    show Trans.Dict.divAP Om Z1=Z1 from rfl,TM.Term.ofList]
  rw [wcnf_I_succ n]
  simp only
  rw [ne_Z1_I n]
  simp only [Bool.false_eq_true,if_false,TM.Term.ofList]
  rfl

theorem subAP_Om_Z1 : Trans.Dict.subAP Om Z1=Z1 := rfl
theorem mulL_Om_Z1 : Trans.Dict.mulL Om Z1=Z1 := rfl
theorem mulL_Z1_one : Trans.Dict.mulL Z1 one=Z1 := rfl
theorem sub1_Z1 : Trans.Dict.sub1 Z1=Z1 := rfl

theorem collapse_zero_J_succ : ∀ n,
    Trans.Dict.collapse 0 (J (n+1))=psi Om (J (n+1))
  | 0 => by decide
  | n+1 => by
    unfold Trans.Dict.collapse
    simp only [Trans.Dict.reg,TM.Term.ofNat]
    rw [toList_J_succ,wcnf_J_Om_succ]
    simp only [List.foldl_cons,List.foldl_nil,
      show le Om Z1=true from by decide,if_true,
      show le Om (I (n+1))=true from le_Om_I (n+1)]
    rw [subAP_Om_Z1,mulL_Om_Z1,mulL_Z1_one,sub1_Z1,
      subAP_I_succ,mulL_Om_I_succ,mulL_I_one_succ]
    simp only [Option.getD_some,TM.Term.plus_zero]
    change omegaNF (plus zero (psi Om (J (n+2))))=psi Om (J (n+2))
    rw [Rows.ProofsB.plus_zero_left (X:=psi Om (J (n+2))) rfl]
    rfl

theorem dict_X : Trans.Dict.dict X=Z1 := rfl

theorem dict_W_X : ∀ n, Trans.Dict.dict (W (n+2) X)=J (n+1)
  | 0 => by decide
  | n+1 => by
    rw [show n+1+2=(n+2)+1 by omega,W,Trans.Dict.dict_sum,
      dict_X,Trans.Dict.dict_D,dict_W_X n,collapse_one_J_succ]
    rfl

theorem dict_D0_W_fF (n : Nat) :
    Trans.Dict.dict (.D 0 (W (n+2) X))=Rows.Selected.fF (n+1) := by
  rw [Trans.Dict.dict_D,dict_W_X,collapse_zero_J_succ]
  unfold Rows.Selected.fF J
  change psi Om (plus Z1 (I (n+1)))=
    psi Om (plus Z1 (iterPhiAt zero base (n+1)))
  rw [iterPhiAt_eq_I]

#print axioms dict_D0_W_fF

end Rows.Selected.G6Dict
