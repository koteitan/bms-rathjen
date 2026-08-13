import Rows.G3

open TM Term BMS Trans Rows Rows.Selected

namespace Rows.Selected.G4Dict

def rep1 : Nat → Trans.Dict.BT
  | 0 => .zero
  | m+1 => .D 1 (rep1 m)

abbrev Om : Term := Z zero
def base : Term := plus Om Om
def I (n : Nat) : Term := Evidence.WF.iterPhi zero base n

theorem base_eq_add : base=add Om Om := rfl

theorem iterPhiAt_eq_I : ∀ n, iterPhiAt zero base n=I n
  | 0 => rfl
  | n+1 => by
    rw [iterPhiAt, iterPhiAt_eq_I n]
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
  simp only [show ((Om:Term)==zero)=false from rfl, Bool.false_or,
    Evidence.WF.ltF_right_zero, Bool.or_false]
  have hd : Om.deg+x.deg≤2*(Om.deg+(phi zero x).deg)+7 := by
    simp only [Term.deg]
    omega
  rw [← Evidence.WF.lt_eq_ltF Om x _ hd]
  exact h

theorem le_Om_I : ∀ n, le Om (I n)=true
  | 0 => by
    rw [show I 0=base from rfl, base_eq_add]
    unfold le
    rw [show ((Om:Term)==add Om Om)=false from rfl]
    simp only [Bool.false_or, Evidence.WF.lt_atom_add (s:=Om) rfl]
    exact Evidence.WF.le_self Om
  | n+1 => by
    rw [I_succ]
    exact Evidence.WF.le_of_lt (lt_Z_phi_of_le (I n) (le_Om_I n))

theorem Z_lt_I_succ (n : Nat) : lt Om (I (n+1))=true := by
  rw [I_succ]
  exact lt_Z_phi_of_le (I n) (le_Om_I n)

theorem I_lt_Z1 : ∀ n, lt (I n) (Z one)=true
  | 0 => by decide
  | n+1 => by
    rw [I_succ]
    unfold lt
    cases h : fuelOf (phi zero (I n)) (Z one) with
    | zero => simp [fuelOf] at h
    | succ f =>
      rw [Evidence.WF.ltF_succ_phi_Z]
      simp only [Bool.and_eq_true]
      have hi:=Evidence.WF.deg_pos (I n)
      have hz:=Evidence.WF.deg_pos (Z one)
      have hf : (I n).deg+(Z one).deg≤f := by
        change (I n).deg+(1+one.deg)≤f
        simp only [fuelOf, Term.deg] at h
        omega
      constructor
      · exact Evidence.WF.ltF_left_zero (by omega) (by simp)
      · rw [← Evidence.WF.lt_eq_ltF (I n) (Z one) f hf]
        exact I_lt_Z1 n

theorem I_lt_M (n : Nat) : lt (I n) M=true := by
  cases n with
  | zero => decide
  | succ n => rw [I_succ]; rfl

theorem inT_I : ∀ n, inT (I n)=true
  | 0 => by decide
  | n+1 => by
    rw [I_succ]
    simp only [TM.Term.inT, inT_I n, I_lt_M n]
    rfl

set_option maxHeartbeats 1000000 in
theorem not_le_I_Om_succ (n : Nat) : le (I (n+1)) Om=false := by
  unfold le
  rw [show ((I (n+1):Term)==Om)=false from
    beq_eq_false_iff_ne.mpr (by
      intro h
      have hz:=Z_lt_I_succ n
      rw [h, Evidence.WF.lt_irrefl] at hz
      exact Bool.noConfusion hz)]
  simp only [Bool.false_or]
  exact Evidence.WF.lt_asymm_inT (by decide) (inT_I (n+1)) (Z_lt_I_succ n)

theorem plus_Z_I_succ (n : Nat) : plus Om (I (n+1))=I (n+1) := by
  unfold plus
  rw [show (I (n+1)).toList=[I (n+1)] from by rw [I_succ]; rfl,
    show Om.toList=[Om] from rfl]
  simp only [List.filter_cons, List.filter_nil,
    not_le_I_Om_succ,
    Bool.false_eq_true, if_false]
  rfl

theorem collapse_one_I_succ (n : Nat) :
    Trans.Dict.collapse 1 (I (n+1))=I (n+2) := by
  have hw : Trans.Dict.wcnf (Z one) [I (n+1)]=([],I (n+1)) := by
    rw [Trans.Dict.wcnf, if_pos (I_lt_Z1 (n+1))]
    rfl
  unfold Trans.Dict.collapse
  simp only [Trans.Dict.reg, TM.Term.ofNat]
  rw [show plus zero one=one from rfl]
  rw [show (I (n+1)).toList=[I (n+1)] from by rw [I_succ]; rfl, hw]
  simp only [List.foldl_nil, Option.getD_none]
  rw [Rows.ProofsB.plus_zero_left rfl, plus_Z_I_succ]
  rw [I_succ, I_succ]
  exact Rows.ProofsB.omegaNF_phi zero (I n) |>.trans
    (Rows.ProofsB.phiNF_phi_arg Rows.ProofsB.isSC_zero)

theorem dict_rep1_one : Trans.Dict.dict (rep1 1)=Om := rfl

theorem dict_rep1_succ : ∀ n,
    Trans.Dict.dict (rep1 (n+2))=I (n+1)
  | 0 => rfl
  | n+1 => by
    rw [rep1,Trans.Dict.dict_D,dict_rep1_succ n]
    exact collapse_one_I_succ n

theorem phiShifted_zero_phi (x : Term) (hx : x≠zero) :
    phiShifted zero (phi zero x)=false := by
  have hne : ((phi zero x:Term)==one)=false := by
    apply beq_eq_false_iff_ne.mpr
    intro h
    injection h with _ hz
    exact hx hz
  have hsplit : splitFin (phi zero x)=(phi zero x,0) := by
    simp [splitFin,TM.Term.toList,TM.Term.ofList,hne]
  unfold phiShifted
  rw [hsplit]
  simp [TM.Term.isFP,TM.Term.isSC,Rows.ProofsB.lt_irrefl]

theorem phiShifted_I_succ (n : Nat) : phiShifted zero (I (n+1))=false := by
  rw [I_succ]
  exact phiShifted_zero_phi (I n) (I_ne_zero n)

theorem logOm_I_succ (n : Nat) : Trans.Dict.logOm (I (n+2))=I (n+1) := by
  rw [show I (n+2)=phi zero (I (n+1)) from I_succ (n+1)]
  unfold Trans.Dict.logOm
  simp only [phiShifted_I_succ, Bool.false_eq_true, if_false]

theorem subAP_I (n : Nat) : Trans.Dict.subAP Om (I (n+1))=I (n+1) := by
  rw [I_succ]
  unfold Trans.Dict.subAP
  simp only [TM.Term.toList]
  rw [show ((phi zero (I n):Term)==Om)=false from rfl]
  rfl

theorem divAP_I (n : Nat) : Trans.Dict.divAP Om (I (n+2))=I (n+2) := by
  unfold Trans.Dict.divAP
  rw [logOm_I_succ, subAP_I]
  calc
    omegaNF (I (n+1)) = omegaNF (phi zero (I n)) := by rw [I_succ n]
    _ = phi zero (phi zero (I n)) := Rows.ProofsB.omegaNF_phi zero (I n) |>.trans
      (Rows.ProofsB.phiNF_phi_arg Rows.ProofsB.isSC_zero)
    _ = I (n+2) := by rw [I_succ (n+1), I_succ n]

theorem I_not_lt_Z (n : Nat) : lt (I (n+2)) Om=false := by
  exact Evidence.WF.lt_asymm_inT
    (by decide) (inT_I (n+2))
    (Z_lt_I_succ (n+1))

theorem Z_lt_I (n : Nat) : lt Om (I (n+2))=true := by
  exact Z_lt_I_succ (n+1)

theorem wcnf_I (n : Nat) :
    Trans.Dict.wcnf Om [I (n+3)]=([(I (n+2),one)],zero) := by
  rw [Trans.Dict.wcnf, if_neg (by
    rw [show lt (I (n+3)) Om=false from I_not_lt_Z (n+1)]
    exact Bool.noConfusion)]
  rw [logOm_I_succ (n+1)]
  dsimp only
  rw [show (I (n+2)).toList=[I (n+2)] from by rw [I_succ]; rfl]
  simp only [I_not_lt_Z, Bool.not_false, if_true, List.filter_cons,
    List.filter_nil, List.map_cons, List.map_nil, divAP_I, TM.Term.ofList]
  rw [Trans.Dict.wcnf]
  rfl

theorem mulL_Om_I (n : Nat) :
    Trans.Dict.mulL Om (I (n+2))=I (n+2) := by
  unfold Trans.Dict.mulL
  rw [show (I (n+2)).toList=[I (n+2)] from by rw [I_succ]; rfl]
  simp only [List.map_cons, List.map_nil, TM.Term.ofList]
  rw [logOm_I_succ, plus_Z_I_succ]
  calc
    omegaNF (I (n+1)) = omegaNF (phi zero (I n)) := by rw [I_succ n]
    _ = phi zero (phi zero (I n)) := Rows.ProofsB.omegaNF_phi zero (I n) |>.trans
      (Rows.ProofsB.phiNF_phi_arg Rows.ProofsB.isSC_zero)
    _ = I (n+2) := by rw [I_succ (n+1), I_succ n]

theorem mulL_I_one (n : Nat) :
    Trans.Dict.mulL (I (n+2)) one=I (n+3) := by
  unfold Trans.Dict.mulL
  rw [show one.toList=[one] from rfl]
  simp only [List.map_cons, List.map_nil, TM.Term.ofList]
  rw [show Trans.Dict.logOm one=zero from rfl, TM.Term.plus_zero]
  calc
    omegaNF (I (n+2)) = omegaNF (phi zero (I (n+1))) := by rw [I_succ (n+1)]
    _ = phi zero (phi zero (I (n+1))) :=
      Rows.ProofsB.omegaNF_phi zero (I (n+1)) |>.trans
        (Rows.ProofsB.phiNF_phi_arg Rows.ProofsB.isSC_zero)
    _ = I (n+3) := by rw [I_succ (n+2), I_succ (n+1)]

theorem sub1_I (n : Nat) : Trans.Dict.sub1 (I (n+3))=I (n+3) := by
  rw [I_succ]
  unfold Trans.Dict.sub1
  simp only [TM.Term.toList]
  rw [show ((phi zero (I (n+2)):Term)==one)=false from by
    apply beq_eq_false_iff_ne.mpr
    intro h
    injection h with _ hz
    rw [show I (n+2)=phi zero (I (n+1)) from I_succ (n+1)] at hz
    exact TM.Term.noConfusion hz]
  rfl

theorem collapse_zero_I (n : Nat) :
    Trans.Dict.collapse 0 (I (n+3))=psi Om (I (n+3)) := by
  unfold Trans.Dict.collapse
  simp only [Trans.Dict.reg, TM.Term.ofNat]
  rw [show (I (n+3)).toList=[I (n+3)] from by rw [I_succ]; rfl, wcnf_I]
  simp only [List.foldl_cons, List.foldl_nil,
    show le Om (I (n+2))=true from by
      exact Evidence.WF.le_of_lt (Z_lt_I n), if_true]
  rw [subAP_I (n+1), mulL_Om_I, mulL_I_one, sub1_I]
  rfl

/-- The dictionary image, including the three exceptional initial values. -/
theorem dict_D0_rep1_fC (n : Nat) :
    Trans.Dict.dict (.D 0 (rep1 (n+1)))=Rows.Selected.fC n := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => decide
    | succ n =>
      cases n with
      | zero => decide
      | succ n =>
        rw [Trans.Dict.dict_D,
          show Trans.Dict.dict (rep1 (n+1+1+1+1))=I (n+3) from by
            simpa only [show n+1+1+1+1=n+2+2 by omega,
              show n+3=(n+2)+1 by omega] using dict_rep1_succ (n+2)]
        rw [collapse_zero_I n]
        unfold Rows.Selected.fC
        change psi Om (I (n+3))=psi Om (iterPhiAt zero base (n+3))
        rw [iterPhiAt_eq_I]

#print axioms dict_D0_rep1_fC

end Rows.Selected.G4Dict
