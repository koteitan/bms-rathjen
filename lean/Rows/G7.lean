import Rows.G7Dict

open TM Term BMS Trans Rows Rows.Selected

namespace Rows.Selected
namespace G7

def M : BMS.Matrix := [[0,0],[1,1],[2,1],[3,1]]
def t : Term := psi (Z zero) zero

/-- Row-one value of an ascending tail column. -/
def q (a : Nat) : Int := if a % 3 = 0 then 0 else 1

/-- An ascending row-zero ladder with the periodic row-one pattern `0,1,1`. -/
def A (a p m : Nat) : Trans.Recal.PS :=
  (List.range m).map fun k => ((((a+k:Nat):Int)), q (p+k))

/-- The parsed expansion after `m` individual tail columns. -/
def L (m : Nat) : Trans.Recal.PS := (0,0) :: (1,1) :: (2,1) :: A 3 3 m
def R (m : Nat) : Trans.Recal.PS := (2,1) :: A 3 3 m
def E (a p m : Nat) : Trans.Recal.PS := (((a:Nat):Int),(1:Int)) :: A (a+1) p m
def S (m : Nat) : Trans.Recal.PS := (0,0) :: E 3 3 m

/-- The right-nested Buchholz tail beginning at row-zero index `a`. -/
def P : Nat → Nat → Trans.Dict.BT
  | _, 0 => .zero
  | a, m+1 => .D (q a).toNat (P (a+1) m)

def LBT (m : Nat) : Trans.Dict.BT := .D 0 (.D 1 (.D 1 (P 3 m)))

theorem A_zero (a p : Nat) : A a p 0=[] := rfl

theorem A_succ (a p m : Nat) :
    A a p (m+1)=((((a:Nat):Int),q p))::A (a+1) (p+1) m := by
  unfold A
  rw [List.range_succ_eq_map,List.map_cons,List.map_map]
  congr 1
  apply List.map_congr_left
  intro k _
  apply Prod.ext
  · simp
    push_cast
    omega
  · simp
    congr 1
    omega

theorem A_succ_last (a p m : Nat) :
    A a p (m+1)=A a p m++[((((a+m:Nat):Int),q (p+m)))] := by
  unfold A
  rw [List.range_succ,List.map_append]
  simp [Nat.add_comm]

theorem length_A (a p m : Nat) : (A a p m).length=m := by simp [A]

theorem incrFirst_A (a p d m : Nat) :
    Trans.Recal.incrFirst (A a p m) (d:Int)=A (a+d) p m := by
  unfold Trans.Recal.incrFirst A
  rw [List.map_map]
  apply List.map_congr_left
  intro k _
  apply Prod.ext
  · simp
    push_cast
    omega
  · simp

theorem incrFirst_A_neg (a p d m : Nat) (hd : d≤a) :
    Trans.Recal.incrFirst (A a p m) (-(d:Int))=A (a-d) p m := by
  unfold Trans.Recal.incrFirst A
  rw [List.map_map]
  apply List.map_congr_left
  intro k _
  apply Prod.ext
  · simp
    push_cast
    omega
  · simp

theorem derp_A (a p m : Nat) :
    Trans.Recal.derp (A a p (m+1))=A (a+1) (p+1) m := by
  rw [A_succ]
  rfl

theorem L_succ (m : Nat) :
    L (m+1)=L m++[((((m+3:Nat):Int),q (m+3)))] := by
  unfold L
  rw [A_succ_last]
  simp [Nat.add_comm]

theorem length_L (m : Nat) : (L m).length=m+3 := by simp [L,length_A]

theorem lenI_L (m : Nat) : Trans.Recal.lenI (L m)=(m:Int)+3 := by
  unfold Trans.Recal.lenI
  rw [length_L]
  omega

theorem predP_L (m : Nat) : Trans.Recal.predP (L (m+1))=L m := by
  rw [L_succ]
  unfold Trans.Recal.predP
  rw [show ((L m++[((((m+3:Nat):Int),q (m+3)))]).length==1)=false from by
    rw [List.length_append,length_L]
    simp]
  simp

/-! ### Link 1: expansion and parsing. -/

theorem expand_M (n : Nat) :
    BMS.expand M n=[[0,0],[1,1],[2,1]]++
      ((List.range n).map fun a =>
        ([[3+3*a,0],[4+3*a,1],[5+3*a,1]] : BMS.Matrix)).flatten := by
  show (BMS.expand? M n).getD []=_
  have h : BMS.expand? M n=some (M.take 0++
      ((List.range (n+1)).map fun a =>
        ([[0+a*3*1,0+a*0*1],[1+a*3*1,1+a*0*1],
          [2+a*3*1,1+a*0*1]] : BMS.Matrix)).flatten) := rfl
  have hf : (fun a : Nat =>
      ([[0+a*3*1,0+a*0*1],[1+a*3*1,1+a*0*1],
        [2+a*3*1,1+a*0*1]] : BMS.Matrix))=
      fun a => [[3*a,0],[1+3*a,1],[2+3*a,1]] := by
    funext a
    simp [Nat.mul_comm]
  rw [h,hf,List.range_succ_eq_map]
  simp only [Option.getD_some,M,List.take,List.map_cons,List.flatten_cons,
    List.map_map,List.singleton_append,List.nil_append]
  have hb : ((fun a : Nat => ([[3*a,0],[1+3*a,1],[2+3*a,1]]:BMS.Matrix)) ∘ Nat.succ)=
      fun a => [[3+3*a,0],[4+3*a,1],[5+3*a,1]] := by
    funext a
    simp only [Function.comp_apply]
    rw [show 3*(a+1)=3+3*a by omega,
      show 1+(3+3*a)=4+3*a by omega,
      show 2+(3+3*a)=5+3*a by omega]
  rw [hb]

theorem q_three_mul (a : Nat) : q (3*a)=0 := by simp [q]
theorem q_three_mul_one (a : Nat) : q (3*a+1)=1 := by simp [q]
theorem q_three_mul_two (a : Nat) : q (3*a+2)=1 := by simp [q]

theorem A_three_mul (n : Nat) :
    A 3 3 (3*n)=((List.range n).map fun a =>
      ([(((3+3*a:Nat):Int),(0:Int)),(((4+3*a:Nat):Int),(1:Int)),
        (((5+3*a:Nat):Int),(1:Int))] : Trans.Recal.PS)).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show 3*(n+1)=3*n+3 by omega,A_succ_last,A_succ_last,A_succ_last,ih,
      List.range_succ,List.map_append,List.flatten_append]
    simp only [List.map_singleton,List.flatten_singleton,List.append_assoc,
      List.singleton_append]
    rw [show 3+3*n=3*(n+1) by omega,
      show 3+(3*n+1)=3*n+4 by omega,
      show 3+(3*n+2)=3*n+5 by omega,
      q_three_mul (n+1),
      show 3*n+4=3*(n+1)+1 by omega,
      show 3*n+5=3*(n+1)+2 by omega,
      q_three_mul_one (n+1),q_three_mul_two (n+1)]
    rw [show 3*(n+1)+1=4+3*n by omega,
      show 3*(n+1)+2=5+3*n by omega]
    simp only [List.cons_append,List.nil_append]

theorem map_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[3+3*a,0],[4+3*a,1],[5+3*a,1]] : BMS.Matrix)).flatten).map
        (fun c => ((c.getD 0 0:Int),(c.getD 1 0:Int)))=A 3 3 (3*n) := by
  rw [A_three_mul]
  rw [List.map_flatten]
  apply congrArg List.flatten
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  simp

theorem all_len_blocks (n : Nat) :
    (((List.range n).map fun a =>
      ([[3+3*a,0],[4+3*a,1],[5+3*a,1]] : BMS.Matrix)).flatten).all
        (fun c => decide (c.length≤2))=true := by simp

/-- Link 1: each expansion lands on a three-column-complete prefix. -/
theorem ofMatrix_M (n : Nat) :
    Trans.Recal.ofMatrix (BMS.expand M n)=some (L (3*n)) := by
  rw [expand_M]
  unfold Trans.Recal.ofMatrix
  rw [show (([[0,0],[1,1],[2,1]]:BMS.Matrix)++
      ((List.range n).map fun a =>
        ([[3+3*a,0],[4+3*a,1],[5+3*a,1]]:BMS.Matrix)).flatten).isEmpty=false from by rfl]
  rw [List.all_append,all_len_blocks]
  simp only [List.all_cons,List.length_cons,List.length_nil,Bool.and_true,
    Bool.not_false,Bool.true_and,List.map_append,List.map_cons,List.map_nil]
  rw [map_blocks]
  rfl

#guard (List.range 8).all fun n =>
  Trans.Recal.ofMatrix (BMS.expand M n)==some (L (3*n))
#guard (List.range 14).all fun m => Trans.Recal.predP (L (m+1))==L m
#guard rest12.any fun r => r.m==M && r.t==t

/-! ### Row-zero structure. -/

theorem getD_A (a p m k : Nat) (hk : k<m) :
    (A a p m).getD k (0,0)=((((a+k:Nat):Int),q (p+k))) := by
  unfold A
  rw [List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range hk]
  rfl

theorem gp0_A (a p m k : Nat) (hk : k<m) :
    Trans.Recal.gp0 (A a p m) (k:Int)=((a+k:Nat):Int) := by
  show (if (k:Int)<0 then 0 else ((A a p m).getD k (0,0)).1)=_
  rw [if_neg (by omega),getD_A a p m k hk]

theorem gp1_A (a p m k : Nat) (hk : k<m) :
    Trans.Recal.gp1 (A a p m) (k:Int)=q (p+k) := by
  show (if (k:Int)<0 then 0 else ((A a p m).getD k (0,0)).2)=_
  rw [if_neg (by omega),getD_A a p m k hk]

theorem gp0_L (m k : Nat) (hk : k<m+3) :
    Trans.Recal.gp0 (L m) (k:Int)=(k:Int) := by
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      cases k with
      | zero => rfl
      | succ j =>
        show (if ((j+3:Nat):Int)<0 then 0 else ((L m).getD (j+3) (0,0)).1)=_
        rw [if_neg (by omega)]
        change ((A 3 3 m).getD j (0,0)).1=_
        rw [getD_A 3 3 m j (by omega)]
        push_cast
        omega

theorem fpar_L (m k : Nat) (hk0 : 0<k) (hk : k<m+3) :
    Trans.Recal.fpar (L m) 0 (k:Int) 0=((k-1:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega),if_pos (by rfl),gp0_L m k hk,length_L]
  obtain ⟨j,rfl⟩ : ∃ j,k=j+1 := ⟨k-1,by omega⟩
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),show ((j+1:Nat):Int)-1=(j:Int) by omega,
    gp0_L m j (by omega),if_pos (by omega)]
  omega

theorem isAncAux_L (m k : Nat) : ∀ f : Nat, k<m+3 → k<f →
    Trans.Recal.isAncAux f (L m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ f : Nat,k<m+3 → k<f →
    Trans.Recal.isAncAux f (L m) 0 (k:Int) 0=true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0:k=0
    · subst k
      rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      rw [fpar_L m k (by omega) hkm]
      rw [show (((k-1:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isPrincipalP_L (m : Nat) : Trans.Recal.isPrincipalP (L m)=true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (L m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_L]
    simp]
  simp only [Bool.not_false,Bool.true_and]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_L]; omega),length_L,lenI_L,
    show (m:Int)+3-1=((m+2:Nat):Int) by push_cast; omega]
  exact isAncAux_L m (m+2) (m+4) (by omega) (by omega)

/-! ### Principal tails and the two-step reduction. -/

theorem length_E (a p m : Nat) : (E a p m).length=m+1 := by
  simp [E,length_A]

theorem lenI_E (a p m : Nat) : Trans.Recal.lenI (E a p m)=(m:Int)+1 := by
  unfold Trans.Recal.lenI
  rw [length_E]
  omega

theorem gp0_E (a p m k : Nat) (hk : k<m+1) :
    Trans.Recal.gp0 (E a p m) (k:Int)=((a+k:Nat):Int) := by
  cases k with
  | zero => rfl
  | succ k =>
    show (if ((k+1:Nat):Int)<0 then 0 else ((E a p m).getD (k+1) (0,0)).1)=_
    rw [if_neg (by omega)]
    change ((A (a+1) p m).getD k (0,0)).1=_
    rw [getD_A (a+1) p m k (by omega)]
    push_cast
    omega

theorem fpar_E (a p m k : Nat) (hk0 : 0<k) (hk : k<m+1) :
    Trans.Recal.fpar (E a p m) 0 (k:Int) 0=((k-1:Nat):Int) := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_E]; omega),if_pos (by rfl),gp0_E a p m k hk,length_E]
  obtain ⟨j,rfl⟩ : ∃ j,k=j+1 := ⟨k-1,by omega⟩
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),show ((j+1:Nat):Int)-1=(j:Int) by omega,
    gp0_E a p m j (by omega),if_pos (by omega)]
  push_cast
  omega

theorem fpar_E_zero (a p m : Nat) :
    Trans.Recal.fpar (E a p m) 0 0 0=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_E]; omega),if_pos (by rfl),length_E]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem isAncAux_E (a p m k : Nat) : ∀ f : Nat, k<m+1 → k<f →
    Trans.Recal.isAncAux f (E a p m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ f : Nat,k<m+1 → k<f →
    Trans.Recal.isAncAux f (E a p m) 0 (k:Int) 0=true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0:k=0
    · subst k
      rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      rw [fpar_E a p m k (by omega) hkm]
      rw [show (((k-1:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isPrincipalP_E (a p m : Nat) : Trans.Recal.isPrincipalP (E a p m)=true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (E a p m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_E]
    cases m <;> rfl]
  simp only [Bool.not_false,Bool.true_and]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_E]; omega),length_E,lenI_E,
    show (m:Int)+1-1=(m:Int) by omega]
  exact isAncAux_E a p m m (m+2) (by omega) (by omega)

theorem fAncAux_E_last (a p m k : Nat) : ∀ (f : Nat) (acc : List Int),
    k<m+1 → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (E a p m) 0 (k:Int) 0 acc).getLast?=some 0 := by
  refine Nat.strongRecOn (motive:=fun k => ∀ (f : Nat) (acc : List Int),
    k<m+1 → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (E a p m) 0 (k:Int) 0 acc).getLast?=some 0) k ?_
  intro k ih f acc hkm hkf hlast
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.fAncAux]
    by_cases hk0:k=0
    · subst k
      rw [show Trans.Recal.fpar (E a p m) 0 ((0:Nat):Int) 0=-1 from by
        simpa using fpar_E_zero a p m,if_neg (by omega)]
      exact hlast
    · rw [fpar_E a p m k (by omega) hkm,if_pos (by omega)]
      exact ih (k-1) (by omega) f (acc++[((k-1:Nat):Int)])
        (by omega) (by omega) (by simp)

theorem fAnc_E_last (a p m : Nat) :
    (Trans.Recal.fAnc (E a p m) 0 (m:Int) 0).getLast?=some 0 := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_E]; omega),length_E]
  exact fAncAux_E_last a p m m (m+2) [(m:Int)]
    (by omega) (by omega) (by simp)

theorem slice_E_full (a p m : Nat) :
    Trans.Recal.slice (E a p m) 0 ((m+1:Nat):Int)=E a p m := by
  unfold Trans.Recal.slice
  simp only [Int.toNat_zero,List.drop_zero]
  rw [show (((m+1:Nat):Int)-0).toNat=m+1 by omega]
  simpa only [length_E] using
    (List.take_length : (E a p m).take (E a p m).length=E a p m)

theorem ppair_E (a p m : Nat) : Trans.Recal.ppair (E a p m)=[E a p m] := by
  unfold Trans.Recal.ppair
  rw [length_E,lenI_E]
  simp only [Trans.Recal.ppairAux]
  rw [if_neg (by omega),show (m:Int)+1-1=(m:Int) by omega,fAnc_E_last]
  simp only [Option.getD_some]
  rw [show (m:Int)+1=((m+1:Nat):Int) by omega,slice_E_full]
  rw [if_pos (by omega)]

theorem fpar0_L_one (m : Nat) : Trans.Recal.fpar0 (L m) 1 0=0 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  simp only [Trans.Recal.fpar0Aux]
  rfl

theorem fpar0_L_two (m : Nat) : Trans.Recal.fpar0 (L m) 2 1=1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  simp only [Trans.Recal.fpar0Aux]
  rfl

theorem fpar0_L_one_lb (m : Nat) : Trans.Recal.fpar0 (L m) 1 1=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar1_L_one (m : Nat) : Trans.Recal.fpar (L m) 1 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  show (let j1:=Trans.Recal.fpar0 (L m) 1 0
    if j1<0 then -1 else if Trans.Recal.gp1 (L m) j1<1 then j1
    else Trans.Recal.fpar1Aux (m+2) (L m) 1 j1 0)=0
  rw [fpar0_L_one]
  rfl

theorem fpar1_L_two_lb (m : Nat) : Trans.Recal.fpar (L m) 1 2 1=-1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  show (let j1:=Trans.Recal.fpar0 (L m) 2 1
    if j1<1 then -1 else if Trans.Recal.gp1 (L m) j1<1 then j1
    else Trans.Recal.fpar1Aux (m+3) (L m) 1 j1 1)=-1
  rw [fpar0_L_two]
  simp only [show ¬((1:Int)<1) by omega,if_false]
  rw [show Trans.Recal.gp1 (L m) 1=1 from rfl,if_neg (by omega)]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_L_one_lb,if_pos (by omega)]

theorem fpar1_L_two (m : Nat) : Trans.Recal.fpar (L m) 1 2 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  rw [show Trans.Recal.gp1 (L m) 2=1 from rfl]
  simp only [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (L m) 2 0=1 from by
    unfold Trans.Recal.fpar0
    rw [if_neg (by rw [lenI_L]; omega),length_L]
    simp only [Trans.Recal.fpar0Aux]
    rfl]
  rw [if_neg (by omega),show Trans.Recal.gp1 (L m) 1=1 from rfl,if_neg (by omega)]
  rw [fpar0_L_one,if_neg (by omega),show Trans.Recal.gp1 (L m) 0=0 from rfl,
    if_pos (by omega)]

theorem trMax_L (m : Nat) : Trans.Recal.trMax (L m)=1 := by
  show Trans.Recal.trMaxAux ((L m).length+1) (L m) 0=1
  rw [length_L]
  simp only [Trans.Recal.trMaxAux]
  rw [if_neg (by rw [lenI_L]; omega)]
  rw [show Trans.Recal.isParentP (L m) 1 (0+1) 0=true from by
    unfold Trans.Recal.isParentP
    rw [show Trans.Recal.fpar (L m) 1 (0+1) 0=0 from by simpa using fpar1_L_one m]
    unfold Trans.Recal.lenI
    rw [length_L]
    rw [show decide ((0:Int)<((m+3:Nat):Int))=true from decide_eq_true (by omega)]
    rfl]
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [if_neg (by rw [lenI_L]; omega)]
  rw [show Trans.Recal.isParentP (L m) 1 (0+1+1) (0+1)=false from by
    unfold Trans.Recal.isParentP
    rw [show Trans.Recal.fpar (L m) 1 (0+1+1) (0+1)=-1 from by
      simpa using fpar1_L_two_lb m]
    simp,if_pos (by rfl)]
  omega

theorem brF_L (m : Nat) : Trans.Recal.brF (L m)=[R m] := by
  unfold Trans.Recal.brF
  rw [trMax_L]
  show Trans.Recal.ppair (R m)=[R m]
  exact ppair_E 2 3 m

theorem firstNodes_L (m : Nat) :
    Trans.Recal.firstNodes (L m)=[2,((m+3:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_L,trMax_L]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show (R m).length=m+1 from length_E 2 3 m]
  simp
  omega

theorem joints_L (m : Nat) : Trans.Recal.joints (L m)=[1] := by
  unfold Trans.Recal.joints
  rw [firstNodes_L]
  change [Trans.Recal.fpar (L m) 0 2 0]=[1]
  rw [show Trans.Recal.fpar (L m) 0 2 0=1 from by
    simpa using fpar_L m 2 (by omega) (by omega)]

theorem incrFirst_E (a p d m : Nat) :
    Trans.Recal.incrFirst (E a p m) (d:Int)=E (a+d) p m := by
  unfold E
  change (((a:Int)+(d:Int)),1)::Trans.Recal.incrFirst (A (a+1) p m) (d:Int)=
    (((a+d:Nat):Int),1)::A (a+d+1) p m
  rw [incrFirst_A]
  rw [show a+1+d=a+d+1 by omega]
  have hh : (((a:Int)+(d:Int)),(1:Int))=(((a+d:Nat):Int),(1:Int)) := by
    apply Prod.ext
    · push_cast
      omega
    · rfl
  exact congrArg (fun z => z::A (a+d+1) p m) hh

theorem incrFirst_E_neg (a p d m : Nat) (hd : d≤a) :
    Trans.Recal.incrFirst (E a p m) (-(d:Int))=E (a-d) p m := by
  unfold E
  change (((a:Int)-(d:Int)),1)::Trans.Recal.incrFirst (A (a+1) p m) (-(d:Int))=
    (((a-d:Nat):Int),1)::A (a-d+1) p m
  rw [incrFirst_A_neg (a+1) p d m (by omega)]
  rw [show a+1-d=a-d+1 by omega]
  have hh : (((a:Int)-(d:Int)),(1:Int))=(((a-d:Nat):Int),(1:Int)) := by
    apply Prod.ext
    · push_cast
      omega
    · rfl
  exact congrArg (fun z => z::A (a-d+1) p m) hh

theorem R_to_S (m : Nat) :
    Trans.Recal.jjSeq 0 (Trans.Recal.gp1 (R m) 0-1)++
      Trans.Recal.incrFirst (R m) (Trans.Recal.gp1 (R m) 0)=S m := by
  change [((0:Int),(0:Int))]++Trans.Recal.incrFirst (E 2 3 m) 1=S m
  rw [show Trans.Recal.incrFirst (E 2 3 m) 1=E 3 3 m from by
    simpa using incrFirst_E 2 3 1 m]
  rfl

theorem red_R (m : Nat) : Trans.Recal.red 1 (R m)=E 1 3 m := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (R m)=false from by
      show Trans.Recal.isZeroP (E 2 3 m)=false
      unfold Trans.Recal.isZeroP
      rw [length_E]
      cases m <;> rfl,
    show Trans.Recal.isPrincipalP (R m)=true from isPrincipalP_E 2 3 m]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (R m) 0==0 && Trans.Recal.gp1 (R m) 0==0)=false from by rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show (Trans.Recal.gp1 (R m) 0==0)=false from by rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [R_to_S]
  simp only [Trans.Recal.red]
  rw [show Trans.Recal.gp1 (R m) 0=1 from rfl]
  simp only [Int.toNat_one]
  simp only [show Trans.Recal.lenI (S m)-1=(m:Int)+1 from by
    unfold S
    change Trans.Recal.lenI ((0,0)::E 3 3 m)-1=_
    unfold Trans.Recal.lenI
    rw [List.length_cons,length_E]
    omega]
  rw [show (S m).drop 1=E 3 3 m from rfl,isPrincipalP_E]
  rw [show decide ((1:Int)≤(m:Int)+1)=true from decide_eq_true (by omega)]
  simp only [Bool.true_and,if_true]
  rw [show Trans.Recal.gp0 (S m) 1=3 from rfl,
    show Trans.Recal.gp1 (S m) 1=1 from rfl]
  simpa using incrFirst_E_neg 3 3 2 m (by omega)

theorem red_L (m : Nat) : Trans.Recal.red 2 (L m)=L m := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (L m)=false from by
      unfold Trans.Recal.isZeroP
      rw [length_L]
      simp,isPrincipalP_L]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (L m) 0==0 && Trans.Recal.gp1 (L m) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_L,lenI_L]
  rw [show ((1:Int)==(m:Int)+3-1)=false from beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true,if_false]
  rw [brF_L,firstNodes_L,joints_L]
  simp only [List.length_cons,List.length_nil]
  rw [show List.range 1=[0] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([R m]:List Trans.Recal.PS).getD 0 []=R m from rfl,
    show ([2,((m+3:Nat):Int)]:List Int).getD 0 0=2 from rfl,
    show ([1]:List Int).getD 0 0=1 from rfl]
  rw [show Trans.Recal.gp1 (R m) 0=1 from rfl]
  simp only [show ((1:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [fpar1_L_two]
  change Trans.Recal.jjSeq 0 1++
    Trans.Recal.incrFirst (Trans.Recal.red 1 (((2:Int),(1:Int))::Trans.Recal.derp (R m))) 1=L m
  rw [show (((2:Int),(1:Int))::Trans.Recal.derp (R m))=R m from by
    unfold R Trans.Recal.derp
    rfl,red_R]
  rw [show Trans.Recal.incrFirst (E 1 3 m) 1=R m from by
    simpa using incrFirst_E 1 3 1 m]
  rfl

/-! ### Reader steps and right-spine replacement. -/

theorem q_add_three (a : Nat) : q (a+3)=q a := by
  unfold q
  rw [show (a+3)%3=a%3 by omega]

theorem q_add_three_left (a : Nat) : q (3+a)=q a := by
  rw [Nat.add_comm,q_add_three]

theorem q_no_two_rises (k : Nat) :
    (!(decide (q k<q (k+1)) && decide (q (k+1)<q (k+2))))=true := by
  have hk : k%3=0 ∨ k%3=1 ∨ k%3=2 := by omega
  rcases hk with h0|h1|h2
  · have h1' : (k+1)%3=1 := by omega
    have h2' : (k+2)%3=2 := by omega
    simp [q,h0,h1',h2']
  · have h1' : (k+1)%3=2 := by omega
    have h2' : (k+2)%3=0 := by omega
    simp [q,h1,h1',h2']
  · have h1' : (k+1)%3=0 := by omega
    have h2' : (k+2)%3=1 := by omega
    simp [q,h2,h1',h2']

theorem gp1_L_tail (m k : Nat) (hk0 : 3≤k) (hk : k<m+3) :
    Trans.Recal.gp1 (L m) (k:Int)=q k := by
  obtain ⟨j,rfl⟩ : ∃ j,k=j+3 := ⟨k-3,by omega⟩
  show (if ((j+3:Nat):Int)<0 then 0 else ((L m).getD (j+3) (0,0)).2)=_
  rw [if_neg (by omega)]
  change ((A 3 3 m).getD j (0,0)).2=q (j+3)
  rw [getD_A 3 3 m j (by omega)]
  rw [q_add_three_left,q_add_three]

theorem fpar0_L_adj (m k : Nat) (hk0 : 0<k) (hk : k<m+3) :
    Trans.Recal.fpar0 (L m) (k:Int) ((k-1:Nat):Int)=((k-1:Nat):Int) := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L,gp0_L m k hk]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_neg (by omega),show ((k:Nat):Int)-1=((k-1:Nat):Int) by omega,
    gp0_L m (k-1) (by omega),if_pos (by omega)]

theorem fpar0_L_self (m k : Nat) (hk : k<m+3) :
    Trans.Recal.fpar0 (L m) (k:Int) (k:Int)=-1 := by
  unfold Trans.Recal.fpar0
  rw [if_neg (by rw [lenI_L]; omega),length_L,gp0_L m k hk]
  simp only [Trans.Recal.fpar0Aux]
  rw [if_pos (by omega)]

theorem fpar1_L_adj (m k : Nat) (hk0 : 0<k) (hk : k<m+3) :
    Trans.Recal.fpar (L m) 1 (k:Int) ((k-1:Nat):Int)=
      if Trans.Recal.gp1 (L m) ((k-1:Nat):Int)<Trans.Recal.gp1 (L m) (k:Int)
      then ((k-1:Nat):Int) else -1 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_L]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_L]
  simp only [Trans.Recal.fpar1Aux]
  rw [fpar0_L_adj m k hk0 hk,if_neg (by omega)]
  by_cases hlt : Trans.Recal.gp1 (L m) ((k-1:Nat):Int)<
      Trans.Recal.gp1 (L m) (k:Int)
  · simp only [if_pos hlt]
  · simp only [if_neg hlt]
    rw [fpar0_L_self m (k-1) (by omega),if_pos (by omega)]

theorem isParent1_L_adj_false (m k : Nat) (hk0 : 0<k) (hk : k<m+3)
    (hlt : ¬ Trans.Recal.gp1 (L m) ((k-1:Nat):Int)<
      Trans.Recal.gp1 (L m) (k:Int)) :
    Trans.Recal.isParentP (L m) 1 (k:Int) ((k-1:Nat):Int)=false := by
  unfold Trans.Recal.isParentP
  rw [fpar1_L_adj m k hk0 hk,lenI_L]
  rw [show decide (0≤((k-1:Nat):Int))=true from decide_eq_true (by omega),
    show decide (((k-1:Nat):Int)<(m:Int)+3)=true from decide_eq_true (by omega)]
  simp only [Bool.true_and]
  rw [if_neg hlt,show (((k-1:Nat):Int)==(-1:Int))=false from
    beq_eq_false_iff_ne.mpr (by omega)]

theorem isAdm_L_parent (k : Nat) :
    Trans.Recal.isAdm (L (k+1)) ((k+2:Nat):Int)=true := by
  unfold Trans.Recal.isAdm Trans.Recal.isUnadmitted
  rw [show decide (((k+2:Nat):Int)>Trans.Recal.lenI (L (k+1)))=false from
    decide_eq_false (by rw [lenI_L]; push_cast; omega)]
  simp only [Bool.false_or]
  cases k with
  | zero => rfl
  | succ k =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [show k+1+1+1=k+3 by omega,
        show k+1+1+2=k+4 by omega,
        show (((k+4:Nat):Int)-1)=((k+3:Nat):Int) by omega,
        show (((k+4:Nat):Int)+1)=((k+5:Nat):Int) by omega]
      change (!(Trans.Recal.isParentP (L (k+3)) 1 ((k+4:Nat):Int) ((k+3:Nat):Int) &&
        Trans.Recal.isParentP (L (k+3)) 1 ((k+5:Nat):Int) ((k+4:Nat):Int)))=true
      by_cases hfirst : Trans.Recal.gp1 (L (k+3)) ((k+3:Nat):Int)<
          Trans.Recal.gp1 (L (k+3)) ((k+4:Nat):Int)
      · have hfirstq : q k<q (k+1) := by
          simpa only [
            gp1_L_tail (k+3) (k+3) (by omega) (by omega),
            gp1_L_tail (k+3) (k+4) (by omega) (by omega),
            show q (k+3)=q k from q_add_three k,
            show q (k+4)=q (k+1) from by
              rw [show k+4=(k+1)+3 by omega,q_add_three]] using hfirst
        have hsecond : ¬ Trans.Recal.gp1 (L (k+3)) ((k+4:Nat):Int)<
            Trans.Recal.gp1 (L (k+3)) ((k+5:Nat):Int) := by
          intro hsecond
          have hsecondq : q (k+1)<q (k+2) := by
            simpa only [
              gp1_L_tail (k+3) (k+4) (by omega) (by omega),
              gp1_L_tail (k+3) (k+5) (by omega) (by omega),
              show q (k+4)=q (k+1) from by
                rw [show k+4=(k+1)+3 by omega,q_add_three],
              show q (k+5)=q (k+2) from by
                rw [show k+5=(k+2)+3 by omega,q_add_three]] using hsecond
          have hn := q_no_two_rises k
          rw [show decide (q k<q (k+1))=true from decide_eq_true hfirstq,
            show decide (q (k+1)<q (k+2))=true from
              decide_eq_true hsecondq] at hn
          contradiction
        have hp2 : Trans.Recal.isParentP (L (k+3)) 1 ((k+5:Nat):Int)
            ((k+4:Nat):Int)=false := by
          simpa using isParent1_L_adj_false (k+3) (k+5) (by omega)
            (by omega) hsecond
        rw [hp2,Bool.and_false]
        rfl
      · have hp1 : Trans.Recal.isParentP (L (k+3)) 1 ((k+4:Nat):Int)
            ((k+3:Nat):Int)=false := by
          simpa using isParent1_L_adj_false (k+3) (k+4) (by omega)
            (by omega) hfirst
        rw [hp1,Bool.false_and]
        rfl

theorem adm_L_parent (k : Nat) :
    Trans.Recal.adm (L (k+1)) ((k+2:Nat):Int)=((k+2:Nat):Int) := by
  unfold Trans.Recal.adm
  rw [length_L]
  simp only [Trans.Recal.admAux]
  rw [if_neg (by omega),isAdm_L_parent,if_pos rfl]

def High : Nat → Trans.Dict.BT
  | 0 => .D 1 .zero
  | k+1 => .D (q k).toNat .zero

def StepC2 (k : Nat) : Trans.Dict.BT :=
  match High k with
  | .D u _ => .D u (.D (q k).toNat .zero)
  | _ => .zero

theorem gp1_L_top (k : Nat) :
    Trans.Recal.gp1 (L (k+1)) ((k+3:Nat):Int)=q k := by
  rw [gp1_L_tail (k+1) (k+3) (by omega) (by omega)]
  exact q_add_three k

theorem gp1_L_parent (k : Nat) :
    Trans.Recal.gp1 (L (k+1)) ((k+2:Nat):Int)=
      match k with | 0 => 1 | j+1 => q j := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [gp1_L_tail (k+2) (k+3) (by omega) (by omega)]
    exact q_add_three k

theorem transType_L (k : Nat) :
    Trans.Recal.transTypeMain (L (k+1)) ((k+2:Nat):Int) ((k+3:Nat):Int)=
      if q k=0 then 1 else if k%3=1 then 6 else 3 := by
  unfold Trans.Recal.transTypeMain
  rw [gp1_L_top]
  by_cases hz:q k=0
  · rw [hz]
    simp only [show ((0:Int)==0)=true from rfl,if_true]
    rw [isAdm_L_parent,if_pos rfl]
  · rw [show (q k==0)=false from beq_eq_false_iff_ne.mpr hz]
    simp only [Bool.false_eq_true,if_false]
    rw [gp1_L_parent]
    cases k with
    | zero => exact absurd rfl hz
    | succ k =>
      by_cases h0:(k+1)%3=0
      · exact absurd (by simp [q,h0]) hz
      · by_cases h1:(k+1)%3=1
        · have hk:k%3=0:=by omega
          simp [q,h0,h1,hk]
          omega
        · have h2:(k+1)%3=2:=by omega
          have hk:k%3=1:=by omega
          simp [q,h0,h1,h2,hk]
          simpa only [show ((k+1+2:Nat):Int)=((k+3:Nat):Int) by omega] using
            isAdm_L_parent (k+1)

theorem mkC2_L (k : Nat) :
    Trans.Recal.mkC2 (L (k+1)) ((k+2:Nat):Int) ((k+3:Nat):Int)
      (Trans.Recal.transTypeMain (L (k+1)) ((k+2:Nat):Int) ((k+3:Nat):Int))
      (High k)=StepC2 k := by
  cases k with
  | zero => rfl
  | succ k =>
    rw [show High (k+1)=.D (q k).toNat .zero from rfl,
      show StepC2 (k+1)=.D (q k).toNat (.D (q (k+1)).toNat .zero) from rfl]
    by_cases h0:(k+1)%3=0
    · have hq : q (k+1)=0 := by simp [q,h0]
      rw [transType_L,hq,if_pos rfl]
      unfold Trans.Recal.mkC2
      rw [show Trans.Recal.gp1 (L (k+2)) ((k+1+3:Nat):Int)=q (k+1)
        from gp1_L_top (k+1),hq]
      rfl
    · by_cases h1:(k+1)%3=1
      · have hq : q (k+1)=1 := by simp [q,h0]
        rw [transType_L,hq,if_neg (by omega),if_pos h1]
        unfold Trans.Recal.mkC2
        rw [show Trans.Recal.gp1 (L (k+2)) ((k+1+3:Nat):Int)=q (k+1)
          from gp1_L_top (k+1),hq]
        rfl
      · have hq : q (k+1)=1 := by simp [q,h0]
        rw [transType_L,hq,if_neg (by omega),if_neg h1]
        unfold Trans.Recal.mkC2
        rw [show Trans.Recal.gp1 (L (k+2)) ((k+1+3:Nat):Int)=q (k+1)
          from gp1_L_top (k+1),hq]
        rfl

theorem P_ne_zero (a m : Nat) : P a (m+1)≠.zero := by
  intro h
  cases h

theorem beq_D_D_zero (u v w : Nat) (b : Trans.Dict.BT) :
    ((Trans.Dict.BT.D u (.D w b)) == (.D v .zero))=false := by
  unfold BEq.beq Trans.Dict.instBEqBT Trans.Dict.instBEqBT.beq
  simp
  intro _
  rfl

theorem size_P : ∀ a m, (P a m).size=m+1
  | _, 0 => rfl
  | a, m+1 => by simp only [P,Trans.Dict.BT.size,size_P]; omega

theorem size_LBT (m : Nat) : (LBT m).size=m+4 := by
  simp only [LBT,Trans.Dict.BT.size,size_P]
  omega

theorem P_last (a m : Nat) :
    P a (m+1)=.D (q a).toNat (P (a+1) m) := rfl

theorem repl_P : ∀ (a k f : Nat), k+2≤f →
    Trans.Recal.replMark f (P a (k+1))
      (.D (q (a+k)).toNat .zero)
      (.D (q (a+k)).toNat (.D (q (a+k+1)).toNat .zero))=
      some (P a (k+2))
  | a, 0, f, hf => by
    cases f with
    | zero => omega
    | succ f =>
      change Trans.Recal.replMark (f+1) (.D (q a).toNat .zero)
        (.D (q a).toNat .zero)
        (.D (q a).toNat (.D (q (a+1)).toNat .zero))=
        some (.D (q a).toNat (.D (q (a+1)).toNat .zero))
      rw [G1.replMark_self (f+1) (q a).toNat .zero
        (.D (q a).toNat (.D (q (a+1)).toNat .zero)) (by omega)]
  | a, k+1, f, hf => by
    cases f with
    | zero => omega
    | succ f =>
      change Trans.Recal.replMark (f+1)
        (.D (q a).toNat (P (a+1) (k+1)))
        (.D (q (a+(k+1))).toNat .zero)
        (.D (q (a+(k+1))).toNat (.D (q (a+(k+1)+1)).toNat .zero))=
        some (.D (q a).toNat (P (a+1) (k+2)))
      rw [Trans.Recal.replMark]
      rw [show ((Trans.Dict.BT.D (q a).toNat (P (a+1) (k+1)))==
          (.D (q (a+(k+1))).toNat .zero))=false from by
            simpa only [P] using
              beq_D_D_zero (q a).toNat (q (a+(k+1))).toNat
                (q (a+1)).toNat (P (a+2) k)]
      simp only [Bool.false_eq_true,if_false]
      have hr : Trans.Recal.replMark f (P (a+1) (k+1))
          (.D (q (a+(k+1))).toNat .zero)
          (.D (q (a+(k+1))).toNat (.D (q (a+(k+1)+1)).toNat .zero))=
          some (P (a+1) (k+2)) := by
        simpa only [show a+(k+1)=a+1+k by omega,
          show a+(k+1)+1=a+1+k+1 by omega] using
          repl_P (a+1) k f (by omega)
      rw [hr]
      rfl

theorem repl_LBT (f k : Nat) (hf : k+4≤f) :
    Trans.Recal.replMark f (LBT k) (High k) (StepC2 k)=some (LBT (k+1)) := by
  obtain ⟨g,rfl⟩ : ∃ g,f=g+4 := ⟨f-4,by omega⟩
  cases k with
  | zero => rfl
  | succ k =>
    change Trans.Recal.replMark (g+4)
      (.D 0 (.D 1 (.D 1 (P 3 (k+1)))))
      (.D (q k).toNat .zero)
      (.D (q k).toNat (.D (q (k+1)).toNat .zero))=
      some (.D 0 (.D 1 (.D 1 (P 3 (k+2)))))
    rw [show g+4=(g+3)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 0 (.D 1 (.D 1 (P 3 (k+1)))))==
        (.D (q k).toNat .zero))=false from beq_D_D_zero 0 (q k).toNat 1 _]
    simp only [Bool.false_eq_true,if_false]
    rw [show g+3=(g+2)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 1 (.D 1 (P 3 (k+1))))==
        (.D (q k).toNat .zero))=false from beq_D_D_zero 1 (q k).toNat 1 _]
    simp only [Bool.false_eq_true,if_false]
    rw [show g+2=(g+1)+1 by omega,Trans.Recal.replMark]
    rw [show ((Trans.Dict.BT.D 1 (P 3 (k+1)))==
        (.D (q k).toNat .zero))=false from by
          simpa only [P] using beq_D_D_zero 1 (q k).toNat (q 3).toNat (P 4 k)]
    simp only [Bool.false_eq_true,if_false]
    have hr : Trans.Recal.replMark (g+1) (P 3 (k+1))
        (.D (q k).toNat .zero)
        (.D (q k).toNat (.D (q (k+1)).toNat .zero))=
        some (P 3 (k+2)) := by
      simpa only [q_add_three_left,
        show 3+k+1=3+(k+1) by omega] using repl_P 3 k (g+1) (by omega)
    rw [hr]
    rfl

/-! ### Fuel-independent reduction of the periodic ladder. -/

/-- A row-zero gap followed by a consecutive periodic tail. -/
def K7 (d a p m : Nat) : Trans.Recal.PS :=
  ((((d:Nat):Int)),q p)::A a (p+1) m

/-- The same gap below the zero root. -/
def C7 (d a p m : Nat) : Trans.Recal.PS := (0,0)::K7 d a p m

def K7Red (p m : Nat) : Trans.Recal.PS := A (q p).toNat p (m+1)
def C7Red (p m : Nat) : Trans.Recal.PS := (0,0)::A 1 p (m+1)

theorem length_K7 (d a p m : Nat) : (K7 d a p m).length=m+1 := by
  simp [K7,length_A]

theorem length_C7 (d a p m : Nat) : (C7 d a p m).length=m+2 := by
  simp [C7,length_K7]

theorem lenI_K7 (d a p m : Nat) :
    Trans.Recal.lenI (K7 d a p m)=(m:Int)+1 := by
  unfold Trans.Recal.lenI
  rw [length_K7]
  omega

theorem lenI_C7 (d a p m : Nat) :
    Trans.Recal.lenI (C7 d a p m)=(m:Int)+2 := by
  unfold Trans.Recal.lenI
  rw [length_C7]
  omega

theorem gp0_K7_zero (d a p m : Nat) :
    Trans.Recal.gp0 (K7 d a p m) 0=(d:Int) := rfl

theorem gp1_K7_zero (d a p m : Nat) :
    Trans.Recal.gp1 (K7 d a p m) 0=q p := rfl

theorem gp0_K7_tail (d a p m k : Nat) (hk : k<m) :
    Trans.Recal.gp0 (K7 d a p m) ((k+1:Nat):Int)=((a+k:Nat):Int) := by
  show (if ((k+1:Nat):Int)<0 then 0 else
    ((K7 d a p m).getD (k+1) (0,0)).1)=_
  rw [if_neg (by omega)]
  change ((A a (p+1) m).getD k (0,0)).1=_
  rw [getD_A a (p+1) m k hk]

theorem gp1_K7_tail (d a p m k : Nat) (hk : k<m) :
    Trans.Recal.gp1 (K7 d a p m) ((k+1:Nat):Int)=q (p+1+k) := by
  show (if ((k+1:Nat):Int)<0 then 0 else
    ((K7 d a p m).getD (k+1) (0,0)).2)=_
  rw [if_neg (by omega)]
  change ((A a (p+1) m).getD k (0,0)).2=_
  rw [getD_A a (p+1) m k hk]

theorem fpar_K7 (d a p m k : Nat) (hda : d<a) (hk0 : 0<k)
    (hk : k<m+1) :
    Trans.Recal.fpar (K7 d a p m) 0 (k:Int) 0=((k-1:Nat):Int) := by
  obtain ⟨j,rfl⟩ : ∃ j,k=j+1 := ⟨k-1,by omega⟩
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_K7]; omega),if_pos (by rfl),length_K7]
  cases j with
  | zero =>
    change Trans.Recal.fpar0Aux (m+2) (K7 d a p m)
      (Trans.Recal.gp0 (K7 d a p m) 1) 0 0=0
    rw [show Trans.Recal.gp0 (K7 d a p m) 1=(a:Int) from by
      simpa using gp0_K7_tail d a p m 0 (by omega)]
    simp only [Trans.Recal.fpar0Aux]
    rw [if_neg (by omega),gp0_K7_zero,if_pos (by push_cast; omega)]
  | succ j =>
    rw [show j+1+1=j+2 by omega,
      show ((j+2:Nat):Int)-1=((j+1:Nat):Int) by omega,
      show j+2-1=j+1 by omega]
    change Trans.Recal.fpar0Aux (m+2) (K7 d a p m)
      (Trans.Recal.gp0 (K7 d a p m) ((j+2:Nat):Int))
      ((j+1:Nat):Int) 0=((j+1:Nat):Int)
    rw [gp0_K7_tail d a p m (j+1) (by omega)]
    simp only [Trans.Recal.fpar0Aux]
    rw [if_neg (by omega),gp0_K7_tail d a p m j (by omega),
      if_pos (by push_cast; omega)]

theorem fpar_C7 (d a p m k : Nat) (hd : 0<d) (hda : d<a)
    (hk0 : 0<k) (hk : k<m+2) :
    Trans.Recal.fpar (C7 d a p m) 0 (k:Int) 0=((k-1:Nat):Int) := by
  obtain ⟨j,rfl⟩ : ∃ j,k=j+1 := ⟨k-1,by omega⟩
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C7]; omega),if_pos (by rfl),length_C7]
  cases j with
  | zero =>
    change Trans.Recal.fpar0Aux (m+3) (C7 d a p m)
      (Trans.Recal.gp0 (C7 d a p m) 1) 0 0=0
    rw [show Trans.Recal.gp0 (C7 d a p m) 1=(d:Int) from rfl]
    simp only [Trans.Recal.fpar0Aux]
    rw [if_neg (by omega),show Trans.Recal.gp0 (C7 d a p m) 0=0 from rfl,
      if_pos (by push_cast; omega)]
  | succ j =>
    cases j with
    | zero =>
      change Trans.Recal.fpar0Aux (m+3) (C7 d a p m)
        (Trans.Recal.gp0 (C7 d a p m) 2) 1 0=1
      rw [show Trans.Recal.gp0 (C7 d a p m) 2=(a:Int) from by
        simpa using gp0_K7_tail d a p m 0 (by omega)]
      simp only [Trans.Recal.fpar0Aux]
      rw [if_neg (by omega),show Trans.Recal.gp0 (C7 d a p m) 1=(d:Int) from rfl,
        if_pos (by push_cast; omega)]
    | succ j =>
      rw [show j+1+1+1=j+3 by omega,
        show ((j+3:Nat):Int)-1=((j+2:Nat):Int) by omega,
        show j+3-1=j+2 by omega]
      change Trans.Recal.fpar0Aux (m+3) (C7 d a p m)
        (Trans.Recal.gp0 (C7 d a p m) ((j+3:Nat):Int))
        ((j+2:Nat):Int) 0=((j+2:Nat):Int)
      rw [show Trans.Recal.gp0 (C7 d a p m) ((j+3:Nat):Int)=
          ((a+j+1:Nat):Int) from by
        simpa using gp0_K7_tail d a p m (j+1) (by omega)]
      simp only [Trans.Recal.fpar0Aux]
      rw [if_neg (by omega),
        show Trans.Recal.gp0 (C7 d a p m) ((j+2:Nat):Int)=
          ((a+j:Nat):Int) from by
            simpa using gp0_K7_tail d a p m j (by omega),
        if_pos (by push_cast; omega)]

theorem isAncAux_K7 (d a p m k : Nat) (hda : d<a) : ∀ f : Nat,
    k<m+1 → k<f →
    Trans.Recal.isAncAux f (K7 d a p m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ f : Nat,k<m+1 → k<f →
    Trans.Recal.isAncAux f (K7 d a p m) 0 (k:Int) 0=true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0:k=0
    · subst k
      rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      rw [fpar_K7 d a p m k hda (by omega) hkm]
      rw [show (((k-1:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isAncAux_C7 (d a p m k : Nat) (hd : 0<d) (hda : d<a) : ∀ f : Nat,
    k<m+2 → k<f →
    Trans.Recal.isAncAux f (C7 d a p m) 0 (k:Int) 0=true := by
  refine Nat.strongRecOn (motive:=fun k => ∀ f : Nat,k<m+2 → k<f →
    Trans.Recal.isAncAux f (C7 d a p m) 0 (k:Int) 0=true) k ?_
  intro k ih f hkm hkf
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.isAncAux]
    by_cases hk0:k=0
    · subst k
      rw [if_pos (by rfl)]
    · rw [show ((0:Int)==(k:Int))=false from beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      rw [fpar_C7 d a p m k hd hda (by omega) hkm]
      rw [show (((k-1:Nat):Int)==(-1:Int))=false from
        beq_eq_false_iff_ne.mpr (by omega)]
      simp only [Bool.false_eq_true,if_false]
      exact ih (k-1) (by omega) f (by omega) (by omega)

theorem isPrincipalP_K7 (d a p m : Nat) (hda : d<a)
    (hnz : q p≠0 ∨ 0<m) :
    Trans.Recal.isPrincipalP (K7 d a p m)=true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (K7 d a p m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_K7]
    cases m with
    | zero =>
      change (q p==0)=false
      exact beq_eq_false_iff_ne.mpr (hnz.resolve_right (by omega))
    | succ m => simp]
  simp only [Bool.not_false,Bool.true_and]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_K7]; omega),length_K7,lenI_K7,
    show (m:Int)+1-1=(m:Int) by omega]
  exact isAncAux_K7 d a p m m hda (m+2) (by omega) (by omega)

theorem isPrincipalP_C7 (d a p m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.isPrincipalP (C7 d a p m)=true := by
  unfold Trans.Recal.isPrincipalP
  rw [show Trans.Recal.isZeroP (C7 d a p m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_C7]
    simp]
  simp only [Bool.not_false,Bool.true_and]
  unfold Trans.Recal.isAnc
  rw [if_neg (by rw [lenI_C7]; omega),length_C7,lenI_C7,
    show (m:Int)+2-1=((m+1:Nat):Int) by omega]
  exact isAncAux_C7 d a p m (m+1) hd hda (m+3) (by omega) (by omega)

theorem fAncAux_K7_last (d a p m k : Nat) : ∀ (f : Nat) (acc : List Int),
    d<a → k<m+1 → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (K7 d a p m) 0 (k:Int) 0 acc).getLast?=some 0 := by
  refine Nat.strongRecOn (motive:=fun k => ∀ (f : Nat) (acc : List Int),
    d<a → k<m+1 → k<f → acc.getLast?=some (k:Int) →
    (Trans.Recal.fAncAux f (K7 d a p m) 0 (k:Int) 0 acc).getLast?=some 0) k ?_
  intro k ih f acc hda hkm hkf hlast
  cases f with
  | zero => omega
  | succ f =>
    simp only [Trans.Recal.fAncAux]
    by_cases hk0:k=0
    · subst k
      rw [show ((0:Nat):Int)=0 from rfl]
      have hp : Trans.Recal.fpar (K7 d a p m) 0 0 0=-1 := by
        unfold Trans.Recal.fpar
        rw [if_neg (by rw [lenI_K7]; omega),if_pos (by rfl),length_K7]
        simp only [Trans.Recal.fpar0Aux]
        rw [if_pos (by omega)]
      rw [hp,if_neg (by omega)]
      exact hlast
    · rw [fpar_K7 d a p m k hda (by omega) hkm,if_pos (by omega)]
      exact ih (k-1) (by omega) f (acc++[((k-1:Nat):Int)]) hda
        (by omega) (by omega) (by simp)

theorem fAnc_K7_last (d a p m : Nat) (hda : d<a) :
    (Trans.Recal.fAnc (K7 d a p m) 0 (m:Int) 0).getLast?=some 0 := by
  unfold Trans.Recal.fAnc
  rw [if_neg (by rw [lenI_K7]; omega),length_K7]
  exact fAncAux_K7_last d a p m m (m+2) [(m:Int)] hda
    (by omega) (by omega) (by simp)

theorem slice_K7_full (d a p m : Nat) :
    Trans.Recal.slice (K7 d a p m) 0 ((m+1:Nat):Int)=K7 d a p m := by
  unfold Trans.Recal.slice
  simp only [Int.toNat_zero,List.drop_zero]
  rw [show (((m+1:Nat):Int)-0).toNat=m+1 by omega]
  simpa only [length_K7] using (List.take_length (l:=K7 d a p m))

theorem ppair_K7 (d a p m : Nat) (hda : d<a) :
    Trans.Recal.ppair (K7 d a p m)=[K7 d a p m] := by
  unfold Trans.Recal.ppair
  rw [length_K7,lenI_K7,Trans.Recal.ppairAux]
  dsimp only
  rw [show (m:Int)+1-1=(m:Int) by omega,if_neg (by omega),
    fAnc_K7_last d a p m hda]
  simp only [Option.getD_some]
  rw [show (0:Int)-1=-1 by omega,Trans.Recal.ppairAux,if_pos (by omega),
    show (m:Int)+1=((m+1:Nat):Int) by omega,slice_K7_full]

theorem A_phase_add_three (a p m : Nat) : A a (p+3) m=A a p m := by
  unfold A
  apply List.map_congr_left
  intro k _
  apply Prod.ext
  · rfl
  · rw [show p+3+k=(p+k)+3 by omega,q_add_three]

theorem K7_phase_add_three (d a p m : Nat) :
    K7 d a (p+3) m=K7 d a p m := by
  unfold K7
  rw [q_add_three]
  rw [show p+3+1=(p+1)+3 by omega,A_phase_add_three]

theorem C7_phase_add_three (d a p m : Nat) :
    C7 d a (p+3) m=C7 d a p m := by
  unfold C7
  rw [K7_phase_add_three]

theorem K7Red_phase_add_three (p m : Nat) :
    K7Red (p+3) m=K7Red p m := by
  unfold K7Red
  rw [q_add_three,A_phase_add_three]

theorem C7Red_phase_add_three (p m : Nat) :
    C7Red (p+3) m=C7Red p m := by
  unfold C7Red
  rw [A_phase_add_three]

theorem fpar1_C7_one (d a p m : Nat) (hd : 0<d) (hda : d<a)
    (hp : q p=1) :
    Trans.Recal.fpar (C7 d a p m) 1 1 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C7]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_C7]
  rw [show Trans.Recal.gp1 (C7 d a p m) 1=q p from rfl]
  change Trans.Recal.fpar1Aux (m+3) (C7 d a p m) (q p) 1 0=0
  rw [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (C7 d a p m) 1 0=0 from by
    rw [G6.fpar0_eq_fpar_row0 _ _ _ (by rw [lenI_C7]; omega)]
    simpa using fpar_C7 d a p m 1 hd hda (by omega) (by omega)]
  rw [if_neg (by omega),show Trans.Recal.gp1 (C7 d a p m) 0=0 from rfl,hp,
    if_pos (by omega)]

theorem fpar1_C7_one_phase1 (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.fpar (C7 d a 1 m) 1 1 0=0 :=
  fpar1_C7_one d a 1 m hd hda (by rfl)

theorem fpar1_C7_one_phase2 (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.fpar (C7 d a 2 m) 1 1 0=0 :=
  fpar1_C7_one d a 2 m hd hda (by rfl)

theorem fpar1_C7_two_lb_phase1 (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.fpar (C7 d a 1 m) 1 2 1=-1 := by
  cases m with
  | zero =>
    unfold Trans.Recal.fpar
    rw [if_pos (by rw [lenI_C7]; omega)]
  | succ m =>
    unfold Trans.Recal.fpar
    rw [if_neg (by rw [lenI_C7]; omega)]
    simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
    rw [length_C7]
    rw [show Trans.Recal.gp1 (C7 d a 1 (m+1)) 2=1 from by
      simpa [q] using gp1_K7_tail d a 1 (m+1) 0 (by omega)]
    change Trans.Recal.fpar1Aux (m+4) (C7 d a 1 (m+1)) 1 2 1=-1
    rw [show m+4=(m+3)+1 by omega]
    rw [Trans.Recal.fpar1Aux]
    rw [show Trans.Recal.fpar0 (C7 d a 1 (m+1)) 2 1=1 from by
      unfold Trans.Recal.fpar0
      rw [if_neg (by rw [lenI_C7]; omega),length_C7]
      change Trans.Recal.fpar0Aux (m+4) (C7 d a 1 (m+1))
        (Trans.Recal.gp0 (C7 d a 1 (m+1)) 2) 1 1=1
      rw [show Trans.Recal.gp0 (C7 d a 1 (m+1)) 2=(a:Int) from by
        simpa using gp0_K7_tail d a 1 (m+1) 0 (by omega)]
      simp only [Trans.Recal.fpar0Aux]
      rw [if_neg (by omega),show Trans.Recal.gp0 (C7 d a 1 (m+1)) 1=(d:Int) from rfl,
        if_pos (by push_cast; omega)],if_neg (by omega)]
    rw [show Trans.Recal.gp1 (C7 d a 1 (m+1)) 1=1 from by rfl,if_neg (by omega)]
    rw [show m+3=(m+2)+1 by omega]
    rw [Trans.Recal.fpar1Aux]
    rw [show Trans.Recal.fpar0 (C7 d a 1 (m+1)) 1 1=-1 from by
      unfold Trans.Recal.fpar0
      rw [if_neg (by rw [lenI_C7]; omega),length_C7]
      simp only [Trans.Recal.fpar0Aux]
      rw [if_pos (by omega)],if_pos (by omega)]

theorem fpar1_C7_two_lb_phase2 (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.fpar (C7 d a 2 m) 1 2 1=-1 := by
  cases m with
  | zero =>
    unfold Trans.Recal.fpar
    rw [if_pos (by rw [lenI_C7]; omega)]
  | succ m =>
    unfold Trans.Recal.fpar
    rw [if_neg (by rw [lenI_C7]; omega)]
    simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
    rw [length_C7]
    rw [show Trans.Recal.gp1 (C7 d a 2 (m+1)) 2=0 from by
      simpa [q] using gp1_K7_tail d a 2 (m+1) 0 (by omega)]
    change Trans.Recal.fpar1Aux (m+4) (C7 d a 2 (m+1)) 0 2 1=-1
    rw [show m+4=(m+3)+1 by omega]
    rw [Trans.Recal.fpar1Aux]
    rw [show Trans.Recal.fpar0 (C7 d a 2 (m+1)) 2 1=1 from by
      unfold Trans.Recal.fpar0
      rw [if_neg (by rw [lenI_C7]; omega),length_C7]
      change Trans.Recal.fpar0Aux (m+4) (C7 d a 2 (m+1))
        (Trans.Recal.gp0 (C7 d a 2 (m+1)) 2) 1 1=1
      rw [show Trans.Recal.gp0 (C7 d a 2 (m+1)) 2=(a:Int) from by
        simpa using gp0_K7_tail d a 2 (m+1) 0 (by omega)]
      simp only [Trans.Recal.fpar0Aux]
      rw [if_neg (by omega),show Trans.Recal.gp0 (C7 d a 2 (m+1)) 1=(d:Int) from rfl,
        if_pos (by push_cast; omega)],if_neg (by omega)]
    rw [show Trans.Recal.gp1 (C7 d a 2 (m+1)) 1=1 from by rfl,if_neg (by omega)]
    rw [show m+3=(m+2)+1 by omega]
    rw [Trans.Recal.fpar1Aux]
    rw [show Trans.Recal.fpar0 (C7 d a 2 (m+1)) 1 1=-1 from by
      unfold Trans.Recal.fpar0
      rw [if_neg (by rw [lenI_C7]; omega),length_C7]
      simp only [Trans.Recal.fpar0Aux]
      rw [if_pos (by omega)],if_pos (by omega)]

theorem fpar1_C7_two_phase1 (d a m : Nat) (hd : 0<d) (hda : d<a)
    (hm : 0<m) :
    Trans.Recal.fpar (C7 d a 1 m) 1 2 0=0 := by
  unfold Trans.Recal.fpar
  rw [if_neg (by rw [lenI_C7]; omega)]
  simp only [show ((1:Nat)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [length_C7]
  rw [show Trans.Recal.gp1 (C7 d a 1 m) 2=1 from by
    simpa [q] using gp1_K7_tail d a 1 m 0 hm]
  change Trans.Recal.fpar1Aux (m+3) (C7 d a 1 m) 1 2 0=0
  rw [show m+3=(m+2)+1 by omega]
  rw [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (C7 d a 1 m) 2 0=1 from by
    simpa using fpar_C7 d a 1 m 2 hd hda (by omega) (by omega),if_neg (by omega)]
  rw [show Trans.Recal.gp1 (C7 d a 1 m) 1=1 from by rfl,if_neg (by omega)]
  rw [show m+2=(m+1)+1 by omega]
  rw [Trans.Recal.fpar1Aux]
  rw [show Trans.Recal.fpar0 (C7 d a 1 m) 1 0=0 from by
    simpa using fpar_C7 d a 1 m 1 hd hda (by omega) (by omega),if_neg (by omega)]
  rw [show Trans.Recal.gp1 (C7 d a 1 m) 0=0 from rfl,if_pos (by omega)]

theorem isParent1_C7_one (d a p m : Nat) (hd : 0<d) (hda : d<a)
    (hp : q p=1) :
    Trans.Recal.isParentP (C7 d a p m) 1 1 0=true := by
  unfold Trans.Recal.isParentP
  rw [fpar1_C7_one d a p m hd hda hp,lenI_C7,
    show decide ((0:Int)<(m:Int)+2)=true from decide_eq_true (by omega)]
  rfl

theorem trMax_C7_phase1 (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.trMax (C7 d a 1 m)=1 := by
  show Trans.Recal.trMaxAux ((C7 d a 1 m).length+1) (C7 d a 1 m) 0=1
  rw [length_C7]
  simp only [Trans.Recal.trMaxAux]
  rw [show (0:Int)+1=1 by omega]
  rw [if_neg (by rw [lenI_C7]; omega),
    show Trans.Recal.isParentP (C7 d a 1 m) 1 1 0=true from
      isParent1_C7_one d a 1 m hd hda (by rfl)]
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [show (1:Int)+1=2 by omega]
  rw [if_neg (by rw [lenI_C7]; omega)]
  rw [show Trans.Recal.isParentP (C7 d a 1 m) 1 2 1=false from by
    unfold Trans.Recal.isParentP
    rw [fpar1_C7_two_lb_phase1 d a m hd hda]
    simp,if_pos (by rfl)]

theorem trMax_C7_phase2 (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.trMax (C7 d a 2 m)=1 := by
  show Trans.Recal.trMaxAux ((C7 d a 2 m).length+1) (C7 d a 2 m) 0=1
  rw [length_C7]
  simp only [Trans.Recal.trMaxAux]
  rw [show (0:Int)+1=1 by omega]
  rw [if_neg (by rw [lenI_C7]; omega),
    show Trans.Recal.isParentP (C7 d a 2 m) 1 1 0=true from
      isParent1_C7_one d a 2 m hd hda (by rfl)]
  simp only [Bool.not_true,Bool.false_eq_true,if_false]
  rw [show (1:Int)+1=2 by omega]
  rw [if_neg (by rw [lenI_C7]; omega)]
  rw [show Trans.Recal.isParentP (C7 d a 2 m) 1 2 1=false from by
    unfold Trans.Recal.isParentP
    rw [fpar1_C7_two_lb_phase2 d a m hd hda]
    simp,if_pos (by rfl)]

theorem brF_C7_phase1_succ (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.brF (C7 d a 1 (m+1))=[K7 a (a+1) 2 m] := by
  unfold Trans.Recal.brF
  rw [trMax_C7_phase1 d a (m+1) hd hda]
  show Trans.Recal.ppair (A a 2 (m+1))=[K7 a (a+1) 2 m]
  rw [A_succ]
  exact ppair_K7 a (a+1) 2 m (by omega)

theorem brF_C7_phase2_succ (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.brF (C7 d a 2 (m+1))=[K7 a (a+1) 3 m] := by
  unfold Trans.Recal.brF
  rw [trMax_C7_phase2 d a (m+1) hd hda]
  show Trans.Recal.ppair (A a 3 (m+1))=[K7 a (a+1) 3 m]
  rw [A_succ]
  exact ppair_K7 a (a+1) 3 m (by omega)

theorem firstNodes_C7_phase1_succ (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.firstNodes (C7 d a 1 (m+1))=[2,((m+3:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_C7_phase1_succ d a m hd hda,
    trMax_C7_phase1 d a (m+1) hd hda]
  simp [length_K7]
  omega

theorem firstNodes_C7_phase2_succ (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.firstNodes (C7 d a 2 (m+1))=[2,((m+3:Nat):Int)] := by
  unfold Trans.Recal.firstNodes Trans.Recal.idxSum
  rw [brF_C7_phase2_succ d a m hd hda,
    trMax_C7_phase2 d a (m+1) hd hda]
  simp [length_K7]
  omega

theorem joints_C7_phase1_succ (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.joints (C7 d a 1 (m+1))=[1] := by
  unfold Trans.Recal.joints
  rw [firstNodes_C7_phase1_succ d a m hd hda]
  change [Trans.Recal.fpar (C7 d a 1 (m+1)) 0 2 0]=[1]
  rw [show Trans.Recal.fpar (C7 d a 1 (m+1)) 0 2 0=1 from by
    simpa using fpar_C7 d a 1 (m+1) 2 hd hda (by omega) (by omega)]

theorem joints_C7_phase2_succ (d a m : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.joints (C7 d a 2 (m+1))=[1] := by
  unfold Trans.Recal.joints
  rw [firstNodes_C7_phase2_succ d a m hd hda]
  change [Trans.Recal.fpar (C7 d a 2 (m+1)) 0 2 0]=[1]
  rw [show Trans.Recal.fpar (C7 d a 2 (m+1)) 0 2 0=1 from by
    simpa using fpar_C7 d a 2 (m+1) 2 hd hda (by omega) (by omega)]

theorem incrFirst_K7 (d a p m r : Nat) :
    Trans.Recal.incrFirst (K7 d a p m) (r:Int)=K7 (d+r) (a+r) p m := by
  unfold K7 Trans.Recal.incrFirst
  rw [List.map_cons]
  change (((d:Int)+(r:Int)),q p)::Trans.Recal.incrFirst (A a (p+1) m) (r:Int)=_
  rw [incrFirst_A]
  congr 1

theorem incrFirst_K7_neg (d a p m r : Nat) (hrd : r≤d) (hra : r≤a) :
    Trans.Recal.incrFirst (K7 d a p m) (-(r:Int))=K7 (d-r) (a-r) p m := by
  unfold K7 Trans.Recal.incrFirst
  rw [List.map_cons]
  change (((d:Int)-(r:Int)),q p)::Trans.Recal.incrFirst (A a (p+1) m) (-(r:Int))=_
  rw [incrFirst_A_neg a (p+1) r m hra]
  congr 1
  apply Prod.ext
  · push_cast
    omega
  · rfl

theorem red_C7_phase1_zero (d a f : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.red (f+1) (C7 d a 1 0)=C7Red 1 0 := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (C7 d a 1 0)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_C7]
    rfl,isPrincipalP_C7 d a 1 0 hd hda]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (C7 d a 1 0) 0==0 &&
    Trans.Recal.gp1 (C7 d a 1 0) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_C7_phase1 d a 0 hd hda,lenI_C7]
  change Trans.Recal.jjSeq 0 1=C7Red 1 0
  rfl

theorem red_C7_phase2_zero (d a f : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.red (f+1) (C7 d a 2 0)=C7Red 2 0 := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (C7 d a 2 0)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_C7]
    rfl,isPrincipalP_C7 d a 2 0 hd hda]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (C7 d a 2 0) 0==0 &&
    Trans.Recal.gp1 (C7 d a 2 0) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_C7_phase2 d a 0 hd hda,lenI_C7]
  change Trans.Recal.jjSeq 0 1=C7Red 2 0
  rfl

theorem red_C7_phase1_step (d a m f : Nat) (hd : 0<d) (hda : d<a)
    (hK : Trans.Recal.red f (K7 2 (a+1) 2 m)=K7Red 2 m) :
    Trans.Recal.red (f+1) (C7 d a 1 (m+1))=C7Red 1 (m+1) := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (C7 d a 1 (m+1))=false from by
    unfold Trans.Recal.isZeroP
    rw [length_C7]
    simp,isPrincipalP_C7 d a 1 (m+1) hd hda]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (C7 d a 1 (m+1)) 0==0 &&
    Trans.Recal.gp1 (C7 d a 1 (m+1)) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_C7_phase1 d a (m+1) hd hda,lenI_C7]
  rw [show ((1:Int)==((m+1:Nat):Int)+2-1)=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true,if_false]
  rw [brF_C7_phase1_succ d a m hd hda,
    firstNodes_C7_phase1_succ d a m hd hda,
    joints_C7_phase1_succ d a m hd hda]
  simp only [List.length_cons,List.length_nil]
  rw [show List.range 1=[0] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([K7 a (a+1) 2 m]:List Trans.Recal.PS).getD 0 []=
      K7 a (a+1) 2 m from rfl,
    show ([2,((m+3:Nat):Int)]:List Int).getD 0 0=2 from rfl,
    show ([1]:List Int).getD 0 0=1 from rfl]
  rw [show Trans.Recal.gp1 (K7 a (a+1) 2 m) 0=1 from by rfl]
  simp only [show ((1:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [fpar1_C7_two_phase1 d a (m+1) hd hda (by omega)]
  change Trans.Recal.jjSeq 0 1++Trans.Recal.incrFirst
    (Trans.Recal.red f ((2,1)::Trans.Recal.derp (K7 a (a+1) 2 m))) 1=_
  rw [show (2,1)::Trans.Recal.derp (K7 a (a+1) 2 m)=K7 2 (a+1) 2 m from rfl,hK]
  unfold K7Red C7Red
  rw [show q 2=1 from rfl]
  rw [show Int.toNat (1:Int)=1 by rfl]
  rw [show Trans.Recal.incrFirst (A 1 2 (m+1)) 1=A 2 2 (m+1) from by
    simpa using incrFirst_A 1 2 1 (m+1)]
  rw [show m+1+1=(m+1)+1 by omega,A_succ 1 1 (m+1)]
  rfl

theorem red_C7_phase2_step (d a m f : Nat) (hd : 0<d) (hda : d<a)
    (hK : Trans.Recal.red f (K7 2 (a+1) 0 m)=K7Red 0 m) :
    Trans.Recal.red (f+1) (C7 d a 2 (m+1))=C7Red 2 (m+1) := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (C7 d a 2 (m+1))=false from by
    unfold Trans.Recal.isZeroP
    rw [length_C7]
    simp,isPrincipalP_C7 d a 2 (m+1) hd hda]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (C7 d a 2 (m+1)) 0==0 &&
    Trans.Recal.gp1 (C7 d a 2 (m+1)) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_C7_phase2 d a (m+1) hd hda,lenI_C7]
  rw [show ((1:Int)==((m+1:Nat):Int)+2-1)=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true,if_false]
  rw [brF_C7_phase2_succ d a m hd hda,
    firstNodes_C7_phase2_succ d a m hd hda,
    joints_C7_phase2_succ d a m hd hda]
  simp only [List.length_cons,List.length_nil]
  rw [show List.range 1=[0] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([K7 a (a+1) 3 m]:List Trans.Recal.PS).getD 0 []=
      K7 a (a+1) 3 m from rfl,
    show ([2,((m+3:Nat):Int)]:List Int).getD 0 0=2 from rfl,
    show ([1]:List Int).getD 0 0=1 from rfl]
  rw [show Trans.Recal.gp1 (K7 a (a+1) 3 m) 0=0 from by rfl]
  simp only [show ((0:Int)==0)=true from rfl,if_true]
  change Trans.Recal.jjSeq 0 1++Trans.Recal.incrFirst
    (Trans.Recal.red f ((2,0)::Trans.Recal.derp (K7 a (a+1) 3 m))) 2=_
  rw [show (2,0)::Trans.Recal.derp (K7 a (a+1) 3 m)=K7 2 (a+1) 3 m from rfl,
    K7_phase_add_three 2 (a+1) 0 m,hK]
  unfold K7Red C7Red
  rw [show q 0=0 from rfl]
  rw [show Int.toNat (0:Int)=0 by rfl]
  rw [show Trans.Recal.incrFirst (A 0 0 (m+1)) 2=A 2 0 (m+1) from by
    simpa using incrFirst_A 0 0 2 (m+1)]
  rw [show m+1+1=(m+1)+1 by omega,A_succ 1 2 (m+1)]
  rw [A_phase_add_three 2 0 (m+1)]
  rfl

theorem red_K7_phase2_from_C (d a m f : Nat) (hda : d<a)
    (hC : Trans.Recal.red f (C7 (d+1) (a+1) 2 m)=C7Red 2 m) :
    Trans.Recal.red (f+1) (K7 d a 2 m)=K7Red 2 m := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (K7 d a 2 m)=false from by
    unfold Trans.Recal.isZeroP
    rw [length_K7]
    cases m <;> rfl,
    isPrincipalP_K7 d a 2 m hda (Or.inl (by decide))]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (K7 d a 2 m) 0==0 &&
    Trans.Recal.gp1 (K7 d a 2 m) 0==0)=false from by
      rw [gp0_K7_zero,gp1_K7_zero]
      simp [q]]
  simp only [Bool.false_eq_true,if_false]
  rw [show (Trans.Recal.gp1 (K7 d a 2 m) 0==0)=false from by rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show Trans.Recal.jjSeq 0 (Trans.Recal.gp1 (K7 d a 2 m) 0-1)++
      Trans.Recal.incrFirst (K7 d a 2 m) (Trans.Recal.gp1 (K7 d a 2 m) 0)=
      C7 (d+1) (a+1) 2 m from by
    rw [gp1_K7_zero]
    change [(0,0)]++Trans.Recal.incrFirst (K7 d a 2 m) 1=_
    rw [show Trans.Recal.incrFirst (K7 d a 2 m) 1=K7 (d+1) (a+1) 2 m from by
      simpa using incrFirst_K7 d a 2 m 1]
    rfl,hC]
  rw [show Trans.Recal.lenI (C7Red 2 m)-1=(m:Int)+1 from by
    unfold C7Red Trans.Recal.lenI
    simp [length_A]
    ]
  rw [gp1_K7_zero]
  rw [show q 2=1 from rfl]
  rw [show decide ((1:Int)≤(m:Int)+1)=true from decide_eq_true (by omega)]
  rw [show Int.toNat (1:Int)=1 by rfl]
  rw [show (C7Red 2 m).drop 1=K7Red 2 m from by rfl]
  rw [show Trans.Recal.isPrincipalP (K7Red 2 m)=true from by
    rw [show K7Red 2 m=K7 1 2 2 m from by
      unfold K7Red K7
      rw [A_succ]
      rfl]
    exact isPrincipalP_K7 1 2 2 m (by omega) (Or.inl (by decide))]
  simp only [Bool.true_and,if_true]
  rw [show -Trans.Recal.gp0 (C7Red 2 m) 1+
      Trans.Recal.gp1 (C7Red 2 m) 1=0 from by
    unfold C7Red
    rw [A_succ]
    rfl]
  simp [Trans.Recal.incrFirst]

theorem red_K7_phase0_zero (d a f : Nat) :
    Trans.Recal.red (f+1) (K7 d a 0 0)=K7Red 0 0 := by
  rw [Trans.Recal.red]
  rfl

theorem red_K7_phase0_step (d a m f : Nat) (hd : 0<d) (hda : d<a)
    (hC : Trans.Recal.red f (C7 (a-d) (a-d+1) 1 m)=C7Red 1 m) :
    Trans.Recal.red (f+1) (K7 d a 0 (m+1))=K7Red 0 (m+1) := by
  rw [Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (K7 d a 0 (m+1))=false from by
    unfold Trans.Recal.isZeroP
    rw [length_K7]
    simp,isPrincipalP_K7 d a 0 (m+1) hda (Or.inr (by omega))]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (K7 d a 0 (m+1)) 0==0 &&
    Trans.Recal.gp1 (K7 d a 0 (m+1)) 0==0)=false from by
      rw [gp0_K7_zero,gp1_K7_zero]
      rw [show (((d:Int)==0))=false from
        beq_eq_false_iff_ne.mpr (by push_cast; omega)]
      rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show (Trans.Recal.gp1 (K7 d a 0 (m+1)) 0==0)=true from by rfl]
  simp only [if_true]
  rw [gp0_K7_zero]
  have hshift : Trans.Recal.incrFirst (K7 d a 0 (m+1)) (-(d:Int))=
      C7 (a-d) (a-d+1) 1 m := by
    rw [incrFirst_K7_neg d a 0 (m+1) d (by omega) (by omega)]
    unfold C7 K7
    rw [A_succ]
    simp [q]
  rw [hshift,hC]
  unfold K7Red C7Red
  rw [show q 0=0 from rfl]
  rw [show Int.toNat (0:Int)=0 by rfl]
  rw [show m+1+1=(m+1)+1 by omega,A_succ 0 0 (m+1)]
  rfl

/-- The four reduction states needed by one complete `0,1,1` period. -/
theorem red_periodic : ∀ m : Nat,
    (∀ d a f : Nat, 0<d → d<a →
      Trans.Recal.red (4*m+f+1) (C7 d a 1 m)=C7Red 1 m) ∧
    (∀ d a f : Nat, 0<d → d<a →
      Trans.Recal.red (4*m+f+1) (C7 d a 2 m)=C7Red 2 m) ∧
    (∀ d a f : Nat, 0<d → d<a →
      Trans.Recal.red (4*m+f+1) (K7 d a 0 m)=K7Red 0 m) ∧
    (∀ d a f : Nat, d<a →
      Trans.Recal.red (4*m+f+2) (K7 d a 2 m)=K7Red 2 m) := by
  intro m
  induction m with
  | zero =>
    refine ⟨?_,?_,?_,?_⟩
    · intro d a f hd hda
      rw [show 4*0+f+1=f+1 by omega]
      exact red_C7_phase1_zero d a f hd hda
    · intro d a f hd hda
      rw [show 4*0+f+1=f+1 by omega]
      exact red_C7_phase2_zero d a f hd hda
    · intro d a f _ _
      rw [show 4*0+f+1=f+1 by omega]
      exact red_K7_phase0_zero d a f
    · intro d a f hda
      rw [show 4*0+f+2=(f+1)+1 by omega]
      exact red_K7_phase2_from_C d a 0 (f+1) hda
        (red_C7_phase2_zero (d+1) (a+1) f (by omega) (by omega))
  | succ m ih =>
    rcases ih with ⟨ihC1,ihC2,ihK0,ihK2⟩
    have hC1 : ∀ d a f : Nat, 0<d → d<a →
        Trans.Recal.red (4*(m+1)+f+1) (C7 d a 1 (m+1))=
          C7Red 1 (m+1) := by
      intro d a f hd hda
      have hK : Trans.Recal.red (4*m+(f+2)+2) (K7 2 (a+1) 2 m)=
          K7Red 2 m := ihK2 2 (a+1) (f+2) (by omega)
      simpa [show 4*(m+1)+f+1=(4*m+(f+2)+2)+1 by omega] using
        red_C7_phase1_step d a m (4*m+(f+2)+2) hd hda hK
    have hC2 : ∀ d a f : Nat, 0<d → d<a →
        Trans.Recal.red (4*(m+1)+f+1) (C7 d a 2 (m+1))=
          C7Red 2 (m+1) := by
      intro d a f hd hda
      have hK : Trans.Recal.red (4*m+(f+3)+1) (K7 2 (a+1) 0 m)=
          K7Red 0 m := ihK0 2 (a+1) (f+3) (by omega) (by omega)
      simpa [show 4*(m+1)+f+1=(4*m+(f+3)+1)+1 by omega] using
        red_C7_phase2_step d a m (4*m+(f+3)+1) hd hda hK
    have hK0 : ∀ d a f : Nat, 0<d → d<a →
        Trans.Recal.red (4*(m+1)+f+1) (K7 d a 0 (m+1))=
          K7Red 0 (m+1) := by
      intro d a f hd hda
      have hC : Trans.Recal.red (4*m+(f+3)+1)
          (C7 (a-d) (a-d+1) 1 m)=C7Red 1 m :=
        ihC1 (a-d) (a-d+1) (f+3) (by omega) (by omega)
      simpa [show 4*(m+1)+f+1=(4*m+(f+3)+1)+1 by omega] using
        red_K7_phase0_step d a m (4*m+(f+3)+1) hd hda hC
    have hK2 : ∀ d a f : Nat, d<a →
        Trans.Recal.red (4*(m+1)+f+2) (K7 d a 2 (m+1))=
          K7Red 2 (m+1) := by
      intro d a f hda
      have hC : Trans.Recal.red (4*(m+1)+f+1)
          (C7 (d+1) (a+1) 2 (m+1))=C7Red 2 (m+1) :=
        hC2 (d+1) (a+1) f (by omega) (by omega)
      simpa [show 4*(m+1)+f+2=(4*(m+1)+f+1)+1 by omega] using
        red_K7_phase2_from_C d a (m+1) (4*(m+1)+f+1) hda hC
    exact ⟨hC1,hC2,hK0,hK2⟩

theorem red_C7_phase1_all (d a m f : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.red (4*m+f+1) (C7 d a 1 m)=C7Red 1 m :=
  (red_periodic m).1 d a f hd hda

theorem red_C7_phase2_all (d a m f : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.red (4*m+f+1) (C7 d a 2 m)=C7Red 2 m :=
  (red_periodic m).2.1 d a f hd hda

theorem red_K7_phase0_all (d a m f : Nat) (hd : 0<d) (hda : d<a) :
    Trans.Recal.red (4*m+f+1) (K7 d a 0 m)=K7Red 0 m :=
  (red_periodic m).2.2.1 d a f hd hda

theorem red_K7_phase2_all (d a m f : Nat) (hda : d<a) :
    Trans.Recal.red (4*m+f+2) (K7 d a 2 m)=K7Red 2 m :=
  (red_periodic m).2.2.2 d a f hda

theorem S_eq_C7 (m : Nat) : S m=C7 3 4 2 m := by
  unfold S E C7 K7
  rfl

theorem C7Red_two_eq (m : Nat) : C7Red 2 m=(0,0)::E 1 3 m := by
  unfold C7Red E
  rw [A_succ]
  rfl

theorem red_S_all (m f : Nat) :
    Trans.Recal.red (4*m+f+1) (S m)=C7Red 2 m := by
  rw [S_eq_C7]
  exact red_C7_phase2_all 3 4 m f (by omega) (by omega)

theorem red_R_all (m f : Nat) :
    Trans.Recal.red (4*m+f+2) (R m)=E 1 3 m := by
  rw [show 4*m+f+2=(4*m+f+1)+1 by omega,Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (R m)=false from by
      show Trans.Recal.isZeroP (E 2 3 m)=false
      unfold Trans.Recal.isZeroP
      rw [length_E]
      cases m <;> rfl,
    show Trans.Recal.isPrincipalP (R m)=true from isPrincipalP_E 2 3 m]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (R m) 0==0 &&
      Trans.Recal.gp1 (R m) 0==0)=false from by rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [show (Trans.Recal.gp1 (R m) 0==0)=false from by rfl]
  simp only [Bool.false_eq_true,if_false]
  rw [R_to_S,red_S_all,C7Red_two_eq]
  rw [show Trans.Recal.lenI ((0,0)::E 1 3 m)-1=(m:Int)+1 from by
    unfold Trans.Recal.lenI
    rw [List.length_cons,length_E]
    omega]
  rw [show Trans.Recal.gp1 (R m) 0=1 from rfl]
  rw [show decide ((1:Int)≤(m:Int)+1)=true from decide_eq_true (by omega)]
  rw [show ((0,0)::E 1 3 m).drop (1:Int).toNat=E 1 3 m from by rfl,
    isPrincipalP_E]
  simp only [Bool.true_and,if_true]
  rw [show Trans.Recal.gp0 ((0,0)::E 1 3 m) 1=1 from rfl,
    show Trans.Recal.gp1 ((0,0)::E 1 3 m) 1=1 from rfl]
  simp [Trans.Recal.incrFirst]

theorem red_L_all (m f : Nat) :
    Trans.Recal.red (4*m+f+3) (L m)=L m := by
  rw [show 4*m+f+3=(4*m+f+2)+1 by omega,Trans.Recal.red]
  rw [show Trans.Recal.isZeroP (L m)=false from by
      unfold Trans.Recal.isZeroP
      rw [length_L]
      simp,isPrincipalP_L]
  simp only [Bool.false_eq_true,if_false,if_true]
  rw [show (Trans.Recal.gp0 (L m) 0==0 &&
      Trans.Recal.gp1 (L m) 0==0)=true from by rfl]
  simp only [if_true]
  rw [trMax_L,lenI_L]
  rw [show ((1:Int)==(m:Int)+3-1)=false from
    beq_eq_false_iff_ne.mpr (by omega)]
  simp only [Bool.false_eq_true,if_false]
  rw [brF_L,firstNodes_L,joints_L]
  simp only [List.length_cons,List.length_nil]
  rw [show List.range 1=[0] by rfl]
  simp only [List.foldl_cons,List.foldl_nil]
  rw [show ([R m]:List Trans.Recal.PS).getD 0 []=R m from rfl,
    show ([2,((m+3:Nat):Int)]:List Int).getD 0 0=2 from rfl,
    show ([1]:List Int).getD 0 0=1 from rfl]
  rw [show Trans.Recal.gp1 (R m) 0=1 from rfl]
  simp only [show ((1:Int)==0)=false from rfl,Bool.false_eq_true,if_false]
  rw [fpar1_L_two]
  change Trans.Recal.jjSeq 0 1++Trans.Recal.incrFirst
    (Trans.Recal.red (4*m+f+2)
      (((2:Int),(1:Int))::Trans.Recal.derp (R m))) 1=L m
  rw [show (((2:Int),(1:Int))::Trans.Recal.derp (R m))=R m from by
    unfold R Trans.Recal.derp
    rfl,red_R_all]
  rw [show Trans.Recal.incrFirst (E 1 3 m) 1=R m from by
    simpa using incrFirst_E 1 3 1 m]
  rfl

theorem redP_L (m : Nat) : Trans.Recal.redP (L m)=L m := by
  unfold Trans.Recal.redP
  have hb : 4*m+3≤Trans.Recal.redFuel (L m) := by
    unfold Trans.Recal.redFuel
    rw [length_L]
    omega
  rw [show Trans.Recal.redFuel (L m)=
    4*m+(Trans.Recal.redFuel (L m)-4*m-3)+3 by omega]
  exact red_L_all m _

theorem isReducedP_L (m : Nat) : Trans.Recal.isReducedP (L m)=true := by
  unfold Trans.Recal.isReducedP
  rw [redP_L]
  exact G1.beq_PS_self _

/-! ### Memo-table invariant for the periodic ladder reader. -/

abbrev Base : Trans.Recal.PS := [((0:Int),(0:Int))]
abbrev B0 : Trans.Recal.PS := [((0:Int),(0:Int)),((1:Int),(1:Int))]

def Val (k : Nat) : Option Int → Trans.Dict.BT
  | none => LBT k
  | _ => High k

def Good (p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT) : Prop :=
  (∀ k, p.1=(L k,none) → p.2=LBT k) ∧
  (∀ k, p.1=(L k,some ((k+2:Nat):Int)) → p.2=High k) ∧
  (p.1=(B0,none) → p.2=.D 0 (.D 1 .zero)) ∧
  (p.1=(B0,some 1) → p.2=.D 1 .zero) ∧
  (p.1=(Base,none) → p.2=Trans.Dict.BT.zero)

def Sound (tbl : Trans.Recal.Memo) : Prop := ∀ p∈tbl, Good p

theorem Sound_nil : Sound [] := by intro p hp; simp at hp

theorem L_inj (a b : Nat) (h : L a=L b) : a=b := by
  have hl:=congrArg List.length h
  rw [length_L,length_L] at hl
  omega

theorem L_ne_B0 (k : Nat) : L k≠B0 := by
  intro h
  have hl:=congrArg List.length h
  rw [length_L] at hl
  simp at hl

theorem L_ne_Base (k : Nat) : L k≠Base := by
  intro h
  have hl:=congrArg List.length h
  rw [length_L] at hl
  simp at hl

theorem B0_ne_Base : B0≠Base := by
  intro h
  have hl:=congrArg List.length h
  simp at hl

theorem adm_L_zero : Trans.Recal.adm (L 0) 1=1 := by rfl

theorem Sound_cons_L (tbl : Trans.Recal.Memo) (hs : Sound tbl) (k : Nat)
    (req : Option Int) (hr : req=none ∨ req=some ((k+2:Nat):Int)) :
    Sound (((L k,req),Val k req)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro j hj
      have hL:L k=L j:=congrArg Prod.fst hj
      have hreq:req=none:=congrArg Prod.snd hj
      have hkj:=L_inj k j hL
      subst hkj
      rw [hreq]
      rfl
    · intro j hj
      have hL:L k=L j:=congrArg Prod.fst hj
      have hreq:req=some ((j+2:Nat):Int):=congrArg Prod.snd hj
      have hkj:=L_inj k j hL
      subst hkj
      rw [hreq]
      rfl
    · intro hj
      exact absurd (congrArg Prod.fst hj) (L_ne_B0 k)
    · intro hj
      exact absurd (congrArg Prod.fst hj) (L_ne_B0 k)
    · intro hj
      exact absurd (congrArg Prod.fst hj) (L_ne_Base k)
  · exact hs p h

theorem Sound_cons_B (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (req : Option Int) (hr : req=none ∨ req=some 1) :
    Sound (((B0,req),if req=none then .D 0 (.D 1 .zero) else .D 1 .zero)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro k hk
      exact absurd (congrArg Prod.fst hk).symm (L_ne_B0 k)
    · intro k hk
      exact absurd (congrArg Prod.fst hk).symm (L_ne_B0 k)
    · intro hk
      have hreq:req=none:=congrArg Prod.snd hk
      rw [hreq]
      rfl
    · intro hk
      have hreq:req=some 1:=congrArg Prod.snd hk
      rw [hreq]
      rfl
    · intro hk
      exact absurd (congrArg Prod.fst hk) B0_ne_Base
  · exact hs p h

theorem Sound_cons_base (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    Sound (((Base,none),Trans.Dict.BT.zero)::tbl) := by
  intro p hp
  rcases List.mem_cons.mp hp with h|h
  · subst h
    refine ⟨?_,?_,?_,?_,fun _=>rfl⟩
    · intro k hk
      exact absurd (congrArg Prod.fst hk).symm (L_ne_Base k)
    · intro k hk
      exact absurd (congrArg Prod.fst hk).symm (L_ne_Base k)
    · intro hk
      exact absurd (congrArg Prod.fst hk).symm B0_ne_Base
    · intro hk
      exact absurd (congrArg Prod.fst hk).symm B0_ne_Base
  · exact hs p h

theorem good_of_find {tbl : Trans.Recal.Memo} (hs : Sound tbl)
    {key : Trans.Recal.PS × Option Int}
    {p : (Trans.Recal.PS × Option Int) × Trans.Dict.BT}
    (h : tbl.find? (fun q=>q.1==key)=some p) : Good p ∧ p.1=key := by
  refine ⟨hs p (List.mem_of_find?_eq_some h),?_⟩
  have hb:p.1==key:=List.find?_some (p:=fun q=>q.1==key) (a:=p) h
  exact eq_of_beq hb

theorem run_base_ok (f : Nat) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (f+1) Base none).run tbl).1=Trans.Dict.BT.zero ∧
      Sound ((Trans.Recal.runAux (f+1) Base none).run tbl).2 := by
  cases hf:tbl.find? (fun q=>q.1==(Base,(none:Option Int))) with
  | some p =>
    rw [G1.run_hit f Base none tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    exact ⟨hg.2.2.2.2 he,hs⟩
  | none =>
    rw [G1.run_base f tbl hf]
    exact ⟨rfl,Sound_cons_base tbl hs⟩

theorem runAux_B0 (g : Nat) (req : Option Int) (hr : req=none ∨ req=some 1)
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+2) B0 req).run tbl).1=
        (if req=none then .D 0 (.D 1 .zero) else .D 1 .zero) ∧
      Sound ((Trans.Recal.runAux (g+2) B0 req).run tbl).2 := by
  cases hf:tbl.find? (fun q=>q.1==(B0,req)) with
  | some p =>
    rw [G1.run_hit (g+1) B0 req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    refine ⟨?_,hs⟩
    rcases hr with h|h
    · subst h
      simpa using hg.2.2.1 he
    · subst h
      simpa using hg.2.2.2.1 he
  | none =>
    rw [Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,
      show Trans.Recal.isReducedP B0=true from G1.isReducedP_LG 0,
      show Trans.Recal.isPrincipalP B0=true from G1.isPrincipalP_LG 0,
      Bool.not_true,Bool.false_eq_true,if_false,
      show Trans.Recal.lenI B0=2 from G1.lenI_LG 0,
      show (((2:Int)-1)==0)=false from rfl,
      show Trans.Recal.predP B0=Base from rfl]
    cases hrun:(Trans.Recal.runAux (g+1) Base none) tbl with
    | mk a s =>
      have ih:=run_base_ok g tbl hs
      rw [show (Trans.Recal.runAux (g+1) Base none).run tbl=(a,s) from hrun] at ih
      have ha:a=Trans.Dict.BT.zero:=ih.1
      have hsm:Sound s:=ih.2
      subst ha
      simp only [show ((Trans.Dict.BT.zero:Trans.Dict.BT)==.zero)=true from rfl,if_true]
      rcases hr with h|h
      · subst h
        exact ⟨rfl,Sound_cons_B s hsm none (Or.inl rfl)⟩
      · subst h
        exact ⟨rfl,Sound_cons_B s hsm (some 1) (Or.inr rfl)⟩

theorem runAux_L0 (g : Nat) (req : Option Int)
    (hr : req=none ∨ req=some 2) (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (g+3) (L 0) req).run tbl).1=Val 0 req ∧
      Sound ((Trans.Recal.runAux (g+3) (L 0) req).run tbl).2 := by
  cases hf:tbl.find? (fun q=>q.1==(L 0,req)) with
  | some p =>
    rw [G1.run_hit (g+2) (L 0) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    refine ⟨?_,hs⟩
    rcases hr with h|h
    · subst h
      exact hg.1 0 he
    · subst h
      exact hg.2.1 0 he
  | none =>
    rw [Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L 0,isPrincipalP_L 0,
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L 0,
      show (((((0:Nat):Int)+3-1)==0))=false from rfl,
      show Trans.Recal.predP (L 0)=B0 from rfl]
    cases hrun:(Trans.Recal.runAux (g+2) B0 none) tbl with
    | mk a s =>
      have ih1:=runAux_B0 g none (Or.inl rfl) tbl hs
      rw [show (Trans.Recal.runAux (g+2) B0 none).run tbl=(a,s) from hrun] at ih1
      have ha:a=.D 0 (.D 1 .zero):=ih1.1
      have hsm:Sound s:=ih1.2
      subst ha
      simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
        modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
        MonadStateOf.get,Id.run,
        show ((Trans.Dict.BT.D 0 (.D 1 .zero))==.zero)=false from rfl,
        Bool.false_eq_true,if_false,
        show Trans.Recal.fpar (L 0) 0 (((0:Nat):Int)+3-1) 0=1 from by
          simpa using fpar_L 0 2 (by omega) (by omega),
        adm_L_zero]
      cases hrun2:(Trans.Recal.runAux (g+2) B0 (some 1)) s with
      | mk c1 s2 =>
        have ih2:=runAux_B0 g (some 1) (Or.inr rfl) s hsm
        rw [show (Trans.Recal.runAux (g+2) B0 (some 1)).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=.D 1 .zero:=ih2.1
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,
          show Trans.Recal.transTypeMain (L 0) 1 (((0:Nat):Int)+3-1)=3 from rfl,
          show Trans.Recal.mkC2 (L 0) 1 (((0:Nat):Int)+3-1) 3
              (Trans.Dict.BT.D 1 .zero)=Trans.Dict.BT.D 1 (.D 1 .zero) from rfl]
        rcases hr with h|h
        · subst h
          rw [show Trans.Recal.replMark
              ((Trans.Dict.BT.D 0 (.D 1 .zero)).size+
                ((Trans.Dict.BT.D 1 .zero).size+
                  (Trans.Dict.BT.D 1 (.D 1 .zero)).size+4))
              (Trans.Dict.BT.D 0 (.D 1 .zero)) (Trans.Dict.BT.D 1 .zero)
                (Trans.Dict.BT.D 1 (.D 1 .zero))=some (LBT 0) from rfl]
          exact ⟨rfl,Sound_cons_L s2 hsm2 0 none (Or.inl rfl)⟩
        · subst h
          simp only [show ¬((2:Int)<(((0:Nat):Int)+3-1)) by omega,if_false]
          exact ⟨rfl,Sound_cons_L s2 hsm2 0 (some 2) (Or.inr rfl)⟩

set_option maxHeartbeats 1000000 in
theorem runAux_step (k g : Nat) (req : Option Int)
    (hr : req=none ∨ req=some (((k+1)+2:Nat):Int))
    (tbl : Trans.Recal.Memo) (hs : Sound tbl)
    (ih : ∀ (r : Option Int), r=none ∨ r=some ((k+2:Nat):Int) →
      ∀ (s : Trans.Recal.Memo), Sound s →
        ((Trans.Recal.runAux (k+g+3) (L k) r).run s).1=Val k r ∧
          Sound ((Trans.Recal.runAux (k+g+3) (L k) r).run s).2) :
    ((Trans.Recal.runAux ((k+1)+g+3) (L (k+1)) req).run tbl).1=
        Val (k+1) req ∧
      Sound ((Trans.Recal.runAux ((k+1)+g+3) (L (k+1)) req).run tbl).2 := by
  cases hf:tbl.find? (fun q=>q.1==(L (k+1),req)) with
  | some p =>
    rw [show k+1+g+3=(k+g+3)+1 by omega,
      G1.run_hit (k+g+3) (L (k+1)) req tbl p hf]
    obtain ⟨hg,he⟩:=good_of_find hs hf
    refine ⟨?_,hs⟩
    rcases hr with h|h
    · subst h
      exact hg.1 (k+1) he
    · subst h
      exact hg.2.1 (k+1) he
  | none =>
    rw [show k+1+g+3=(k+g+3)+1 by omega,Trans.Recal.runAux]
    simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
      modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
      MonadStateOf.get,Id.run,hf,isReducedP_L (k+1),isPrincipalP_L (k+1),
      Bool.not_true,Bool.false_eq_true,if_false,lenI_L (k+1),
      show (((((k+1:Nat):Int)+3-1)==0))=false from by simp; omega,
      predP_L k]
    cases hrun:(Trans.Recal.runAux (k+g+3) (L k) none) tbl with
    | mk a s =>
      have ih1:=ih none (Or.inl rfl) tbl hs
      rw [show (Trans.Recal.runAux (k+g+3) (L k) none).run tbl=(a,s) from hrun] at ih1
      have ha:a=LBT k:=ih1.1
      have hsm:Sound s:=ih1.2
      subst ha
      simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
        modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
        MonadStateOf.get,Id.run,
        show ((LBT k)==Trans.Dict.BT.zero)=false from rfl,
        Bool.false_eq_true,if_false,
        show Trans.Recal.fpar (L (k+1)) 0 (((k+1:Nat):Int)+3-1) 0=
            ((k+2:Nat):Int) from by
          rw [show (((k+1:Nat):Int)+3-1)=((k+3:Nat):Int) by push_cast; omega]
          have h:=fpar_L (k+1) (k+3) (by omega) (by omega)
          simpa using h,
        show Trans.Recal.adm (L (k+1)) ((k+2:Nat):Int)=
            ((k+2:Nat):Int) from by simpa using adm_L_parent k]
      cases hrun2:(Trans.Recal.runAux (k+g+3) (L k)
          (some ((k+2:Nat):Int))) s with
      | mk c1 s2 =>
        have ih2:=ih (some ((k+2:Nat):Int)) (Or.inr rfl) s hsm
        rw [show (Trans.Recal.runAux (k+g+3) (L k)
            (some ((k+2:Nat):Int))).run s=(c1,s2) from hrun2] at ih2
        have hc1:c1=High k:=ih2.1
        have hsm2:Sound s2:=ih2.2
        subst hc1
        simp only [StateT.run,bind,StateT.bind,StateT.get,StateT.pure,pure,
          modify,modifyGet,MonadStateOf.modifyGet,StateT.modifyGet,get,getThe,
          MonadStateOf.get,Id.run,
          show Trans.Recal.mkC2 (L (k+1)) ((k+2:Nat):Int)
              (((k+1:Nat):Int)+3-1)
              (Trans.Recal.transTypeMain (L (k+1)) ((k+2:Nat):Int)
                (((k+1:Nat):Int)+3-1)) (High k)=StepC2 k from by
            rw [show (((k+1:Nat):Int)+3-1)=((k+3:Nat):Int) by push_cast; omega]
            exact mkC2_L k]
        rcases hr with h|h
        · subst h
          rw [repl_LBT ((LBT k).size+((High k).size+(StepC2 k).size+4)) k (by
            show k+4≤(LBT k).size+((High k).size+(StepC2 k).size+4)
            rw [size_LBT]
            omega)]
          simp only [Option.getD_some]
          exact ⟨rfl,Sound_cons_L s2 hsm2 (k+1) none (Or.inl rfl)⟩
        · subst h
          simp only [show ¬((((k+1)+2:Nat):Int)<(((k+1:Nat):Int)+3-1)) by
              push_cast; omega,
            if_false,
            show Trans.Recal.gp1 (L (k+1)) (((k+1:Nat):Int)+3-1)=q k from by
              rw [show (((k+1:Nat):Int)+3-1)=((k+3:Nat):Int) by push_cast; omega]
              exact gp1_L_top k]
          exact ⟨rfl,Sound_cons_L s2 hsm2 (k+1)
            (some (((k+1)+2:Nat):Int)) (Or.inr rfl)⟩

set_option maxHeartbeats 2000000 in
theorem runAux_L (k g : Nat) (req : Option Int)
    (hr : req=none ∨ req=some ((k+2:Nat):Int))
    (tbl : Trans.Recal.Memo) (hs : Sound tbl) :
    ((Trans.Recal.runAux (k+g+3) (L k) req).run tbl).1=Val k req ∧
      Sound ((Trans.Recal.runAux (k+g+3) (L k) req).run tbl).2 := by
  induction k generalizing g req tbl with
  | zero => exact runAux_L0 g req (by simpa using hr) tbl hs
  | succ k ih =>
    apply runAux_step k g req hr tbl hs
    intro r h s ht
    exact ih g r h s ht

theorem transPort_L (m : Nat) : Trans.Recal.transPort (L m)=LBT m := by
  have hb:m+3≤Trans.Recal.transFuel (L m) := by
    show m+3≤40+6*((L m).length+Trans.Recal.maxE (L m))
    rw [length_L]
    omega
  have h:Trans.Recal.transFuel (L m)=
      m+(Trans.Recal.transFuel (L m)-m-3)+3 := by omega
  show ((Trans.Recal.runAux (Trans.Recal.transFuel (L m)) (L m) none).run []).1=_
  rw [h]
  exact (runAux_L m _ none (Or.inl rfl) [] Sound_nil).1

theorem P_phase_add_three : ∀ a m : Nat, P (a+3) m=P a m
  | _,0 => rfl
  | a,m+1 => by
    rw [P,P,q_add_three]
    exact congrArg (Trans.Dict.BT.D (q a).toNat)
      (by simpa only [show a+3+1=(a+1)+3 by omega] using
        P_phase_add_three (a+1) m)

theorem LBT_period (n : Nat) :
    LBT (3*(n+1))=Trans.Dict.BT.D 0
      (.D 1 (.D 1 (LBT (3*n)))) := by
  unfold LBT
  rw [show 3*(n+1)=3*n+3 by omega]
  change Trans.Dict.BT.D 0 (.D 1 (.D 1 (P 3 (3*n+3))))=
    Trans.Dict.BT.D 0 (.D 1 (.D 1 (.D 0 (.D 1 (.D 1 (P 3 (3*n)))))))
  rw [show 3*n+3=(3*n+2)+1 by omega,P]
  rw [show 3*n+2=(3*n+1)+1 by omega,P]
  rw [show 3*n+1=3*n+1 by rfl,P]
  simp [q]
  rw [show P 6 (3*n)=P 3 (3*n) from P_phase_add_three 3 (3*n)]

/-- Link 3a: every complete `0,1,1` block advances the raw Gamma ladder once. -/
theorem dict_LBT_G (n : Nat) :
    Trans.Dict.dict (LBT (3*n))=G7Dict.G n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [LBT_period]
    exact G7Dict.dict_D011_G (LBT (3*n)) n ih

/-- Link 3b: the raw Gamma ladder is the selected row's closed form. -/
theorem dict_LBT (n : Nat) :
    Trans.Dict.dict (LBT (3*n))=fB n := by
  rw [dict_LBT_G,G7Dict.fB_eq_G]

theorem fB_succ (n : Nat) : fB (n+1)=phiNF (fB n) zero := rfl

theorem fB_shape : ∀ n : Nat, ∃ a : Term, a≠zero ∧ fB n=phi a zero
  | 0 => ⟨ofNat 2,by decide,rfl⟩
  | n+1 => by
    obtain ⟨a,ha,hf⟩:=fB_shape n
    refine ⟨phi a zero,?_,?_⟩
    · intro h
      cases h
    · rw [fB_succ,hf,Rows.ProofsB.phiNF_zero_arg (by rfl)]

theorem le_phi_zero_one (a : Term) (ha : a≠zero) :
    le (phi a zero) TM.Term.one=false := by
  have hne : ((phi a zero:Term)==TM.Term.one)=false := by
    apply beq_eq_false_iff_ne.mpr
    intro h
    injection h with h0 _
    exact ha h0
  unfold le
  rw [hne]
  simp only [Bool.false_or]
  rw [show TM.Term.one=phi zero zero from rfl,
    Evidence.WF.lt_phi_phi (beq_eq_false_iff_ne.mp hne),if_neg ha,
    show lt a zero=false from Rows.ProofsB.ltF_lt_zero _ _]
  simp only [Bool.false_eq_true,if_false]
  unfold le
  rw [show ((phi a zero:Term)==zero)=false from rfl]
  simp only [Bool.false_or]
  exact Rows.ProofsB.ltF_lt_zero _ _

theorem one_plus_fB (n : Nat) : plus TM.Term.one (fB n)=fB n := by
  obtain ⟨a,ha,hf⟩:=fB_shape n
  rw [hf]
  unfold plus
  rw [show (phi a zero).toList=[phi a zero] from rfl,
    show TM.Term.one.toList=[TM.Term.one] from rfl]
  simp only [List.filter_cons,List.filter_nil]
  rw [le_phi_zero_one a ha]
  rfl

/-- The selected Gamma-zero row agrees with its closed expansion sequence. -/
theorem oR_M (n : Nat) : Trans.oR (BMS.expand M n)=some (fB n) := by
  show (if (BMS.expand M n).isEmpty then some TM.Term.zero
        else ((Trans.Recal.ofMatrix (BMS.expand M n)).map
          Trans.Recal.transPort).map
            (fun u=>plus TM.Term.one (Trans.Dict.dict u)))=some (fB n)
  rw [show (BMS.expand M n).isEmpty=false from by
    rw [expand_M]
    rfl]
  simp only [Bool.false_eq_true,if_false,ofMatrix_M,Option.map_some]
  rw [transPort_L,dict_LBT,one_plus_fB]

#guard (List.range 8).all fun n =>
  Trans.oR (BMS.expand M n)==some (fB n)
#print axioms oR_M


end G7
end Rows.Selected
